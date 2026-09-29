# Isabelle toolchain for the SZS session, for podman or docker.
#
#   podman build -t szs-isabelle -f Containerfile .
#   podman run --rm --userns=keep-id --user "$(id -u):$(id -g)" -v "$PWD:/work:ro,Z" szs-isabelle build -v -D /work/IsabelleFormalisation
#
# The image has Isabelle and a prebuilt HOL heap; the SZS heap and logs go
# to a scratch directory inside the container.  Nothing is written to the
# mounted repository, which is why it can be mounted read-only.
# --userns=keep-id together with --user runs Isabelle under your own uid, so
# that it can read the mounted files under rootless podman (the image's own
# user would otherwise win over keep-id).  Any other
# Isabelle tool works the same way, e.g.
#
#   podman run --rm --userns=keep-id --user "$(id -u):$(id -g)" -v "$PWD:/work:ro,Z" szs-isabelle build_log -H Error -d /work/IsabelleFormalisation SZS
#
# Follows Isabelle's own docker_build recipe (src/Pure/Tools/docker_build.scala).

FROM docker.io/library/ubuntu:24.04
ARG ISABELLE_VERSION=Isabelle2025-2
SHELL ["/bin/bash", "-o", "pipefail", "-c"]

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get -y update && \
    apt-get install -y curl less libfontconfig1 libgomp1 openssh-client perl pwgen rlwrap && \
    apt-get clean

RUN useradd -m isabelle
USER isabelle
WORKDIR /home/isabelle

# Install Isabelle and build HOL into the installation's own heap directory
# (system_heaps), so that it is found whatever user id runs the container.
#
# An Isabelle.tar.gz in the build context is used if present, so that the
# 1 GB download is not repeated and the build works when the TUM download
# host is unreachable.  With a nix install:
#   cp "$(nix build --no-link --print-out-paths nixpkgs#isabelle.src)" Isabelle.tar.gz
# Otherwise the tarball is fetched from ISABELLE_URL (override with
# --build-arg).  The glob keeps COPY from failing when the file is absent.
ARG ISABELLE_URL=https://isabelle.in.tum.de/dist/${ISABELLE_VERSION}_linux.tar.gz
COPY --chown=isabelle Containerfile Isabelle.tar.gz* /tmp/context/
RUN if [ -f /tmp/context/Isabelle.tar.gz ]; then \
      echo "Using Isabelle.tar.gz from the build context" && \
      mv /tmp/context/Isabelle.tar.gz Isabelle.tar.gz; \
    else \
      echo "Downloading ${ISABELLE_URL}" && \
      curl --ipv4 --fail --show-error --location --retry 3 \
        --output Isabelle.tar.gz "${ISABELLE_URL}"; \
    fi && \
    rm -rf /tmp/context && \
    tar xzf Isabelle.tar.gz && \
    rm Isabelle.tar.gz && \
    mv "${ISABELLE_VERSION}" Isabelle && \
    Isabelle/bin/isabelle build -o system_heaps -b HOL

# Rootless podman may run the container under an arbitrary uid.  The home
# directory must be traversable by it (useradd creates it 750), and the user
# settings directory (SZS heap, logs, build databases) must be created by
# that uid itself: Isabelle chmods its SQLite databases, which fails on files
# another uid created.  So the image ships no ~/.isabelle and no
# /tmp/isabelle-* (both left behind by the HOL build), and USER_HOME points
# at a directory that does not exist until first use.
RUN chmod 755 /home/isabelle && \
    rm -rf /home/isabelle/.isabelle /tmp/isabelle-*
ENV USER_HOME=/tmp/isabelle-user

ENTRYPOINT ["/home/isabelle/Isabelle/bin/isabelle"]
