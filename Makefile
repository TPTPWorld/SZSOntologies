# Targets for the SZS_Ontologies repository.  Needs isabelle on PATH; pdf
# also needs pdflatex with ulem and txfonts.

ISABELLE ?= isabelle
OUT := $(CURDIR)/output

.PHONY: build pdf problems atp clean

build:
	$(ISABELLE) build -D .

pdf: build
	$(ISABELLE) document -d . -P $(OUT) SZS_Ontologies
	@echo "$(OUT)/document.pdf"

# Problems/ is committed; CI fails if it differs from this export.
problems: build
	rm -rf Problems
	$(ISABELLE) export -d . -n -p 1 -O Problems -x 'SZS_Ontologies.SZS_Export:T*/*' SZS_Ontologies

# E and Vampire on TF0, Zipperposition and Vampire on TH0, all bundled
# with Isabelle.  Every verdict must equal the file's "% Status" line.
atp: E := $(shell $(ISABELLE) getenv -b E_HOME)/eprover
atp: V := $(shell $(ISABELLE) getenv -b VAMPIRE_HOME)/vampire
atp: Z := $(shell $(ISABELLE) getenv -b ZIPPERPOSITION_HOME)/zipperposition
atp:
	@fail=0; \
	szs() { grep -m1 -o 'SZS status [A-Za-z]*' | sed 's/SZS status //'; }; \
	for f in Problems/TF0/*.p; do \
	  want=$$(grep -m1 '^% Status' $$f | sed 's/.*: *//'); \
	  e=$$($(E) --auto --silent --cpu-limit=60 $$f 2>&1 | szs); \
	  v=$$($(V) --mode casc -t 60 $$f 2>&1 | szs); \
	  echo "$$f E=$$e Vampire=$$v"; \
	  [ "$$e" = "$$want" ] && [ "$$v" = "$$want" ] || fail=1; \
	done; \
	for f in Problems/TH0/*.p; do \
	  want=$$(grep -m1 '^% Status' $$f | sed 's/.*: *//'); \
	  z=$$($(Z) -o none --timeout 60 $$f 2>&1 | szs); \
	  v=$$($(V) --mode casc -t 60 $$f 2>&1 | szs); \
	  echo "$$f Zipperposition=$$z Vampire=$$v"; \
	  [ "$$z" = "$$want" ] && [ "$$v" = "$$want" ] || fail=1; \
	done; \
	exit $$fail

clean:
	rm -rf output export
