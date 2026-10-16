# Read by `atp_mcp` through `--config .claude/atp_mcp.exs` in `.mcp.json`; the
# cwd is the repository root when the MCP host launches it.  Points the
# Isabelle backend at this repository's own session so that `prove_isabelle`
# can import SZS_Ontologies.* theories.
import Config

config :atp_client, :isabelle,
  session: "SZS_Ontologies",
  dirs: [Path.expand(".")],
  session_start_timeout_ms: 600_000
