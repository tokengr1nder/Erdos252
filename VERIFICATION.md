# Verification

Checked on 10 October 2026 with Lean 4.35.0-rc2 and mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

Full build, trust-zero rebuild, statement and axiom audits, and fresh replay
using Lean's kernel passed. The main statement is unchanged.
Its axiom list is exactly `propext`, `Classical.choice`, and `Quot.sound`.

See [README.md](README.md) for reproduction commands.
