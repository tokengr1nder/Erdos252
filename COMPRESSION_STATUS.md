# Compression paused

Paused on 2026-09-13. No new compression pass was started after the stop request.

## Current state

- Proof baseline: `dc5e877ef910e3e83bbdb26afb938acd138b67d8` on `main`.
- `Erdos252/Solution.lean`: **812 substantive lines**, **1,090 total lines**.
  Substantive excludes blank and comment-only lines. Including the root import,
  the proof requires **813 substantive lines**, **1,091 total lines**.
- No Lean proof lines exceed 100 columns.
- The main theorem statement is unchanged; its axiom list is exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- The full build, fresh trust-zero build, statement and axiom audits, and fresh
  kernel replay passed again at this stopping point. No Lean or PDF files changed.
- The last completed simplification bounds each scaled finite remainder directly,
  takes a finite sum of termwise limits, and cancels the expanded vertex sum
  directly, removing the intermediate `gridCore` and `finiteMain` layer.
- The complete proof PDF and corrected LaTeX presentation are published.
  GitHub's contents API returned `PROOF.pdf` at the baseline commit above:
  150,823 bytes, byte-identical to the local file, with SHA-256
  `a928efb8015a79a3bca697ad56bc37fb4319f85dade97c01f6ac34a4a5bc17e9`.

## Proposed next step (not attempted)

Try replacing the separate `scaledTail_tsum` and `summable_blockTerm` proofs
with one `HasSum` proof, deriving the current conclusions from `.tsum_eq` and
`.summable`. They currently repeat the same scaled-tail summand conversion.
This is only a candidate: keep it only if the complete dependency-adjusted proof
is genuinely shorter, without buying lines through reflow or wider columns.

Do not resume until requested. Preserve the exact main theorem statement and
the three-axiom list. Before any later publication, pass the full build, fresh
trust-zero build, statement audit, axiom audit, and fresh kernel replay; update
the complete PDF and presentation to match any proof changes. Report substantive
and total counts separately and keep the 100-column limit.
