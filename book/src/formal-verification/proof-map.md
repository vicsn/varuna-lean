# Proof Map

One connected picture of the Varuna verifier-soundness argument — what is in
Lean, what is still a hypothesis, and what is left outside the kernel.

Open the interactive map:

**[proof-map.html](proof-map.html)**

The spine runs down the left: accepting proof → Fiat–Shamir challenges →
polynomial-commitment openings → AHP checks → R1CS. Iteration 0 colours
the R1CS relation. Iteration 1 colours evaluation-domain vanishing
and Schwartz–Zippel. Iteration 2 colours the holographic indexer.
Iteration 3 colours rowcheck, lineval, and the matrix sumcheck.
Iteration 4 colours Sonic-KZG openings and binding breaks.
Iteration 5 colours the V2 Fiat–Shamir schedule.
Iteration 6 colours batching and the extra round.
Iteration 7 colours the typed accept predicate, toy fixtures, and
source-pinned snarkVM samples (`SpotCheck.lean`).
Iteration 8 colours the knowledge-soundness capstone.

Statuses, edge verbs, and the iteration plan are in [PLAN.md](../../../PLAN.md).
How each item of the security-analysis plan is (or is not) covered is in
[security-analysis.md](security-analysis.md).
This wrapper is intentionally thin: we are not cloning the Ironwood book.
