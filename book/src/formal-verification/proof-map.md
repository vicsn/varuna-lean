# Proof Map

One connected picture of the Varuna verifier-soundness argument — what is in
Lean, what is still a hypothesis, and what is left outside the kernel.

Open the interactive map:

**[proof-map.html](proof-map.html)**

The spine runs down the left: accepting proof → Fiat–Shamir challenges →
polynomial-commitment openings → AHP checks → R1CS. Proved nodes cover the
R1CS relation, evaluation-domain vanishing and Schwartz–Zippel, the
holographic indexer, rowcheck, lineval, and the matrix sumcheck, Sonic-KZG
openings and binding breaks, the V2 Fiat–Shamir schedule, batching and the
extra round, the typed accept predicate, toy fixtures, source-pinned snarkVM
samples (`SpotCheck.lean`), and the knowledge-soundness capstone. The V2
chain (the mask sum is proved zero for V3), the
algebraic-adversary PC layer, the probability bounds, and the R1CS bridge
are on the map as well.

Statuses and edge verbs are in [PLAN.md](../../../PLAN.md), which also lists
what is still open. How each item of the security-analysis plan is covered
is in [security-analysis.md](security-analysis.md).
This wrapper is intentionally thin: we are not cloning the Ironwood book.
