# Proof Map

One connected picture of the Varuna verifier-soundness argument — what is in
Lean, what is still a hypothesis, and what is left outside the kernel.

Open the interactive map:

**[proof-map.html](proof-map.html)**

The spine runs down the left: accepting proof → Fiat–Shamir challenges →
polynomial-commitment openings → AHP checks → R1CS. Iteration 0 colours
the R1CS relation. Iteration 1 colours evaluation-domain vanishing
(`v_H(α)=0 ↔ α∈H`) and the Schwartz–Zippel bad-set bound.

Statuses, edge verbs, and the iteration plan are in [PLAN.md](../../../PLAN.md).
This wrapper is intentionally thin: we are not cloning the Ironwood book.
