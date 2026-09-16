# Proof Map

One connected picture of the Varuna verifier-soundness argument — what is in
Lean, what is still a hypothesis, and what is left outside the kernel.

Open the interactive map:

**[proof-map.html](proof-map.html)**

The spine runs down the left: accepting proof → Fiat–Shamir challenges →
polynomial-commitment openings → AHP checks → R1CS. The first iteration
colours only the R1CS relation, and only partially (`satisfies_nil`,
`mulConstraint_holds_iff`, `hadamardSat_zero`). The general sparse ↔
Hadamard equivalence is still a hypothesis.

Statuses, edge verbs, and the iteration plan are in [PLAN.md](../../../PLAN.md).
This wrapper is intentionally thin: we are not cloning the Ironwood book.
