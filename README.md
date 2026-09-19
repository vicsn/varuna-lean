# Formalizing Varuna

Lean 4 formal verification of the [Varuna](https://github.com/ProvableHQ/varuna-sage-impl)
zkSNARK — the Marlin-based proof system that secures Aleo / snarkVM.

The approach follows [zcash/ironwood](https://github.com/zcash/ironwood): a
successful `lake build` *is* the verification; a proof map records what is
proved, what is still a hypothesis, and what is left outside Lean; and a
trust-boundary census makes those claims build-time checks rather than
prose.

## Current status

**Iteration 2 complete.** The holographic indexer is in Lean: row / col /
val interpolants recover sparse matrix entries on the nonzero domain,
and `assert_axioms` makes the census a build-time check.

**Iteration 3 complete.** The three AHP identities are in Lean:
rowcheck (`σ_A σ_B − σ_C = h₀ v_H`), univariate lineval sumcheck
(`∑ f = |K| σ`), and the rational matrix sumcheck on the sparse
`a(X)`, `b(X)` encoding. Accepting a challenge yields the algebraic
claim or Schwartz–Zippel break data (`inspectResidual`).

**Iteration 4 complete.** Sonic-KZG is in Lean: labeled polynomials,
linear combinations (including the three zero-eval LCs), honest opening
completeness, and binding as computed break data
(`pairingBreak_of_double_opening`).

**Iteration 5 complete.** The V2 Fiat–Shamir schedule is in Lean:
absorb-then-squeeze (`α` only in the second squeeze; extra
`prepare_third` round), with forks and RO collisions as computed data
(`inspectFork`, `inspectCollision`). Poseidon = RO remains a floor.

**Iteration 6 complete.** Multi-circuit batching is in Lean: first
combiners are `1`, selector polynomials lift subdomain residuals to
the common domain, and the extra round binds instance sums before
`η_b, η_c`. `inspectBatch` is the computed batch-break.

**Iteration 7 complete.** The typed accept predicate and modelling
floors live in `Match.lean`. Toy-field fixtures accept honest zeros
and reject flipped LC evaluations; the KZG pairing equation is checked
on a multiplicative `𝔽₁₇` pairing. BLS12-377 captures remain a pin.

**Iteration 8 complete.** `knowledgeSoundness` is the advertised
endpoint: an accepting algebraic V2 transcript with no computed AHP
or batch break yields the three domain identities (Hadamard on `H`,
lineval sum, matrix on `K`). Poseidon = RO and pairing hardness stay
floors.

See [PLAN.md](PLAN.md) and the
[proof map](book/src/formal-verification/proof-map.html).

The formalization targets snarkVM’s **`VarunaVersion.V2`**.

This repository verifies the **proof system**, not the circuits it
proves. Circuit-gadget correctness is a separate effort
([aleovm-circuits-lean](https://github.com/ProvableHQ/pfcs) / ACL2).

## Verifying the proofs

Install [`elan`](https://github.com/leanprover/elan). The
[`lean-toolchain`](lean-toolchain) pin is installed automatically.

```sh
lake build --wfail
```

A successful build re-elaborates every proof. There is no separate test
suite: the proofs *are* the verification.

## Layout

```
Varuna.lean                         -- library root (imports the census)
Varuna/
  PrimeField.lean                   -- [0, p) integer carrier (iteration 0)
  R1CS.lean                         -- SNARK relation, sparse ↔ Hadamard
  Field.lean                        -- Mathlib `ZMod p` (iteration 1)
  Domain.lean                       -- EvalDomain, v_H, Lagrange, SZ
  Indexer.lean                      -- holographic row/col/val oracles
  AHP.lean                          -- rowcheck, lineval, matrix sumcheck
  SonicPC.lean                      -- labeled polynomials, KZG, binding breaks
  FiatShamir.lean                   -- V2 absorb/squeeze schedule, forks
  Batching.lean                     -- multi-circuit combiners, selectors
  Match.lean                        -- typed accept, floors, toy fixtures
  Soundness.lean                    -- knowledge-soundness capstone
  AxiomCheck.lean                   -- assert_axioms / assert_computable
  TrustBoundary.lean                -- axiom-census (build-checked)
PLAN.md                             -- verification plan
protocol-docs/                      -- algorithm spec (git submodule)
book/src/formal-verification/
  proof-map.md                      -- thin wrapper
  proof-map.html                    -- interactive dependency map
```

## Sources of truth

| Artifact | Role |
| --- | --- |
| [`protocol-docs`](https://github.com/ProvableHQ/protocol-docs) (submodule) | Algorithm identities, including V2 batching |
| [`varuna-sage-impl/docs/spec.pdf`](https://github.com/ProvableHQ/varuna-sage-impl/blob/main/docs/spec.pdf) | Protocol specification |
| [`varuna-sage-impl`](https://github.com/ProvableHQ/varuna-sage-impl) | SageMath reference (single-circuit R1CS, ZK) |
| `snarkVM/algorithms/src/snark/varuna/` | Deployed Rust implementation (`VarunaVersion.V2`) |
| [Marlin](https://eprint.iacr.org/2019/1047) | Underlying AHP |
| [`mathlib4` v4.33.0](https://github.com/leanprover-community/mathlib4/releases/tag/v4.33.0) | Field, polynomials, roots of unity |

## License

Copyright 2026 Provable Inc.

Licensed under the Apache License, Version 2.0. See [LICENSE.md](LICENSE.md).
