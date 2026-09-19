# Formalizing Varuna

Lean 4 formal verification of the [Varuna](https://github.com/ProvableHQ/varuna-sage-impl)
zkSNARK — the Marlin-based proof system that secures Aleo / snarkVM.

The approach follows [zcash/ironwood](https://github.com/zcash/ironwood): a
successful `lake build` *is* the verification; a proof map records what is
proved, what is still a hypothesis, and what is left outside Lean; and a
trust-boundary census (stubbed in this first layer) will make those claims
build-time checks rather than prose.

## Current status

**Iteration 2 complete.** The holographic indexer is in Lean: row / col /
val interpolants recover sparse matrix entries on the nonzero domain,
and `assert_axioms` makes the census a build-time check.

**Iteration 3 complete.** The three AHP identities are in Lean:
rowcheck (`σ_A σ_B − σ_C = h₀ v_H`), univariate lineval sumcheck
(`∑ f = |K| σ`), and the rational matrix sumcheck on the sparse
`a(X)`, `b(X)` encoding. Accepting a challenge yields the algebraic
claim or Schwartz–Zippel break data (`inspectResidual`).

Every layer above the AHP (polynomial commitments, Fiat–Shamir, the
deployed verifier) is on the map as a hypothesis, definition, or
out-of-Lean floor. See [PLAN.md](PLAN.md) and the
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
