# Formalizing Varuna

Lean 4 formal verification of the [Varuna](https://github.com/ProvableHQ/varuna-sage-impl)
zkSNARK — the Marlin-based proof system that secures Aleo / snarkVM.

The approach follows [zcash/ironwood](https://github.com/zcash/ironwood): a
successful `lake build` *is* the verification; a proof map records what is
proved, what is still a hypothesis, and what is left outside Lean; and a
trust-boundary census (stubbed in this first layer) will make those claims
build-time checks rather than prose.

## Current status

**Iteration 1 complete.** Mathlib `v4.33.0` is pinned. Evaluation
domains, `v_H(α) = 0 ↔ α ∈ H`, Lagrange basis, and univariate
Schwartz–Zippel (`szBadSet`) are in Lean. The R1CS relation from
iteration 0 remains the statement the SNARK is about.

Every layer above domains (indexer, AHP PIOPs, polynomial commitments,
Fiat–Shamir, the deployed verifier) is on the map as a hypothesis,
definition, or out-of-Lean floor. See [PLAN.md](PLAN.md) and the
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
  TrustBoundary.lean                -- axiom-census stub
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
