# Formalizing Varuna

Lean 4 formal verification of the [Varuna](https://github.com/ProvableHQ/varuna-sage-impl)
zkSNARK — the Marlin-based proof system that secures Aleo / snarkVM.

The approach follows [zcash/ironwood](https://github.com/zcash/ironwood): a
successful `lake build` *is* the verification; a proof map records what is
proved, what is still a hypothesis, and what is left outside Lean; and a
trust-boundary census (stubbed in this first layer) will make those claims
build-time checks rather than prose.

## Current status

**Iteration 0 complete.** The R1CS relation Varuna proves knowledge of is
defined in two views (sparse constraints and the AHP Hadamard form) and
proved equivalent:

- an empty constraint system is satisfied
- a multiplication constraint holds iff the assigned values multiply
- the empty Hadamard system holds
- sparse constraints ↔ `Az ∘ Bz = Cz`, including duplicate columns and
  implicit zeros
- formatted public inputs prepend the constant-`1` slot and are
  admissible iff their length is a power of two
- a concrete toy instance (`3 * 5 = 15` over `𝔽₁₇`) satisfies the
  multiplication constraint in both views

Every layer above the relation (AHP, polynomial commitments,
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
  PrimeField.lean                   -- [0, p) carrier (Mathlib in iteration 1)
  R1CS.lean                         -- SNARK relation, sparse ↔ Hadamard
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

## License

Copyright 2026 Provable Inc.

Licensed under the Apache License, Version 2.0. See [LICENSE.md](LICENSE.md).
