# Formalizing Varuna

Lean 4 formal verification of the [Varuna](https://github.com/ProvableHQ/varuna-sage-impl)
zkSNARK — the Marlin-based proof system that secures Aleo / snarkVM.

The approach follows [zcash/ironwood](https://github.com/zcash/ironwood): a
successful `lake build` *is* the verification; a proof map records what is
proved, what is still a hypothesis, and what is left outside Lean; and a
trust-boundary census makes those claims build-time checks rather than
prose.

## Current status

The formalization targets snarkVM’s **`VarunaVersion.V3`**. Lean checks
the algebraic verifier: the R1CS relation (sparse constraints equivalent
to `Az ∘ Bz = Cz`), evaluation domains and Schwartz–Zippel, the
holographic indexer, the three AHP identities, Sonic-KZG openings and
binding breaks, the V3 Fiat–Shamir schedule, and multi-circuit batching.
`TypedProof.accepts` is the typed accept predicate. `SpotCheck.lean`
kernel-checks source samples against the pinned `snarkVM/` submodule.
`assert_axioms` makes the census a build-time check.

`v2_chain` is the old schedule, with `η_A` fixed at `1`. It concludes
`(Az + e) ∘ Bz = Cz`, and `shifted_witness_accepts` shows a prover can
prove `5 · 1 = 0` against that verifier. V3 squeezes `η_A` after the
mask and the sums. `v3_chain` then forces `e = 0` and the unshifted
rows, and `v3_shifted_residual_ne` shows the V2 messages do not make
the V3 lineval residual identically zero. `V3Endpoint.sound` composes
the `h₀` opening, the matrix sumchecks, and `v3_chain`; `sound_r1cs`
ends at the R1CS relation in either mode. The PC layer is proved
under an algebraic adversary (trapdoor breaks), probabilities are counted
per challenge and per oracle query, and the Fiat–Shamir prefix binds the
public inputs. `V2Endpoint.sound` composes the `h₀` opening reduction,
the matrix sumchecks, and `v2_chain` in one theorem; `ahp_error_concrete`
states the AHP error with concrete residual degrees. `Fingerprint.lean`
kernel-checks a captured snarkVM V2 proof: every coefficient of the three
zero-eval LCs is Lean's formula, and each LC vanishes over the BLS12-377
scalar field. Poseidon = RO, pairing hardness, and the algebraic-adversary
restriction stay floors.

See [PLAN.md](PLAN.md) and the
[proof map](book/src/formal-verification/proof-map.html).
How each item of the security-analysis plan is covered is in
[security-analysis.md](book/src/formal-verification/security-analysis.md).

### What remains

- Compose the other openings (`ẑ`, `h₁`, `g₁`, matrix witnesses) the way
  `h₀` is composed, and compose the matrix-residual `γ` step
  (`matrix_extract`). The endpoint uses one `K` for all matrices; the
  selector-batched sumcheck is not in it.
- One theorem that derives every V2 squeeze’s bad set from the transcript.
- The fingerprint stops at the zero-eval LC layer. MSM / pairing assembly
  is outside Lean.
- Algebraic theorems are over an arbitrary field. BLS12-377 is the
  fingerprint’s carrier, not `V3Endpoint.sound`’s.

Zero knowledge (a simulator) is not claimed. The V2 mask-sum shift is
a theorem about that schedule; V3 closes it.

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
  PrimeField.lean                   -- [0, p) integer carrier for the R1CS relation
  R1CS.lean                         -- SNARK relation, sparse ↔ Hadamard
  Field.lean                        -- Mathlib `ZMod p`
  Domain.lean                       -- EvalDomain, v_H, Lagrange, SZ
  Indexer.lean                      -- holographic row/col/val oracles
  AHP.lean                          -- rowcheck, lineval, matrix sumcheck
  Lineval.lean                      -- V2 lineval polynomial with M̂(α, X)
  MatrixSumcheck.lean               -- Lagrange closed form; |K| σ = M̂(α, β)
  PublicInput.lean                  -- input subdomain, reindex_by_subdomain
  SonicPC.lean                      -- labeled polynomials, KZG, binding breaks
  Algebraic.lean                    -- KZG under an algebraic adversary, degree bounds
  OpeningBatch.lean                 -- batched Sonic openings
  FiatShamir.lean                   -- V2 absorb/squeeze schedule, forks
  Batching.lean                     -- multi-circuit combiners, selectors
  Selectors.lean                    -- selector = indicator; batched checks
  Probability.lean                  -- bad-challenge counts, adaptive union bound
  Degree.lean                       -- concrete residual degrees in ahp_error
  FSBound.lean                      -- Fiat–Shamir query charging
  Statement.lean                    -- init_sponge binds the public inputs
  Match.lean                        -- typed accept, floors, toy fixtures
  Soundness.lean                    -- knowledge-soundness capstone
  Composition.lean                  -- V2 chain and the mask-sum shift
  Bridge.lean                       -- Int R1CS ↔ ZMod p; satisfies from rows
  Endpoint.lean                     -- PC reduction + matrix sumchecks + v2_chain
  Fingerprint.lean                  -- captured snarkVM proof vs Lean LC formulas
  Fingerprint/Capture.lean          -- the capture, generated from fixtures/
  SpotCheck.lean                    -- source-pinned samples vs snarkVM
  ProofSize.lean                    -- proof element counts vs the spec
  AxiomCheck.lean                   -- assert_axioms / assert_computable
  TrustBoundary.lean                -- axiom-census (build-checked)
PLAN.md                             -- verification plan
fixtures/fingerprint/               -- captured V2 proof, capture patch, provenance
scripts/fingerprint_to_lean.py      -- fixture → Fingerprint/Capture.lean
protocol-docs/                      -- algorithm spec (git submodule)
snarkVM/                            -- deployed verifier (git submodule)
book/src/formal-verification/
  proof-map.md                      -- thin wrapper
  proof-map.html                    -- interactive dependency map
  security-analysis.md              -- security-analysis plan vs Lean coverage
```

## Sources of truth

| Artifact | Role |
| --- | --- |
| [`protocol-docs`](https://github.com/ProvableHQ/protocol-docs) (submodule) | Algorithm identities, including V2 batching |
| [`varuna-sage-impl/docs/spec.pdf`](https://github.com/ProvableHQ/varuna-sage-impl/blob/main/docs/spec.pdf) | Protocol specification |
| [`varuna-sage-impl`](https://github.com/ProvableHQ/varuna-sage-impl) | SageMath reference (single-circuit R1CS, ZK) |
| [`snarkVM`](https://github.com/ProvableHQ/snarkVM) (submodule, pin in `Varuna.snarkVMPin`) | Deployed Rust implementation (`VarunaVersion.V2`); `SpotCheck.lean` samples, `Fingerprint.lean` captured proof |
| [Marlin](https://eprint.iacr.org/2019/1047) | Underlying AHP |
| [`mathlib4` v4.33.0](https://github.com/leanprover-community/mathlib4/releases/tag/v4.33.0) | Field, polynomials, roots of unity |

## License

Copyright 2026 Provable Inc.

Licensed under the Apache License, Version 2.0. See [LICENSE.md](LICENSE.md).
