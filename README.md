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

`v3_chain` gives `Az ∘ Bz = Cz` on the constraint domain, with the mask
sum equal to zero, in either mode. `V3Endpoint.sound` composes the `h₀`
opening, one nonzero domain per matrix, and `v3_chain`.
`sound_of_openings` reduces `ẑ`, `h₁`, `g₁`, and the matrix witnesses;
`sound_of_combined_matrix` is the `δ` batch; `matrix_sumcheck_of_selector`
is the selector-batched sum. `V3Batch.sound` is the endpoint for a
batch of circuits and instances as snarkVM runs it: the rowcheck,
lineval, and matrix checks are each one LC over the whole batch
(selectors, snarkVM's combiners, one quotient), and together they give
every instance `Az ∘ Bz = Cz` on its circuit's constraint domain.
`V3Batch.sound_of_transcript` runs the checks on the opened values,
reads the challenges and weights off a V3 transcript's squeezes, takes
"no squeezed element is in its bad set" as its one Fiat–Shamir
hypothesis, and proves the relation for the statement the transcript
absorbs. `V3Batch.adaptive_soundness` charges that hypothesis against an
adaptive prover: queries carry the earlier challenges, each squeeze's
bad set is read off its query, and at most `Q · b · |S|^{Q-1}` of the
`|S|^Q` oracle tapes yield an accepted transcript for a false statement.
`V3Batch.adaptive_soundness_concrete` computes `b` for the batch from
the SRS size (every committed polynomial below `D` powers) and the
largest domains.
snarkVM's batch weights `ν_i τ_{i,j}` are counted one drawn element at a
time. `PreprocessingAHP` is the public-coin argument in the algebraic
projection. `sound_r1cs` ends at the R1CS relation.
The PC layer is proved under an algebraic adversary (trapdoor breaks),
probabilities are counted per challenge and per oracle query, and the
Fiat–Shamir prefix binds the public inputs. `ahp_error_concrete` states
the AHP error with concrete residual degrees. `Fingerprint.lean`
kernel-checks a captured snarkVM V3 batch proof over two circuits with two
instances each: every coefficient of the three zero-eval LCs is Lean's
formula, and each LC vanishes over the BLS12-377 scalar field. Poseidon = RO, pairing hardness, and the algebraic-adversary
restriction stay floors.

The scope, the soundness spine, and how each security-analysis item is covered
are in [security-analysis.md](book/src/formal-verification/security-analysis.md).
The interactive picture is the
[proof map](book/src/formal-verification/proof-map.html).

### What remains

- The fingerprint stops at the zero-eval LC layer. The capture has field
  elements only, so MSM / pairing assembly is outside Lean. Byte
  encodings stay a floor. Sage proofs are not captured in this project.
- `knowledgeSoundness_bls` states the capstone at `ZMod bls12_377_r`.
  Primality of that modulus is a `Fact`, not a kernel proof.
- `V3Batch.adaptive_soundness`'s queries carry the earlier challenges,
  the standard multi-round Fiat–Shamir encoding. snarkVM's sponge
  absorbs only the messages; identifying the two is part of the
  Poseidon = RO floor.
- Poseidon = RO, pairing hardness, the algebraic adversary, the SRS,
  and index = circuit stay floors. The AHP simulator programs one
  opening and absorbs the witness into the ZK mask. A constant blinding
  shifts the hiding commitment along `gamma_g`, and one fresh hiding
  opening is simulation-extractable (`ZK.lean`).

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
  Lineval.lean                      -- lineval polynomial with M̂(α, X)
  MatrixSumcheck.lean               -- Lagrange closed form; |K| σ = M̂(α, β)
  MatrixBatch.lean                  -- one δ-batched matrix sumcheck over all circuits
  PublicInput.lean                  -- input subdomain, reindex_by_subdomain
  SonicPC.lean                      -- labeled polynomials, KZG, binding breaks
  Algebraic.lean                    -- KZG under an algebraic adversary, degree bounds
  OpeningBatch.lean                 -- batched Sonic openings
  FiatShamir.lean                   -- V3 absorb/squeeze schedule, forks
  Batching.lean                     -- multi-circuit combiners, selectors
  Selectors.lean                    -- selector = indicator; batched checks
  Probability.lean                  -- bad-challenge counts, adaptive union bound
  Combiners.lean                    -- batch weights drawn element by element
  Degree.lean                       -- concrete residual degrees in ahp_error
  FSBound.lean                      -- Fiat–Shamir query charging
  AdaptiveFS.lean                   -- queries carry the history; adaptive charging
  Statement.lean                    -- init_sponge binds the public inputs
  Match.lean                        -- typed accept, floors, toy fixtures
  Soundness.lean                    -- knowledge-soundness capstone
  Composition.lean                  -- v3_chain: mask sum zero and Az ∘ Bz = Cz
  Bridge.lean                       -- Int R1CS ↔ ZMod p; satisfies from rows
  Endpoint.lean                     -- PC reduction + matrix sumchecks + v3_chain
  BatchEndpoint.lean                -- the V3 endpoint batched over circuits and instances
  BatchDegree.lean                  -- batched residual degrees from D and the domains
  BatchFS.lean                      -- adaptive Fiat–Shamir soundness of the batch
  Fingerprint.lean                  -- captured snarkVM batch proof vs Lean LC formulas
  Fingerprint/Capture.lean          -- the capture, generated from fixtures/
  SpotCheck.lean                    -- source-pinned samples vs snarkVM
  ProofSize.lean                    -- proof element counts vs the spec
  AxiomCheck.lean                   -- assert_axioms / assert_computable
  TrustBoundary.lean                -- axiom-census (build-checked)
fixtures/fingerprint/               -- captured batch proof, capture patch, provenance
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
| [`protocol-docs`](https://github.com/ProvableHQ/protocol-docs) (submodule) | Algorithm identities, including V3 batching |
| [`varuna-sage-impl/docs/spec.pdf`](https://github.com/ProvableHQ/varuna-sage-impl/blob/main/docs/spec.pdf) | Protocol specification |
| [`varuna-sage-impl`](https://github.com/ProvableHQ/varuna-sage-impl) | SageMath reference (single-circuit R1CS, ZK) |
| [`snarkVM`](https://github.com/ProvableHQ/snarkVM) (submodule, pin in `Varuna.snarkVMPin`) | Deployed Rust implementation (`VarunaVersion.V3`); `SpotCheck.lean` samples, `Fingerprint.lean` captured proof |
| [Marlin](https://eprint.iacr.org/2019/1047) | Underlying AHP |
| [`mathlib4` v4.33.0](https://github.com/leanprover-community/mathlib4/releases/tag/v4.33.0) | Field, polynomials, roots of unity |

## License

Copyright 2026 Provable Inc.

Licensed under the Apache License, Version 2.0. See [LICENSE.md](LICENSE.md).
