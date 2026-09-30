# Formal verification of Varuna

This is the plan for verifying the Varuna proof system in Lean 4, in the
same spirit as [zcash/ironwood](https://github.com/zcash/ironwood): a
layered Lean development over Mathlib, a proof map that makes the
theorem graph and its remaining holes visible, and a trust-boundary
census so “what you are trusting” is a build-time property rather than
a comment.

The interactive map is [`book/src/formal-verification/proof-map.html`](book/src/formal-verification/proof-map.html).
Open that file in a browser. Nodes are coloured **proven / hypothesis /
out-of-Lean / definition / goal**. How each item of the security-analysis
plan is covered is in
[`book/src/formal-verification/security-analysis.md`](book/src/formal-verification/security-analysis.md).

---

## 1. What is being verified

**Target.** Knowledge soundness of the *deployed* Varuna verifier: the
object in snarkVM that validators actually run. Completeness of the
individual checks is proved alongside soundness. Zero-knowledge
(a simulator) is not claimed.

Varuna is an optimized Marlin ([CHMMVW19](https://eprint.iacr.org/2019/1047))
AHP compiled through a Sonic-style polynomial commitment and made
non-interactive with Fiat–Shamir. The formalization targets
snarkVM’s `VarunaVersion.V2` and names:

- universal, updatable SRS
- holographic indexer (row / col / val oracles for `A, B, C`)
- three PIOPs: rowcheck, univariate (lincheck) sumcheck, rational
  (matrix) sumcheck — snarkVM’s linear combinations
  `rowcheck_zerocheck`, `lineval_sumcheck`, `matrix_sumcheck`
- Sonic PC openings on BLS12-377
- multi-circuit / multi-instance batching, including the extra IOP
  round added in 2025 to stop adaptive statement selection
- optional zero-knowledge (masking polynomials)

The constraint language is R1CS (`Az ∘ Bz = Cz`).

**Non-goals (separate projects).**

| Concern | Where it lives |
| --- | --- |
| snarkVM gadget ↔ spec correctness | ACL2 AleoVM circuits; `aleovm-circuits-lean` |
| Aleo instructions / Leo compilation | ACL2 language books; future verifying compiler |
| AleoBFT consensus | `aleobft-formal` (ACL2) |
| Pairing / curve arithmetic as a library | Mathlib + a future CompElliptic-style pin |

The proof system says: *if the verifier accepts, then (under the
named assumptions) there exists a witness satisfying the R1CS*. It
does not say the R1CS means what the Leo programmer thought. In ZK
mode the proved relation is the shifted one in §5, not R1CS.

---

## 2. Ironwood conventions we adopt

Ironwood’s [formal-verification page](https://zcash.github.io/ironwood/formal-verification.html)
is the style guide. Three rules transfer directly.

### 2.1 Breaks as computed data

A theorem `soundness ∨ ∃-break` is vacuous in a prime-order group
(nontrivial discrete-log relations always exist) and for compressing
hashes (collisions always exist). Ironwood therefore makes every
reduction a **plain `def`** that *returns* the breaking data
(coefficients, colliding queries), with `Prop` certificates attached.

For Varuna the analogous breaks are:

- a Schwartz–Zippel root (AHP identity failed, challenge hit the
  vanishing set)
- a polynomial-commitment binding break (two openings of one
  commitment)
- a discrete-log / pairing-assumption break extracted from a
  Sonic-PC forgery
- a random-oracle collision or programming miss

Extractors are `def`s, not `∃` in `Prop`, and `noncomputable` is
forbidden on that path.

### 2.2 Trust discipline

General theorems rest only on `propext`, `Classical.choice`,
`Quot.sound`. Concrete closed facts (a captured snarkVM proof’s
MSM/pairing equation, a curve cardinality) may use `native_decide`,
and that extension of the trusted base is **named** on the census.

`Varuna/TrustBoundary.lean` is the census file. `assert_axioms` /
`assert_computable` in `Varuna/AxiomCheck.lean` make the trusted base a
build-time property. CI still fails on `sorry` via `lake build --wfail`.

Toy-field samples in `Match.lean` / `SpotCheck.lean` use kernel `decide`,
not `native_decide`, so the census stays those three axioms. Correspondence
with snarkVM is source-pinned samples (`Varuna.snarkVMPin`) and one captured
V2 proof (`Fingerprint.lean`), which is also kernel `decide`, over the
BLS12-377 scalar field. The group-level MSM / pairing assembly is not captured.

### 2.3 Modelling boundaries are not axioms

Hash-as-RO, pairing-as-hardness, “the verifying key is the index of
the real circuit”, and byte-level encodings are **floors** on the
proof map. They do not appear as Lean `axiom`s. A reader of a
capstone theorem must still be able to see them as explicit
hypotheses or as out-of-Lean identification steps.

---

## 3. The soundness spine

Ironwood’s spine is

```
accepting proof → verifier equation → IPA tree → opening → SnarkRelation
```

Varuna’s spine, reading the Sage verifier and
`snarkVM/.../varuna/ahp/ahp.rs`, is

```
accepting proof
  → Fiat–Shamir challenges          (schedule proved; Poseidon = RO is a floor)
  → Sonic-PC openings               (h₀ reduction proved; pairing hardness is a floor)
  → AHP linear combinations evaluate to zero
      rowcheck_zerocheck
      lineval_sumcheck
      matrix_sumcheck
  → (Az + e) ∘ Bz = Cz              (e = 0 in NonZK; unchecked in ZK)
  → R1CS witness                    (NonZK, via Bridge.lean)
```

`V2Endpoint.sound` is the composed theorem: a no-break opening of the
rowcheck quotient `h₀`, the three matrix sumchecks, and `v2_chain`
give `(Az + e) ∘ Bz = Cz` on `R`. `sound_nonZK` ends at `satisfies`.
The holes in that composition are in §5.

```
  deployed snarkVM verifier          (definition; LC layer fingerprinted)
           │
           ▼
  accepting proof                    (typed predicate, proved iff the Prop)
           │
           ▼
  FS transcript / challenges         (schedule proved; Poseidon = RO is a floor)
           │
           ▼
  PC openings bind the oracles       (algebraic reduction; pairing/SRS floors)
           │
           ▼
  AHP verifier equations             (proved)
     rowcheck ──► lincheck ──► matrix sumcheck
           │
           ▼
  (Az + e) ∘ Bz = Cz                 (proved; e unchecked in ZK)
           │
           ▼
  R1CS witness                       (proved in NonZK)
```

---

## 4. What Lean checks

Sorry-free. `lake build --wfail` is the verifier. A node on the proof
map is `proven` only when its anchor names a real declaration.

**R1CS relation** (`PrimeField.lean`, `R1CS.lean`). Sparse constraints
and the Hadamard predicate agree: `satisfies_iff_hadamard`. A
multiplication constraint is multiplication (`mulConstraint_holds_iff`).
Formatted public inputs prepend the constant-`1` slot and are admissible
iff their length is a power of two. Toy instance `3 * 5 = 15` over `𝔽₁₇`.

**Field, domains, vanishing** (`Field.lean`, `Domain.lean`). Mathlib
`ZMod p` (`v4.33.0`). Multiplicative subgroup of size `2^k`,
`v_H(X) = X^{|H|} - 1` with `v_H(α) = 0 ↔ α ∈ H`, Lagrange basis,
Schwartz–Zippel (`schwartzZippel_card`, `szBadSet`). The R1CS relation
stays on integer residues; `Bridge.lean` sends them to `ZMod p`
(`satisfies_iff_zmod`, `satisfies_of_rows`).

**Indexer** (`Indexer.lean`). Row / col / val interpolants recover
sparse entries on the nonzero domain (`rowOracle_eval` and siblings).
`holographicEval_at_nodes` is the snarkVM identity
`M(a,b)=∑_k val(k) L^R_row(k)(a) L^C_col(k)(b)` at domain nodes.

**AHP** (`AHP.lean`, `Lineval.lean`, `MatrixSumcheck.lean`,
`Degree.lean`). The three checks are polynomial identities.
`inspectResidual` returns either “identically zero” or the challenge
as break data. Rowcheck gives the Hadamard identity on `H`. The
faithful V2 lineval polynomial is `s + Σ η_M M̂(α, X) ẑ`, and
`Σ_C M̂(α, c) ẑ(c) = LDE(Mz)(α)`. The matrix sumcheck proves
`|K| σ = M̂(α, β)` (`matrix_sumcheck_value`). `ahp_error_concrete`
is the adaptive union bound with residual degrees computed from the
prover’s degree bounds.

**Polynomial commitment** (`SonicPC.lean`, `Algebraic.lean`,
`OpeningBatch.lean`). Labeled polynomials, linear combinations
including the three zero-eval LCs, honest KZG completeness, and
binding as computed data: two openings of one commitment
(`pairingBreak_of_double_opening`), a wrong opening
(`inspectOpening_break`), a violated degree bound
(`inspectDegree_break`), and batched openings. Pairing groups are
abstract. Hardness is the `pairingHardness` floor; the algebraic
adversary is the `algebraicAdversary` floor.

**Fiat–Shamir** (`FiatShamir.lean`, `Statement.lean`, `FSBound.lean`).
V2 absorb-then-squeeze: combiners, `α` only, extra `prepareThird`
(`η_b, η_c` delayed), `β`, `δ`, `γ`. Each challenge is a function of
the prefix before that squeeze. `init_sponge` binds the public inputs
(`v2Init_injective`). Forks and collisions are `def`s. `fs_query_charge`
bounds lazy-oracle tapes by `Q · b / |S|`. Poseidon = RO is a floor.

**Batching** (`Batching.lean`, `Selectors.lean`, `PublicInput.lean`).
First combiner of each family is `1`. Selectors are indicators on `H`.
`batchedZerocheck_extract` and `batchedSumcheck_extract` give per-circuit
claims or a lucky combination. The extra round binds instance sums
before `η_b, η_c`. `reindex_by_subdomain` and `ẑ = x̂` on the input
subdomain.

**Faithfulness** (`Match.lean`, `SpotCheck.lean`, `Fingerprint.lean`,
`ProofSize.lean`). `TypedProof.accepts` agrees with the `Prop` accept.
Modelling floors are enumerated and are not axioms. Toy-field fixtures
accept honest zeros and reject flipped evaluations. `SpotCheck.lean`
kernel-checks source samples against the pinned `snarkVM/` submodule.
`Fingerprint.lean` kernel-checks one honest snarkVM V2 hiding-mode
proof: every coefficient of the three zero-eval LCs is Lean's formula,
and each LC vanishes over the BLS12-377 scalar field. It also pins
`row(γ) col(γ) ≠ row_col(γ)`: `matrixBPoly` and the deployed `b` agree
only on `K`.

**Capstone** (`Composition.lean`, `Endpoint.lean`, `Soundness.lean`).
`v2_chain` gives `(Az + e) ∘ Bz = Cz` with `e` the mask sum.
`shifted_witness_accepts` shows the unchecked mask sum is exploitable
in ZK mode (confirmed against the pinned snarkVM). `v2_chain_nonZK`
and `satisfies_of_rows` give the R1CS rows. `V2Endpoint.sound` composes
the `h₀` opening reduction, the three matrix sumchecks, and `v2_chain`.
`knowledgeSoundness` is the earlier Marlin-shaped statement (three
domain identities and a zero batch sum). `knowledgeSoundness_rests_on_floors`
keeps the floors explicit. Probability counts are in `Probability.lean`.

---

## 5. What remains

**Endpoint composition.** `V2Endpoint.sound` still takes as hypotheses:

- openings of `ẑ`, `h₁`, `g₁`, and the matrix witnesses (each reduces
  the same way as `h₀`, via `value_correct_of_inspect_none`)
- the matrix residuals themselves (the `γ` step is `matrix_extract`)
- one `K` for all three matrices, so the selector-batched sumcheck
  (`batchedSumcheck_extract`) is not composed in

**Fiat–Shamir bad sets.** `fs_break_count` says a V2 output with a
break at any squeeze is a query hit, if its challenges were answered
on its queries. No single theorem derives every V2 squeeze’s bad set
from the transcript.

**Interactive primitive.** Marlin’s public-coin preprocessing argument
of knowledge is not an interactive object in Lean. The development
works in the algebraic-adversary projection (`represent`, `ProofView`).

**Faithfulness past the LC layer.** The fingerprint covers zero-eval
LC coefficients of one captured proof. The group-level MSM / pairing
assembly is outside Lean. Captured Sage proofs are not pinned. Byte
encodings stay a floor.

**Concrete field on the generic statements.** Algebraic theorems are
over an arbitrary `Field`. The BLS12-377 scalar field is the carrier
of the fingerprint, not of `V2Endpoint.sound`.

**Mask sum (protocol gap).** In ZK mode nothing checks `e = Σ_C s = 0`.
A prover can prove `5 · 1 = 0` (`xIsZero_shifted`). Closing it needs a
new `VarunaVersion`: either enforce `e = 0` (for example a checked
degree bound on a mask of the form `X t(X) + v_C(X) r(X)`), or absorb
a claimed mask sum before `α`. This is not a missing lemma about the
deployed verifier.

**Named floors, not open proofs.** Poseidon = RO, pairing / trapdoor
hardness, algebraic adversary, SRS, encodings, index = circuit.
Zero knowledge (a simulator), hiding, and simulation extractability
are excluded.

**Proof-map check.** A `book/validate-proof-journey.py` (Ironwood has
one) should check that every `proven` anchor exists in the Lean sources
and that every edge’s `via` is a real name. Not written yet.

---

## 6. Proof-map discipline

Copied from Ironwood’s `proof-map.md` / `proof-map-embed.html`:

- **entails** — B follows from A (and any other incoming arrows)
- **discharges** — A proves away hypothesis B
- **rests on** — B is an assumption A still needs (in-Lean `hyp` or
  out-of-Lean floor)

Statuses:

| Status | Meaning |
| --- | --- |
| `proven` | A named Lean theorem exists; `lake build` checks it |
| `hyp` | In-Lean hypothesis, or a lemma stated but not proved |
| `floor` | Modelling identification, not a Lean axiom |
| `object` | A definition (data or `Prop`), not a theorem |
| `goal` | Advertised capstone |

A node is `proven` only when its `anchor` field names a real
declaration. The unchecked mask sum (`maskSum`) stays `hyp`.

---

## 7. Sources, pins, and correspondence

Pin sources by commit, not by branch.

| Source | Use |
| --- | --- |
| `ProvableHQ/varuna-sage-impl` `docs/spec.pdf` | Human protocol spec |
| `ProvableHQ/varuna-sage-impl` Sage PIOPs | Executable identities for rowcheck / sumchecks |
| `ProvableHQ/protocol-docs` (`protocol-docs/` submodule) | Algorithm identities (rowcheck, lincheck, matrix sumcheck), including VarunaVersion V2 batching |
| `ProvableHQ/snarkVM` submodule (`Varuna.snarkVMPin`) `algorithms/src/snark/varuna/` | Deployed AHP, FS, PC, batching (target: `VarunaVersion.V2`); sampled in `SpotCheck.lean` |
| `ProvableHQ/snarkVM` `algorithms/src/polycommit/sonic_pc/` and `kzg10/` | PC interface and pairing check |
| `leanprover-community/mathlib4` tag `v4.33.0` | Field, `Polynomial`, roots of unity, Lagrange |
| `fixtures/fingerprint/` | One captured snarkVM V2 proof |

The Sage implementation is single-circuit R1CS with ZK and without
batching or lookups. Lean should not treat Sage as the deployed
system: it is the readable PIOP, snarkVM is the verifier of record.

---

## 8. Build, CI, and documentation scope

- `lake build --wfail` is the verifier. CI runs it
  (`.github/workflows/lean.yml`) and fetches the Mathlib cache.
- Mathlib is pinned at tag `v4.33.0` (toolchain `v4.33.0`).
- `assert_axioms` / `assert_computable` in `Varuna/AxiomCheck.lean`
  bound the census; `sorryAx` fails the build.
- We are **not** cloning the Ironwood book (mdBook, proof journey,
  glossary, CI-checks essay). The proof map plus this plan plus a
  short README are the documentation for now.
