# Formal verification of Varuna

This is the plan for verifying the Varuna proof system in Lean 4, in the
same spirit as [zcash/ironwood](https://github.com/zcash/ironwood): a
layered Lean development over (eventually) Mathlib, a proof map that
makes the theorem graph and its remaining holes visible, and a
trust-boundary census so “what you are trusting” is a build-time
property rather than a comment.

The interactive map is [`book/src/formal-verification/proof-map.html`](book/src/formal-verification/proof-map.html).
Open that file in a browser. Nodes are coloured **proven / hypothesis /
out-of-Lean / definition / goal**. Iteration 0 colours the R1CS relation,
including the sparse ↔ Hadamard equivalence.

---

## 1. What is being verified

**Target.** Knowledge soundness (and, later, completeness and
zero-knowledge) of the *deployed* Varuna verifier: the object in
snarkVM that validators actually run.

Varuna is an optimized Marlin ([CHMMVW19](https://eprint.iacr.org/2019/1047))
AHP compiled through a Sonic-style polynomial commitment and made
non-interactive with Fiat–Shamir. Deployed features that the
formalization must eventually name, even if they are out of the first
iterations:

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
does not say the R1CS means what the Leo programmer thought.

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

Iteration 0 does not yet have reductions. From the first AHP soundness
lemma onward, extractors must be `def`s, not `∃` in `Prop`, and
`noncomputable` is forbidden on that path.

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
  → Fiat–Shamir challenges
  → Sonic-PC openings
  → AHP linear combinations evaluate to zero
      rowcheck_zerocheck
      lineval_sumcheck
      matrix_sumcheck
  → Az ∘ Bz = Cz
  → R1CS witness
```

The bottom rung is what iteration 0 starts to put in Lean. Everything
above it is drawn on the map so later work has a slot, not so it
looks finished.

```
  deployed snarkVM verifier          (definition / faithfulness)
           │
           ▼
  accepting proof                    (definition)
           │
           ▼
  FS transcript / challenges         (definition; Poseidon = RO is a floor)
           │
           ▼
  PC openings bind the oracles       (hypothesis; pairing/SRS floors)
           │
           ▼
  AHP verifier equations             (definition + proof)
     rowcheck ──► lincheck ──► matrix sumcheck
           │
           ▼
  Az ∘ Bz = Cz                       (definition + proof)
           │
           ▼
  knowledge-soundness capstone       (goal)
```

---

## 4. Iterations

Each iteration is meant to be a self-contained PR: sorry-free on its
own claims, `lake build --wfail` green, proof-map statuses updated,
census extended. Do not mark a node `proven` until a named Lean
declaration exists.

### Iteration 0 — R1CS relation (complete)

**Goal.** A Lean carrier for the statement Varuna is *about*.

**Delivered.**

- `Varuna.PrimeField` — `[0, p)` add/mul, including distributivity
- `Varuna.R1CS` — sparse constraints, Hadamard predicate, dense matrices
- `satisfies_nil`, `satisfies_append`
- `mulConstraint_holds_iff` — `(x)(y)=(out) ↔ assigned product`
- `hadamardSat_zero` — empty matrix system
- `coeffOf_duplicate`, `coeffOf_eq_zero_of_not_mem` — duplicate columns
  and implicit zeros
- `satisfies_iff_hadamard` — sparse list ↔ `Az ∘ Bz = Cz`
- formatted public-input convention: `formatPublicInput` prepends `1`,
  `formattedPublicInputAdmissible` requires `|x| = 2^k`, `padZeros`
  matches snarkVM input padding
- `toy_mul_holds` / `formatted_toy_holds` — `3 * 5 = 15` over `𝔽₁₇`
- `TrustBoundary` stub printing those axioms
- proof map with the full spine drawn and this layer coloured `proven`

**Exit criterion (met).** `satisfies cs asg p ↔ hadamardSat (toMatrix cs) …`
with no `sorry`, and the census lists it.

### Iteration 1 — Mathlib carrier, domains, vanishing (complete)

**Goal.** Algebraic facts every later PIOP lemma quotes.

**Delivered.**

- Mathlib pin `v4.33.0` (toolchain `leanprover/lean4:v4.33.0`), `lake-manifest.json`
- `Varuna.Field` — `Fp p := ZMod p` with `Fact p.Prime` (toy `𝔽₁₇`)
- `Varuna.EvalDomain` — multiplicative subgroup of size `2^k` with
  primitive generator, matching snarkVM `EvaluationDomain`
- `v_H(X) = X^{|H|} - 1` and `v_H(α) = 0 ↔ α ∈ H`
- Lagrange basis: `1` at one node, `0` at the others
- `schwartzZippel_card` / `szBadSet` — at most `deg` roots; a miss is
  not a root
- formatted public-input `PowTwo` ↔ core `Nat.isPowerOfTwo`

The R1CS relation remains on the iteration-0 integer carrier; AHP
identities from here on are over a Mathlib `Field`. A bridge lemma can
land when the indexer consumes both.

**Exit criterion (met).** Vanishing iff, Schwartz–Zippel bound, Mathlib
pin, no `sorry`.

### Iteration 2 — Holographic indexer (complete)

**Goal.** Sparse matrices become oracles that recover entries on `K`.

**Delivered.**

- `Varuna.CircuitInfo` matching snarkVM (public inputs, variables,
  constraints, nonzero counts)
- `rowOracle` / `colOracle` / `valOracle` interpolants on the nonzero
  domain, with `*_eval` recovering the stored table at each `K`-node
- `holographicEval_at_nodes` — the snarkVM identity
  `M(a,b)=∑_k val(k) L^R_row(k)(a) L^C_col(k)(b)` at domain nodes
- `assert_axioms` / `assert_computable` elaborator; TrustBoundary is
  now a build-time census rather than `#print axioms`

Column reindexing of the public-input subdomain
(`reindex_by_subdomain`) is named for the batching layer.

**Exit criterion (met).** Oracle evaluation recovers entries; census
commands reject `sorryAx`.

### Iteration 3 — AHP PIOPs (complete)

**Goal.** The three interactive checks as polynomial identities, targeting
`VarunaVersion.V2` (single-circuit identities; batch selectors are
iteration 6).

**Delivered.**

- `Varuna.SNARKMode` / `maskPoly` — ZK masking parameterized (`mask = 0`
  for NonZK)
- `inspectResidual` — Ironwood-style SZ extractor: accepting + no break
  data implies the residual is identically zero
- rowcheck: `rowcheckResidual`, honest quotient, `rowcheck_on_domain`
  (Hadamard on `H`), `rowcheck_extract`
- univariate / lineval: `honestUnivariate`, `univariate_sum` (`∑ f = |K| σ`),
  `assignmentPoly` / `linevalPoly`, `univariate_extract`
- matrix / rational: `matrixAPoly` / `matrixBPoly` matching snarkVM
  `a(X)`, `b(X)`; `matrix_on_domain` / `matrix_rational`;
  `matrix_extract`
- `AHPVerifierChecks.accepts` — the three `LC_WITH_ZERO_EVAL` names

**Exit criterion (met).** Each identity, at a challenge outside a computed
bad set (or with `inspectResidual = none`), implies the corresponding
matrix/witness claim; completeness is a sibling theorem; no `sorry`.

### Iteration 4 — Polynomial commitment (complete)

**Goal.** Sonic PC as used by snarkVM (`polycommit/sonic_pc`).

**Delivered.**

- `LabeledPolynomial` / `PolynomialInfo` with degree and hiding bounds
- `LCTerm` / `LinearCombination` matching snarkVM, including
  `lcWithZeroEval` / `isZeroEval`
- abstract bilinear `Pairing` and KZG `kzgCheck`
  (`e(C − v g, h) = e(w, βh − z h)`)
- `kzgCheck_honest` — completeness for `C = p(β)·g` on a well-formed SRS
- `inspectBinding` / `pairingBreak_of_double_opening` — two distinct
  openings of one commitment yield a pairing-product identity with
  nonzero scalar (PC forgery ⇒ pairing-break *structure*)
- `kzgCheck_batch` — bilinearity of a two-claim `ξ`-combination

BLS12-377 remains a later concrete pin. Hardness of the pairing break
is a floor.

**Exit criterion (met).** Binding is a computed `def`; completeness and
the forgery reduction are sorry-free; census extended.

### Iteration 5 — Fiat–Shamir and the deployed transcript (complete)

**Goal.** The V2 absorb/squeeze schedule, with forks and collisions as
computed data.

**Delivered.**

- `VarunaVersion` (`V1` / `V2`); the formalization targets `V2`
- `FSMessage` / `Transcript` / `RO` — Poseidon identified with a
  programmable random oracle is a floor
- `squeezeN` — successive squeezes re-absorb the previous challenge
- `V2Challenge` / `V2Transcript` — absorb then squeeze: combiners, `α`
  only, extra `prepareThird` (`η_b, η_c` delayed), `β`, `δ`, `γ`
- `challenge_eq_ro` / `alpha_prefix_isPrefix` — each challenge is a
  function of the prefix *before* that squeeze; `α` is a prefix of
  prepare-third and of `β`
- `inspectFork` — two oracles that disagree at a shared prefix
  (programming / rewind); `inspectCollision` — two prefixes, one RO
- `hasPrepareThird_V2` / `v2_secondRound_lt_v1` — V2 has the extra
  round and squeezes one second-round challenge instead of three

Forking as a *probabilistic* special-soundness extractor (rewinding
an adversary) remains iteration 8. Here the break data is computed.

**Exit criterion (met).** V2 schedule in Lean; a message is in the
prefix before its challenge; forks/collisions are `def`s; no `sorry`.

### Iteration 6 — Batching (complete)

**Goal.** Multi-circuit / multi-instance batching, with the extra IOP
round that prevents adaptive statement selection after seeing verifier
randomness. Soundness must not silently assume a single circuit.

Sage does not implement batching; the source of truth here is
snarkVM plus the spec.

**Delivered.**

- `BatchCombiners` / `circuitCombiners` / `instanceCombiners` — first
  combiner of each family is `1` (not squeezed), matching snarkVM
  `sample_batch_combiners`
- `MatrixCombiners.ofEtaBC` / `DeltaCombiners.first` — `η_A = 1`,
  first-circuit `δ_A = 1`
- `weightedSum` / `inspectBatch` — accepting combination with no break
  data implies every claim is zero
- `selectorPoly` / `selector_mul_vanishing` / `lift_residual` —
  snarkVM `s = (v_H / v_{H_i}) · (|H_i|/|H|)` when `|H_i|` divides
  `|H|`; times `v_{H_i}` this is `(|H_i|/|H|) v_H`. A subdomain
  residual lifts with that scale (the unscaled geometric quotient
  is `selectorGeom`)
- `batched_rowcheck_two` — honest two-circuit rowcheck combination
  with the snarkVM scale on each selector
- extra round: `alpha_independent_of_prepareThird` (`α` ignores later
  instance sums) and `prepareThird_challenge_eq` (`η_b, η_c` see those
  sums)

**Exit criterion (met).** Batching identities and the extra-round
binding are sorry-free; `inspectBatch` is a computed `def`.

### Iteration 7 — Deployed-verifier faithfulness (complete)

**Goal.** Ironwood’s fingerprint pattern: a Lean model of the assembled
accept predicate, named floors, and negative fixtures.

**Delivered.**

- `ModellingFloor` / `modellingFloors` — Poseidon = RO, pairing
  hardness, SRS, encodings, index = circuit (out of Lean, not axioms)
- `typedAHPAccepts` / `TypedProof.accepts` — the three zero-eval LCs
  plus a batch combination, as a Boolean predicate agreeing with the
  `Prop` accept
- `lcNames_match_snarkVM` — `matrix_sumcheck`, `lineval_sumcheck`,
  `rowcheck_zerocheck`
- toy-field fixtures on `ZMod 17`, kernel-checked with `decide` (not
  `native_decide`, so the census stays `propext` / `choice` / `Quot.sound`)
- negative fixtures: flipping any LC evaluation rejects; a lucky
  `𝔽₁₇` combination `1·3+2·7=0` is a batch break; a binding break at
  a repeated point
- `toyMulPairing` / `toy_kzg_accepts` — the KZG pairing equation on a
  multiplicative toy pairing
- `SpotCheck.lean` — source-pinned samples against the `snarkVM/`
  submodule (`Varuna.snarkVMPin`): V2 squeeze counts, first combiners
  `= 1`, `η_A = 1`, vanishing `X^n-1`, padding at `ω^0 = 1`,
  selector point-eval matching `evaluate_selector_polynomial`,
  four-term matrix `b` LC, KZG pairing equation. This is **not**
  Ironwood’s MSM/`native_decide` fingerprint of a BLS12-377 proof.

A captured snarkVM proof followed later (`Fingerprint.lean`, below);
captured Sage proofs remain future pins.
Byte encodings stay a floor. The selector scale `|H_i|/|H|` was a
real mismatch found by sampling `ahp/selectors.rs`; Lean now matches
the deployed formula.

**Exit criterion (met).** Typed accept in Lean; floors enumerated;
negative fixtures reject; no `sorry`; census unchanged in axioms.

### Iteration 8 — Knowledge-soundness capstone (complete)

**Goal.** Compose iterations 3–7 into a single advertised endpoint.

**Delivered.**

- `SoundnessBreak` — residual / batch / fork / collision data
- `inspectAHP` — the three residual inspectors, in order
- `ProofView` / `ProofView.inspect` — algebraic V2 transcript plus
  batch claims
- `knowledgeSoundness` — if the three LCs accept, the batch sum is
  zero, inspection returns no break, and the univariate degree bound
  holds, then Hadamard holds on `H`, the lineval sum identity holds
  on `Vd`, the matrix identity holds on `K`, and every batch claim
  is zero
- `inspectBinding_none_same_point` — two openings of one commitment
  at the same point with no binding break have equal values
- floors stay explicit (`knowledgeSoundness_rests_on_floors`)

This is the *algebraic* capstone at a generic field. Computational
rewinding of an FS adversary (probability `d/|F|`) and the BLS12-377
scalar-field pin remain named gaps: `goodChal` on the proof map, and
the five modelling floors. Zero-knowledge (simulator) is a twin
concern, not on this spine.

**Exit criterion (met).** Named endpoint in `TrustBoundary`; sorry-free;
breaks are `def`s; floors are not axioms.

### Security-analysis follow-up (complete)

**Goal.** Close the gaps [security-analysis.md](book/src/formal-verification/security-analysis.md)
found, except categories Ironwood also assumes (hash = RO, algebraic
adversary, hardness, byte encodings) or does not claim (zero knowledge).

**Delivered.**

- `Lineval.lean`: the faithful V2 lineval polynomial `s + Σ η_M M̂(α, X) ẑ`
  and `Σ_C M̂(α, c) ẑ(c) = LDE(Mz)(α)`
- `MatrixSumcheck.lean`: subgroup Lagrange closed form off the domain;
  the matrix sumcheck proves `|K| σ = M̂(α, β)`
- `Composition.lean`: `v2_chain` gives `(Az + e) ∘ Bz = Cz` with `e` the
  mask sum; `shifted_witness_accepts` shows the unchecked mask sum is
  exploitable in ZK mode (confirmed against the pinned snarkVM);
  `v2_chain_nonZK` gives the R1CS rows
- `Bridge.lean`: `Int` residues ↔ `ZMod p`; `satisfies_of_rows`
- `Selectors.lean`: selectors are indicators on `H`; batched zerocheck
  and sumcheck soundness
- `Algebraic.lean`, `OpeningBatch.lean`: KZG evaluation soundness,
  degree bounds, and batched openings under an algebraic adversary, as
  computed trapdoor breaks; new floor `algebraicAdversary`
- `Probability.lean`, `FSBound.lean`: bad-challenge counts over any
  finite challenge set, the adaptive union bound, and Fiat–Shamir query
  charging (`Q · b / |S|`)
- `Statement.lean`, `PublicInput.lean`: `init_sponge` binds the public
  inputs; `reindex_by_subdomain` and `ẑ = x̂` on the input subdomain
- `ProofSize.lean`: proof element counts from snarkVM's `Proof`

**Delivered in a second pass** (listed as not done after the first):

- `Degree.lean`: residual degrees from degree bounds on the prover's
  polynomials; `ahp_error_concrete` is `ahp_error` with them plugged in
- `Endpoint.lean`: `V2Endpoint.sound` composes the `h₀` opening reduction
  (`value_correct_of_inspect_none`), the three matrix sumchecks
  (`matrix_sumcheck_value`), and `v2_chain` into one theorem;
  `sound_nonZK` ends at `satisfies`
- `Fingerprint.lean`: one honest snarkVM V2 hiding-mode proof, captured on
  the prover side with test-only instrumentation (`fixtures/fingerprint/`,
  with provenance). Kernel `decide` over `ZMod q` checks that every
  coefficient snarkVM assembles for the three zero-eval LCs is Lean's
  formula, that each LC vanishes, and that the scalar forms are the model's
  definitions. It also pins `row(γ) col(γ) ≠ row_col(γ)`: the Lean
  `matrixBPoly` and the deployed `b` agree only on `K`

**Still open.** The endpoint takes the other openings (`ẑ`, `h₁`, `g₁`,
matrix witnesses) as evaluations of the committed polynomials, and the
matrix residuals as identities (the `γ` step is `matrix_extract`); each
reduces like `h₀`. It uses one `K` for all matrices; the selector-batched
matrix sumcheck (`batchedSumcheck_extract`) is not composed in. The
fingerprint covers the zero-eval LC layer, not the MSM / pairing assembly.

---

## 5. Proof-map discipline

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

A node moves to `proven` only when its `anchor` field names a real
declaration. Iteration 0 sets `mulConstraint`, `r1csEmpty`, and
`hadamardIff` to `proven`, and leaves the rest of the spine as
`object` / `hyp` / `floor` / `goal`.

A later `book/validate-proof-journey.py` (Ironwood has one) should
check that every `proven` anchor exists in the Lean sources and that
every edge’s `via` is a real name. Not written yet.

---

## 6. Sources, pins, and correspondence

Pin sources by commit, not by branch, once iteration 2 starts
quoting them.

| Source | Use |
| --- | --- |
| `ProvableHQ/varuna-sage-impl` `docs/spec.pdf` | Human protocol spec |
| `ProvableHQ/varuna-sage-impl` Sage PIOPs | Executable identities for rowcheck / sumchecks |
| `ProvableHQ/protocol-docs` (`protocol-docs/` submodule) | Algorithm identities (rowcheck, lincheck, matrix sumcheck), including VarunaVersion V2 batching |
| `ProvableHQ/snarkVM` submodule (`Varuna.snarkVMPin`) `algorithms/src/snark/varuna/` | Deployed AHP, FS, PC, batching (target: `VarunaVersion.V2`); sampled in `SpotCheck.lean` |
| `ProvableHQ/snarkVM` `algorithms/src/polycommit/sonic_pc/` and `kzg10/` | PC interface and pairing check |
| `leanprover-community/mathlib4` tag `v4.33.0` | Field, `Polynomial`, roots of unity, Lagrange |
| Sage / snarkVM test vectors | Iteration-7 fixtures |

The Sage implementation is single-circuit R1CS with ZK and without
batching or lookups. Lean should not treat Sage as the deployed
system: it is the readable PIOP, snarkVM is the verifier of record.

---

## 7. Build, CI, and documentation scope

- `lake build --wfail` is the verifier. CI runs it
  (`.github/workflows/lean.yml`) and fetches the Mathlib cache.
- Mathlib is pinned at tag `v4.33.0` (toolchain `v4.33.0`).
- `assert_axioms` / `assert_computable` in `Varuna/AxiomCheck.lean`
  bound the census; `sorryAx` fails the build.
- We are **not** cloning the Ironwood book (mdBook, proof journey,
  glossary, CI-checks essay). The proof map plus this plan plus a
  short README are the documentation for now.

---

## 8. Suggested PR sequence

1. **This PR** — relation + first lemmas + proof map + plan.
2. **Finish iteration 0** — sparse ↔ Hadamard iff, formatted inputs.
3. **Mathlib + domains + SZ.**
4. **Indexer holography.**
5. **AHP rowcheck**, then lincheck, then matrix sumcheck (V2).
6. **PC binding** as a computed break.
7. **Fiat–Shamir schedule** for `VarunaVersion.V2` + extra batching round.
8. **snarkVM fixtures** (faithfulness).
9. **Knowledge-soundness capstone** + full census.

---

## 9. What you are trusting after iteration 0

The Lean kernel has checked that

- `satisfies []` is true
- a multiplication constraint is exactly multiplication
- the empty Hadamard system holds
- sparse constraints are `Az ∘ Bz = Cz` for the dense matrices they
  encode (duplicate columns add; missing columns are zero), once
  variable indices are in range and the assignment is formatted
- formatted public inputs prepend the constant-`1` slot and are
  admissible iff their length is a power of two
- one toy assignment satisfies one constraint, including in the
  formatted view

It has **not** checked Varuna, Marlin, the AHP, the PC, Fiat–Shamir,
or the Rust verifier. The proof map is there so that sentence stays
true in public as the green region grows.
