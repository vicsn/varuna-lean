# Security analysis

This is the record of the Varuna verification: what is in scope, the conventions, the soundness spine, and how each item of the security-analysis plan is covered. The interactive picture is [`proof-map.html`](proof-map.html). Lean links below are relative to the repository root. snarkVM paths refer to the pinned `snarkVM/` submodule (`Varuna.snarkVMPin`). The spec is `protocol-docs/snark/varuna/varuna-spec-prod.tex`.

The development follows [zcash/ironwood](https://github.com/zcash/ironwood): a layered Lean development over Mathlib, a proof map that shows the theorem graph and its remaining holes, and a trust-boundary census so the trusted base is a build-time property.

**Status**, for the item-by-item sections below. **Lean**: kernel-checked here. **Partial**: Lean checks the core; a composed or concrete statement is missing. **Spec**: argued in the spec only. **Excluded**: a category Ironwood also assumes or does not claim (hash = random oracle, algebraic adversary, hardness, byte encodings); named as a floor where it is an assumption. Zero knowledge of the AHP simulator and of one hiding opening is now Lean; see §5.

## What is being verified

**Target.** Knowledge soundness of the deployed Varuna verifier, the object in snarkVM that validators run, `VarunaVersion.V3`. Completeness of the individual checks is proved alongside soundness. The AHP simulator ([`ZK.lean`](../../../Varuna/ZK.lean)) programs the one opening outside the domain and absorbs the witness into the ZK mask. A constant blinding shifts the hiding commitment along `gamma_g`, and a fresh algebraic opening is a trapdoor break or the represented value ([`simulation_extractable`](../../../Varuna/ZK.lean#L154)). Pairing independence of `g` and `gamma_g` stays a hypothesis of that binding.

Varuna is an optimized Marlin ([CHMMVW19](https://eprint.iacr.org/2019/1047)) AHP, compiled through a Sonic-style polynomial commitment and made non-interactive with Fiat–Shamir. The formalization targets snarkVM’s `VarunaVersion.V3` and names:

- universal, updatable SRS
- holographic indexer (row / col / val oracles for $A, B, C$)
- three PIOPs: rowcheck, univariate (lincheck) sumcheck, rational (matrix) sumcheck — snarkVM’s linear combinations `rowcheck_zerocheck`, `lineval_sumcheck`, `matrix_sumcheck`
- Sonic PC openings on BLS12-377
- multi-circuit / multi-instance batching, including the extra IOP round added in 2025 to stop adaptive statement selection
- optional zero-knowledge (masking polynomials)

The constraint language is R1CS ($Az \circ Bz = Cz$). If the V3 verifier accepts, then under the named assumptions there is a witness satisfying the R1CS. [`v3_chain`](../../../Varuna/Composition.lean#L173) gives that relation on $R$, in either mode, with the mask sum equal to zero.

**Separate projects.**

| Concern | Where it lives |
| --- | --- |
| snarkVM gadget ↔ spec correctness | ACL2 AleoVM circuits; `aleovm-circuits-lean` |
| Aleo instructions / Leo compilation | ACL2 language books; future verifying compiler |
| AleoBFT consensus | `aleobft-formal` (ACL2) |
| Pairing / curve arithmetic as a library | Mathlib + a future CompElliptic-style pin |

The R1CS means what the circuit says. Whether that circuit is what a Leo programmer intended is the gadget and compiler work above.

## Conventions

Ironwood’s [formal-verification page](https://zcash.github.io/ironwood/formal-verification.html) is the style guide.

**Breaks as computed data.** A theorem `soundness ∨ ∃-break` is vacuous in a prime-order group (nontrivial discrete-log relations always exist) and for compressing hashes (collisions always exist). Every reduction is a plain `def` that returns the breaking data, with `Prop` certificates attached. For Varuna the breaks are a Schwartz–Zippel root, a polynomial-commitment binding break (two openings of one commitment), a discrete-log / pairing-assumption break extracted from a Sonic-PC forgery, and a random-oracle collision or programming miss. Extractors are `def`s, and `noncomputable` is kept off that path. `inspectResidual` is the exception: it is noncomputable because it inspects Mathlib polynomials.

**Trust discipline.** General theorems rest only on `propext`, `Classical.choice`, and `Quot.sound`. Concrete closed facts may use `native_decide`, and that extension of the trusted base is named on the census. [`TrustBoundary.lean`](../../../Varuna/TrustBoundary.lean) is the census. `assert_axioms` / `assert_computable` in [`AxiomCheck.lean`](../../../Varuna/AxiomCheck.lean) make it a build-time property. CI fails on `sorry` via `lake build --wfail`. Toy-field samples in `Match.lean` / `SpotCheck.lean`, and the captured proof in `Fingerprint.lean`, use kernel `decide`, so the census stays those three axioms. The group-level MSM / pairing assembly is not captured.

**Floors are identifications, not axioms.** Hash-as-RO, pairing-as-hardness, “the verifying key is the index of the real circuit”, and byte-level encodings are floors on the proof map. They do not appear as Lean `axiom`s. A reader of a capstone theorem can see them as explicit hypotheses or as out-of-Lean identification steps ([`knowledgeSoundness_rests_on_floors`](../../../Varuna/Soundness.lean)).

## The soundness spine

Ironwood’s spine is accepting proof → verifier equation → IPA tree → opening → `SnarkRelation`. Varuna’s spine, reading the Sage verifier and `snarkVM/.../varuna/ahp/ahp.rs`, is:

```
accepting proof
  → Fiat–Shamir challenges          (schedule proved; Poseidon = RO is a floor)
  → Sonic-PC openings               (h₀ reduction proved; pairing hardness is a floor)
  → AHP linear combinations evaluate to zero
      rowcheck_zerocheck
      lineval_sumcheck
      matrix_sumcheck
  → Az ∘ Bz = Cz
  → R1CS witness
```

[`V3Endpoint.sound`](../../../Varuna/Endpoint.lean) is the composed theorem: a no-break opening of the rowcheck quotient $h_0$, the three matrix sumchecks, and [`v3_chain`](../../../Varuna/Composition.lean#L173) give a zero mask sum and $Az \circ Bz = Cz$ on $R$. [`sound_r1cs`](../../../Varuna/Endpoint.lean) ends at `satisfies`. How the openings, the $\delta$ batch, and the selector sumcheck enter that composition is §2.3. What stays outside it is [below](#what-remains).

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
  Az ∘ Bz = Cz                       (proved)
           │
           ▼
  R1CS witness                       (proved)
```

## Proof-map statuses

Copied from Ironwood’s proof map. Edge verbs:

- **entails** — B follows from A (and any other incoming arrows)
- **discharges** — A proves away hypothesis B
- **rests on** — B is an assumption A still needs (an in-Lean hypothesis or an out-of-Lean floor)

| Status | Meaning |
| --- | --- |
| `proven` | A named Lean theorem exists; `lake build` checks it |
| `hyp` | In-Lean hypothesis, or a lemma stated but not proved |
| `floor` | Modelling identification, not a Lean axiom |
| `object` | A definition (data or `Prop`), not a theorem |
| `goal` | Advertised capstone |

A node is `proven` only when its `anchor` field names a real declaration. `book/validate-proof-journey.py` checks that every `proven` anchor, and every edge `via`, names a declaration in `Varuna/`. `maskSum` is `v3_chain`: the mask sum is zero.

## Layers

Sorry-free. `lake build --wfail` is the verifier. The item sections below say what each security-analysis question concludes. This is the file-level inventory those sections draw on.

**R1CS** (`PrimeField.lean`, `R1CS.lean`). Sparse constraints and the Hadamard predicate agree ([`satisfies_iff_hadamard`](../../../Varuna/R1CS.lean#L464)). A multiplication constraint is multiplication ([`mulConstraint_holds_iff`](../../../Varuna/R1CS.lean#L161)). Formatted public inputs prepend the constant-$1$ slot and are admissible iff their length is a power of two ([`formattedPublicInputAdmissible_isPowerOfTwo`](../../../Varuna/Domain.lean#L55)). The toy instance $3 \cdot 5 = 15$ holds over $\mathbb F_{17}$ ([`toy_mul_holds`](../../../Varuna/R1CS.lean#L576)).

**Field, domains, vanishing** (`Field.lean`, `Domain.lean`, `Bridge.lean`). Mathlib `ZMod p` at `v4.33.0`. A multiplicative subgroup of size $2^k$, with $v_H(X) = X^{|H|} - 1$ and $v_H(\alpha) = 0 \leftrightarrow \alpha \in H$, a Lagrange basis, and Schwartz–Zippel ([`schwartzZippel_card`](../../../Varuna/Domain.lean), [`szBadSet`](../../../Varuna/Domain.lean)). The R1CS relation stays on integer residues; [`satisfies_iff_zmod`](../../../Varuna/Bridge.lean#L64) and [`satisfies_of_rows`](../../../Varuna/Bridge.lean#L96) send them to `ZMod p`.

**Indexer** (`Indexer.lean`). Row, column, and value interpolants recover sparse entries on the nonzero domain ([`rowOracle_eval`](../../../Varuna/Indexer.lean#L116) and its siblings). [`holographicEval_at_nodes`](../../../Varuna/Indexer.lean#L85) is the snarkVM identity $M(a,b) = \sum_k \mathrm{val}(k)\, L^R_{\mathrm{row}(k)}(a)\, L^C_{\mathrm{col}(k)}(b)$ at domain nodes.

**AHP, polynomial commitment, Fiat–Shamir, batching.** The three checks, their error, and the batching extractors are §1. Sonic-PC binding, degree bounds, hiding, and simulation extractability are §2.4. The V3 absorb-then-squeeze schedule, including [`prepareThirdEtaSqueeze .V3 = 3`](../../../Varuna/Batching.lean#L386) and the domain separator `VARUNA-2026-V3` ([`v3Init`](../../../Varuna/Statement.lean#L50)), is §3. Forks and collisions are `def`s (`inspectFork`, `inspectCollision`). The first combiner of each family is $1$. [`reindexBySubdomain`](../../../Varuna/PublicInput.lean#L34) and $\hat z = \hat x$ on the input subdomain are below, with the other facts the numbered items do not ask for.

**Faithfulness and the capstone.** [`TypedProof.accepts`](../../../Varuna/Match.lean) agrees with the `Prop` accept. Toy-field fixtures accept honest zeros and reject flipped evaluations. The V3 composition (`V3Endpoint.sound`, `sound_of_openings`, `sound_of_combined_matrix`, `matrix_sumcheck_of_selector`, `sound_r1cs`) and the Marlin-shaped [`knowledgeSoundness`](../../../Varuna/Soundness.lean) are §2. [`knowledgeSoundness_bls`](../../../Varuna/Soundness.lean#L245) restates that statement at `ZMod bls12_377_r`. The fingerprint and the source samples are the Lean-vs-snarkVM item below.

## 1. Soundness of the AHP

### 1.1 The soundness notion S1 that step 2 needs (Lean)

S1 should be round-by-round knowledge soundness, because step 3 then costs $Q \cdot \varepsilon_{\text{round}}$. Each Varuna check is a polynomial identity at a fresh challenge, so the RBR doomed state is "some residual is nonzero", and the bad challenges are its roots. Lean provides this per check as computed data: [`inspectResidual`](../../../Varuna/AHP.lean#L57), [`inspectResidual_accepts`](../../../Varuna/AHP.lean#L69), and the three extractors [`rowcheck_extract`](../../../Varuna/AHP.lean#L156), [`univariate_extract`](../../../Varuna/AHP.lean#L273), [`matrix_extract`](../../../Varuna/AHP.lean#L380). [`ahp_error`](../../../Varuna/Probability.lean#L243) gives the adaptive union bound across $\alpha, \beta, \gamma$.

### 1.2 S1 error of the unbatched AHP, including ZK (Lean)

The spec (lines 444–452) gives $\frac{2|R|}{|\mathbb F\setminus R|} + \frac{2|C|}{|\mathbb F\setminus C|} + \frac{3|K|}{|\mathbb F|}$.

Lean proves the shape of the bound over any finite challenge set $S$:

- [`card_filter_inspectResidual_le`](../../../Varuna/Probability.lean#L41): a residual of degree $d$ has at most $d$ bad challenges in $S$.
- [`ahp_error`](../../../Varuna/Probability.lean#L243): an adaptive prover breaks on at most $(d_R + d_L + d_M)\,|S|^2$ of the $|S|^3$ triples.

- [`ahp_error_concrete`](../../../Varuna/Degree.lean#L70): the same bound with the residual degrees computed from degree bounds on the prover's polynomials, by [`natDegree_rowcheckResidual_le`](../../../Varuna/Degree.lean#L30), [`natDegree_univariateResidual_le`](../../../Varuna/Degree.lean#L43), and [`natDegree_matrixResidual_le`](../../../Varuna/Degree.lean#L55). For example, the rowcheck residual has degree at most $\max(\deg z_A + \deg z_B,\ \deg z_C,\ \deg h_0 + |R|)$.

$S$ is where snarkVM's 252-bit AHP challenges enter (`crypto_hash/poseidon.rs:473-476`). Masked witnesses are covered, since the residuals are over arbitrary polynomials. ZK enters through the input bounds, which carry the query bound $b$ (e.g. `deg h_0 ≤ 2|R| + 2b − 2`, `second.rs:66`). The combiner terms are 1.3.

### 1.3 S1 error of each AHP batching step (Lean)

- **Selectors are indicators of $H_i$ on $H$:** [`selectorPoly_eval_indicator`](../../../Varuna/Selectors.lean#L59).
- **Batched zerocheck:** [`batchedZerocheck_extract`](../../../Varuna/Selectors.lean#L94). A batched rowcheck that is a multiple of $v_H$ gives each circuit's rowcheck on its own domain, or a lucky combination on $H$ as a whole: one that vanishes at every point of $H$ while some claim is live ([`inspectBatchOn`](../../../Varuna/Batching.lean#L189)). No lucky combination at any single point implies the hypothesis ([`inspectBatchOn_eq_none_of_pointwise`](../../../Varuna/Batching.lean#L215)).
- **Batched sumchecks:** [`batchedSumcheck_extract`](../../../Varuna/Selectors.lean#L163) and [`sum_selectorPoly_mul`](../../../Varuna/Selectors.lean#L123). This covers lineval ($\mu, \rho$) and matrix ($\delta$) batching: per-circuit sums, or a lucky combination.
- **Cost of a lucky combination:** snarkVM draws a round's weights one squeezed element at a time: the instance combiners $\tau_{i,j}$ and then the circuit combiner $\nu_i$ of each circuit (`sample_batch_combiners`, `verifier.rs:50-76`), the $\eta$s (`verifier.rs:193-208`), and the $\delta$s (`verifier.rs:241-246`). Each weight is a product of distinct drawn elements, so the combination of claims is affine in each element with the others fixed ([`coordAffine_scheme`](../../../Varuna/Combiners.lean#L219)). Call a prefix of drawn elements live if some completion leaves the combination nonzero somewhere on the domain. At most one next element ends liveness ([`WeightDraw.card_bad_le_one`](../../../Varuna/Combiners.lean#L82)), and a combination that is lucky on the whole domain passes such a step ([`WeightDraw.exists_bad_of_lucky`](../../../Varuna/Combiners.lean#L110)). Over $k$ drawn elements, at most $k\,|S|^{k-1}$ of the $|S|^k$ draws are lucky, i.e. $k/|S|$ ([`WeightDraw.card_lucky_le`](../../../Varuna/Combiners.lean#L132)). A live claim makes the empty prefix live when no two weights are the same monomial ([`exists_weightedSum_scheme_ne_zero`](../../../Varuna/Combiners.lean#L266)), so this covers `inspectBatchOn` and `inspectBatch` ([`card_filter_inspectBatchOn_scheme_le`](../../../Varuna/Combiners.lean#L329), [`card_filter_inspectBatch_scheme_le`](../../../Varuna/Combiners.lean#L342)). The weight schemes are snarkVM's: [`combinerScheme`](../../../Varuna/Combiners.lean#L523) is $\nu_i \tau_{i,j}$ in squeeze order (for two circuits of two instances, $1, \tau_{0,1}, \nu_1, \tau_{1,1}\nu_1$: [`schemeWeights_combinerScheme_two_two`](../../../Varuna/Combiners.lean#L538)), [`prepareThirdScheme`](../../../Varuna/Combiners.lean#L575) is $\nu_i \tau_{i,j} \eta_M$, and [`deltaScheme`](../../../Varuna/Combiners.lean#L585) is the $\delta$s; [`combinerScheme_valid`](../../../Varuna/Combiners.lean#L566) shows no two instances share a weight. For the batched rowcheck this is [`card_filter_batchedZerocheck_combiners_le`](../../../Varuna/Combiners.lean#L646): all of $R$ costs what one point costs, where counting point by point would multiply by $|R|$. Two claims with weights $[1, \eta]$ are the case $k = 1$, at most one bad $\eta$ ([`card_filter_inspectBatch_pair`](../../../Varuna/Probability.lean#L68), [`card_filter_inspectBatchOn_pair`](../../../Varuna/Probability.lean#L90)).
- **Prepare-third round:** [`alpha_independent_of_prepareThird`](../../../Varuna/Batching.lean#L405) and [`prepareThird_challenge_eq`](../../../Varuna/Batching.lean#L413). $\alpha$ is squeezed before that round; $\eta_A, \eta_B, \eta_C$ are squeezed there ([`prepareThirdEtaSqueeze_V3`](../../../Varuna/Batching.lean#L386)).

### 1.4 Assumptions underpinning S1 (Lean)

S1 is information-theoretic and does not need the AGM. Every theorem here is `assert_axioms`-bounded to `propext`, `Classical.choice`, `Quot.sound` ([`TrustBoundary.lean`](../../../Varuna/TrustBoundary.lean)). S1's remaining hypotheses are visible in the statements: primitive roots ([`EvalDomain`](../../../Varuna/Domain.lean#L69)) and degree bounds (`hdeg`), which the PC enforces (2.4).

## 2. Soundness of AHP + PCS compilation

### 2.1 The primitive P (Lean; algebraic projection)

P is Marlin's public-coin preprocessing argument of knowledge. [`PreprocessingAHP`](../../../Varuna/Soundness.lean#L216) is that interaction: a list of rounds, each an absorbed message and a squeezed challenge, plus [`ProofView`](../../../Varuna/Soundness.lean#L91), the polynomials read off those rounds. [`PreprocessingAHP.sound`](../../../Varuna/Soundness.lean#L224) requires $\alpha$, $\beta$, and $\gamma$ to be challenges of the rounds and applies [`knowledgeSoundness`](../../../Varuna/Soundness.lean#L184). Group elements still come with SRS representations ([`represent`](../../../Varuna/Algebraic.lean#L102)); the object does not carry group elements itself.

### 2.2 The property S2 that step 3 needs (Lean)

S2 is RBR knowledge soundness, charged per oracle query. [`fs_query_charge`](../../../Varuna/FSBound.lean#L51): with at most $b$ bad answers per query, at most $Q\,b\,|S|^{Q-1}$ of $|S|^Q$ lazy-oracle tapes let a deterministic adversary hit one. A squeeze of several elements is several queries, each on the prefix extended by the elements already squeezed, as `squeezeN` does ([`squeezeN_before_getElem`](../../../Varuna/FSBound.lean#L103), [`elemBefore`](../../../Varuna/FSBound.lean#L83)). [`fs_break_count`](../../../Varuna/FSBound.lean#L125): an output with a break at any squeezed element is such a hit, if every element was answered on one of its queries ([`OutputFromQueries`](../../../Varuna/FSBound.lean#L117)). [`squeezeBad`](../../../Varuna/FSBound.lean#L310) is the bad set of each element: Schwartz–Zippel roots at $\alpha$, $\beta$, $\gamma$, and at the combiner squeezes the elements that end liveness of that squeeze's weight draw (§1.3), at most one each. The first combiners weight the batched rowcheck on all of $R$ ([`rowcheckDraw`](../../../Varuna/Combiners.lean#L622)). [`fs_v2_squeeze_charge`](../../../Varuna/FSBound.lean#L358) puts those sets on the query prefixes ([`prefixBad`](../../../Varuna/FSBound.lean#L259)) and charges the resulting break count. Squeezed elements enter a prefix as `field` messages, so a query prefix names one squeeze element if no prover message is a lone `field` ([`elemBefore_inj`](../../../Varuna/FSBound.lean#L177)). Under that condition, a lucky draw in the output is a break ([`outputBreaks_of_lucky`](../../../Varuna/FSBound.lean#L288)); for the rowcheck that is the lucky event of `batchedZerocheck_extract` on snarkVM's weights ([`outputBreaks_of_rowcheck_lucky`](../../../Varuna/FSBound.lean#L376)). Poseidon = RO stays a floor.

### 2.3 Compilation yields S2 from S1 (Lean)

Under the algebraic restriction, every PC step either gives the polynomial fact S1 uses or a computed trapdoor break:

- an accepted opening with a wrong value: [`inspectOpening_break`](../../../Varuna/Algebraic.lean#L182)
- a violated degree bound: [`inspectDegree_break`](../../../Varuna/Algebraic.lean#L304)
- a batched opening: [`batchedOpening_extract`](../../../Varuna/OpeningBatch.lean#L61) per point, [`acrossPoints_extract`](../../../Varuna/OpeningBatch.lean#L90) across points

[`V3Endpoint.sound`](../../../Varuna/Endpoint.lean#L221) composes the opening reduction with the AHP. A no-break opening of the rowcheck quotient $h_0$ ([`value_correct_of_inspect_none`](../../../Varuna/Algebraic.lean#L207)), the three matrix sumchecks with their degree bounds ([`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L185)), and [`v3_chain`](../../../Varuna/Composition.lean#L173) give a zero mask sum and $Az \circ Bz = Cz$ on $R$. Each matrix has its own nonzero domain. The $\gamma$ check is `matrixEval` $= 0$ plus [`inspectResidual`](../../../Varuna/AHP.lean#L57), which [`inspectResidual_accepts`](../../../Varuna/AHP.lean#L69) turns into the residual identity [`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L185) consumes. [`sound_of_openings`](../../../Varuna/Endpoint.lean#L301) does the same for $\hat z$, $h_1$, $g_1$, and the three matrix witnesses: a no-break opening plus the scalar check the verifier runs is the polynomial check. [`sound_of_combined_matrix`](../../../Varuna/Endpoint.lean#L377) replaces the three $\gamma$ checks by one $\delta$-combination ([`inspectBatch_accepts`](../../../Varuna/Batching.lean#L177)). [`matrix_sumcheck_of_selector`](../../../Varuna/Endpoint.lean#L429) turns a selector-batched sum on a common domain ([`batchedSumcheck_extract`](../../../Varuna/Selectors.lean#L163)) into $|K|\sigma = \hat M(\alpha,\beta)$ via [`matrix_sumcheck_value_of_sum`](../../../Varuna/MatrixSumcheck.lean#L152). [`knowledgeSoundness_bls`](../../../Varuna/Soundness.lean#L245) restates the Marlin capstone at `ZMod bls12_377_r`. That `bls12_377_r` is prime is a `Fact` hypothesis: trial division is not a practical kernel proof at this size. [`Fingerprint.q_eq_bls12_377_r`](../../../Varuna/Fingerprint.lean) shows the captured modulus is that number.

### 2.4 Properties of SonicPCS (Lean)

- **Extractability:** from the algebraic restriction, named as the floor `algebraicAdversary` ([`ModellingFloor`](../../../Varuna/Match.lean#L34)).
- **Evaluation binding:** [`inspectOpening_break`](../../../Varuna/Algebraic.lean#L182) and [`pairingBreak_of_double_opening`](../../../Varuna/SonicPC.lean#L354); hardness is the `pairingHardness` floor.
- **Degree bounds:** [`inspectDegree_break`](../../../Varuna/Algebraic.lean#L304). [`natDegree_X_mul_add_C_lt`](../../../Varuna/Algebraic.lean#L411) turns $\deg g_1 \le |C|-2$ (`third.rs:60`) into `hdeg`.
- **Hiding** (ZK only): [`kzgCheckHiding_honest`](../../../Varuna/SonicPC.lean#L464) is the snarkVM check `e(C − v g − random_v gamma_g, h) = e(w, βh − z h)`. A constant blinding is the shift `ρ · gamma_g` on top of the non-hiding commitment ([`commit_hiding_as_blind`](../../../Varuna/SonicPC.lean#L481), [`commit_blind_shift`](../../../Varuna/SonicPC.lean#L487)), and a nonzero `gamma_g` makes that scalar unique ([`commit_const_blind_injective`](../../../Varuna/SonicPC.lean#L494)). With pairing-independent generators, equal hiding commitments agree on both `p(β)` and `r(β)` ([`commit_hiding_binding`](../../../Varuna/SonicPC.lean#L512)). That independence is a hypothesis, not a proved hardness statement. The development does not treat the blinding coset as a uniform distribution.
- **Simulation extractability:** an accepted algebraic hiding opening is a trapdoor break or the represented value ([`hidingOpening_extract`](../../../Varuna/Algebraic.lean#L391)). The simulator's hiding opening of the masked lineval checks, and a fresh polynomial is extracted the same way ([`simulation_extractable`](../../../Varuna/ZK.lean#L154)). Padding still makes proofs non-unique (`varuna-padding.tex:256`), so this is not the unique-response property of [WM], and it is one opening rather than the whole SNARK.

### 2.5 Loss from batching SonicPCS openings (Lean)

Both levels reduce to a lucky combination: [`batchedOpening_extract`](../../../Varuna/OpeningBatch.lean#L61) and [`acrossPoints_extract`](../../../Varuna/OpeningBatch.lean#L90). With one free 168-bit challenge per combination (`sonic_pc/mod.rs:280, 373-414`), each costs at most $1/|S|$ ([`card_filter_linear_le_one`](../../../Varuna/Probability.lean#L59)), so the three points cost about $2^{-166}$. The randomizers are transcript-derived, so [`fs_query_charge`](../../../Varuna/FSBound.lean#L51) multiplies by $Q$: $Q = 2^{64}$ gives about $2^{-102}$. The target security level should be fixed together with $Q$.

## 3. Soundness of the Fiat–Shamir transform (Lean; Poseidon = RO excluded)

- **Schedule:** absorb then squeeze, with each challenge a function of the prefix before that squeeze ([`challenge_eq_ro`](../../../Varuna/FiatShamir.lean#L162)), and each further element of a squeeze a function of that prefix and the elements before it ([`squeezeN_before_getElem`](../../../Varuna/FSBound.lean#L103)). V3 squeezes $\alpha$ alone in the second round and $\eta_A, \eta_B, \eta_C$ in prepare-third ([`sample_v3_second_round_squeeze`](../../../Varuna/SpotCheck.lean#L72), [`sample_v3_prepareThird_eta_squeezes`](../../../Varuna/SpotCheck.lean#L67)).
- **Statement binding:** [`v3Init`](../../../Varuna/Statement.lean#L50) models `init_sponge` with domain separator `VARUNA-2026-V3`. [`v3Init_injective`](../../../Varuna/Statement.lean#L91): the initial transcript determines the public inputs and the commitments.
- **Query charging:** [`fs_query_charge`](../../../Varuna/FSBound.lean#L51).
- **Poseidon = RO:** a floor.

## 4. Succinctness (Lean count; asymptotics from the spec)

[`ProofShape`](../../../Varuna/ProofSize.lean#L30) counts snarkVM's `Proof` (`data_structures/proof.rs`). For $i$ circuits and $J$ instances in ZK mode, that is $J + 3i + 8$ in $\mathbb G_1$ and $1 + 6i + 3J + 3$ in $\mathbb F$ ([`g1_eq`](../../../Varuna/ProofSize.lean#L63), [`fr_eq`](../../../Varuna/ProofSize.lean#L68)).

The spec's $9\,\mathbb G_1 + 10\,\mathbb F$ omits the three KZG witnesses and the `random_v` values ([`spec_single_proof`](../../../Varuna/ProofSize.lean#L74)). Its batch $\mathbb F$ count $1 + 9i$ is right only when $J = i$ ([`spec_batch_scalars_iff`](../../../Varuna/ProofSize.lean#L86)). Verifier time (2 pairings plus $O(\sum |x| + \log |R_{\max}|)$) is the spec's; Lean has no cost model.

## 5. Zero knowledge (Lean AHP simulator and hiding openings)

The AHP simulator is honest-verifier, query bound 1. [`maskAt`](../../../Varuna/ZK.lean#L41) is the constant mask that sends one opening outside the domain to any chosen field element and leaves the domain values unchanged ([`masked_eval_at_query`](../../../Varuna/ZK.lean#L50), [`masked_agrees_on_domain`](../../../Varuna/ZK.lean#L45)). [`simulateRowcheck`](../../../Varuna/ZK.lean#L65) then makes the rowcheck accept at that challenge ([`simulateRowcheck_accepts`](../../../Varuna/ZK.lean#L69)).

[`simulateLineval`](../../../Varuna/ZK.lean#L105) builds the lineval polynomial from the public input and a mask, with no witness. [`simulateLineval_eq_real`](../../../Varuna/ZK.lean#L111) moves a real witness into the ZK mask, and [`simulateLineval_witness`](../../../Varuna/ZK.lean#L124) shows the honest sumcheck witness agrees. [`simulateLineval_accepts`](../../../Varuna/ZK.lean#L135) is the simulated check. In non-ZK mode the mask is dropped ([`linevalPolyEta_nonZK_ignores_mask`](../../../Varuna/ZK.lean#L85)), so the witness cannot be moved.

The hiding commitment of that polynomial is the non-hiding commitment plus a constant blinding along `gamma_g`. [`simulateHidingLineval_accepts`](../../../Varuna/ZK.lean#L142) is the honest `random_v` opening. [`simulation_extractable`](../../../Varuna/ZK.lean#L154) says that opening checks, and that a fresh algebraic opening of a different polynomial is a trapdoor break or the represented value.

## Areas the plan does not list

1. **How the three V3 checks compose (Lean).** [`v3_chain`](../../../Varuna/Composition.lean#L173), [`sum_linevalPoly`](../../../Varuna/Lineval.lean#L163), [`linevalTarget_eq_mzPoly`](../../../Varuna/Lineval.lean#L115), [`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L185).
2. **From domain identities to R1CS (Lean).** [`satisfies_iff_zmod`](../../../Varuna/Bridge.lean#L64) and [`satisfies_of_rows`](../../../Varuna/Bridge.lean#L96).
3. **Challenge space (Lean).** Every count takes an arbitrary finite $S$.
4. **Degree bounds (Lean).** See 2.4.
5. **Public input and reindexing (Lean).** [`reindexBySubdomain`](../../../Varuna/PublicInput.lean#L34), [`reindex_witness_mod_ne_zero`](../../../Varuna/PublicInput.lean#L46), [`assignment_at_input_position`](../../../Varuna/PublicInput.lean#L73): $\hat z$ equals the verifier's $\hat x$ at every input position, given canonical generators (`hgen`).
6. **Index = circuit (floor, now precise).** The hypotheses `hidx*` of [`satisfies_of_rows`](../../../Varuna/Bridge.lean#L96) state exactly what the floor assumes.
7. **Completeness (Lean).** [`rowcheckResidual_honest`](../../../Varuna/AHP.lean#L128), [`univariateResidual_honest`](../../../Varuna/AHP.lean#L201), [`matrixResidual_honest`](../../../Varuna/AHP.lean#L343), [`kzgCheck_honest`](../../../Varuna/SonicPC.lean#L261), [`accepts_of_residuals_zero`](../../../Varuna/AHP.lean#L402).
8. **Lean vs snarkVM (Lean fingerprint).** [`Fingerprint.lean`](../../../Varuna/Fingerprint.lean) re-checks one captured snarkVM V3 hiding-mode batch proof over two circuits with two instances each ([`batch_shape`](../../../Varuna/Fingerprint.lean#L260); [`fixtures/fingerprint`](../../../fixtures/fingerprint/PROVENANCE.md), from the pinned tree with test-only instrumentation). The verifier sees only combined openings, so the capture is on the prover side, re-assembled in the verifier's LC shape. Kernel `decide` over the BLS12-377 scalar field checks three things:
   - every coefficient snarkVM assembles equals Lean's formula, with circuits and instances combined by `weightedSum` ([`matrix_coeffs`](../../../Varuna/Fingerprint.lean#L297), [`lineval_coeffs`](../../../Varuna/Fingerprint.lean#L286), [`rowcheck_coeffs`](../../../Varuna/Fingerprint.lean#L280));
   - each LC vanishes, both as snarkVM assembled it and in Lean's batched scalar form ([`matrix_vanishes`](../../../Varuna/Fingerprint.lean#L331), [`matrix_model`](../../../Varuna/Fingerprint.lean#L341));
   - the scalar forms are the model ([`eval_selectorBatch`](../../../Varuna/Fingerprint.lean#L81), [`matrixTerm_eq_scalar`](../../../Varuna/Fingerprint.lean#L89)).

   The two circuits differ on every domain, so each batching ingredient is exercised. The first combiner of each family is $1$ and the rest are squeezed, with fresh third-round combiners ([`first_combiners_eq_one`](../../../Varuna/Fingerprint.lean#L348), [`later_combiners_squeezed`](../../../Varuna/Fingerprint.lean#L355)). The selector scale is non-trivial at $\alpha$, $\beta$, and $\gamma$ ([`selectors_scaled`](../../../Varuna/Fingerprint.lean#L364)), and $v_{X_i}(\beta)$ is per circuit ([`input_domains_differ`](../../../Varuna/Fingerprint.lean#L370)). The fixture also shows $\mathrm{row}(\gamma)\,\mathrm{col}(\gamma) \ne \mathrm{row\_col}(\gamma)$ in both circuits ([`product_form_differs`](../../../Varuna/Fingerprint.lean#L374)): Lean's `matrixBPoly` agrees with the deployed $b$ only on $K$, which is all [`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L185) uses. [`SpotCheck.lean`](../../../Varuna/SpotCheck.lean) samples the source. The fixture has field elements only, so the group-level MSM / pairing assembly is outside Lean, and byte encodings stay a floor. Sage proofs are not captured: the Sage implementation is a readable single-circuit PIOP, and snarkVM is the verifier of record.

## What remains

**Faithfulness past the LC layer.** The fingerprint covers zero-eval LC coefficients of one captured batch proof (two circuits, two instances each). The group-level MSM / pairing assembly, byte encodings, and Sage proofs are outside that capture. See the fingerprint item above.

**Primality of the scalar modulus.** `knowledgeSoundness_bls` is the capstone at `ZMod bls12_377_r`, and `Fingerprint.q_eq_bls12_377_r` shows the captured `q` is that number. Primality is a `Fact`, as in §2.3.

**Named floors.** Poseidon = RO, pairing / trapdoor hardness, algebraic adversary, SRS, encodings, and index = circuit. Commitment hiding is the constant shift $\rho \cdot \mathtt{gamma\_g}$ ([`commit_hiding_as_blind`](../../../Varuna/SonicPC.lean), [`commit_blind_shift`](../../../Varuna/SonicPC.lean)) together with binding of both scalars ([`commit_hiding_binding`](../../../Varuna/SonicPC.lean)). Simulation extractability of one hiding opening is [`simulation_extractable`](../../../Varuna/ZK.lean#L154). Unique responses and a distribution over the group stay out: padding makes proofs non-unique, and pairing independence of the two generators is a hypothesis of the hiding binding. [`PreprocessingAHP`](../../../Varuna/Soundness.lean) is the public-coin interaction in the algebraic projection; it carries the represented polynomials, not group elements.

## Summary

| Item | Status | Main Lean anchors |
| --- | --- | --- |
| 1.1 S1 notion | Lean | `inspectResidual`, `ahp_error` |
| 1.2 Unbatched error | Lean | `ahp_error_concrete`, `card_filter_inspectResidual_le` |
| 1.3 AHP batching error | Lean | `batchedZerocheck_extract`, `WeightDraw.card_bad_le_one`, `card_filter_batchedZerocheck_combiners_le` |
| 1.4 Assumptions | Lean | `TrustBoundary.lean` |
| 2.1 Primitive P | Lean (algebraic projection) | `PreprocessingAHP.sound`, `ProofView` |
| 2.2 S2 | Lean | `fs_v2_squeeze_charge`, `fs_query_charge`, `outputBreaks_of_lucky` |
| 2.3 Compilation | Lean | `V3Endpoint.sound_of_openings`, `matrix_sumcheck_of_selector` |
| 2.4 PCS properties | Lean | `inspectOpening_break`, `commit_hiding_binding`, `hidingOpening_extract` |
| 2.5 PC batching loss | Lean | `batchedOpening_extract`, `acrossPoints_extract` |
| 3 Fiat–Shamir | Lean | `v3Init_injective`, `fs_query_charge` |
| 4 Succinctness | Lean count | `ProofShape.g1_eq`, `spec_batch_scalars_iff` |
| 5 Zero knowledge | Lean AHP simulator and one hiding opening | `simulateLineval_eq_real`, `simulation_extractable` |

## Sources and pins

Pin sources by commit, not by branch.

| Source | Use |
| --- | --- |
| `ProvableHQ/varuna-sage-impl` `docs/spec.pdf` | Human protocol spec |
| `ProvableHQ/varuna-sage-impl` Sage PIOPs | Executable identities for rowcheck / sumchecks |
| `ProvableHQ/protocol-docs` (`protocol-docs/` submodule) | Algorithm identities (rowcheck, lincheck, matrix sumcheck), including V3 batching |
| `ProvableHQ/snarkVM` submodule (`Varuna.snarkVMPin`) `algorithms/src/snark/varuna/` | Deployed AHP, FS, PC, batching (target: `VarunaVersion.V3`); sampled in `SpotCheck.lean` |
| `ProvableHQ/snarkVM` `algorithms/src/polycommit/sonic_pc/` and `kzg10/` | PC interface and pairing check |
| `leanprover-community/mathlib4` tag `v4.33.0` | Field, `Polynomial`, roots of unity, Lagrange |
| `fixtures/fingerprint/` | One captured snarkVM V3 hiding-mode batch proof: two circuits, two instances each |

The Sage implementation is single-circuit R1CS with ZK, and without batching or lookups. It is a readable PIOP. snarkVM is the verifier of record, and this project does not capture Sage proofs.

## Build

`lake build --wfail` is the verifier. CI runs it (`.github/workflows/lean.yml`) and fetches the Mathlib cache. Mathlib is pinned at tag `v4.33.0` (toolchain `v4.33.0`). `assert_axioms` / `assert_computable` in `Varuna/AxiomCheck.lean` bound the census; `sorryAx` fails the build. A node on the proof map is `proven` only when its anchor names a real declaration.
