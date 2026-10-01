# Security analysis plan: how each point is tackled

This maps every item of the Varuna security-analysis plan to three things: the answer, what the Lean kernel checks, and what is left. Lean links are relative to the repository root. snarkVM paths refer to the pinned `snarkVM/` submodule (`Varuna.snarkVMPin`). The spec is `protocol-docs/snark/varuna/varuna-spec-prod.tex`.

**Status.** **Lean**: kernel-checked here. **Partial**: Lean checks the core; a composed or concrete statement is missing. **Spec**: argued in the spec only. **Excluded**: a category Ironwood also assumes or does not claim (hash = random oracle, algebraic adversary, hardness, byte encodings, zero knowledge); named as a floor where it is an assumption.

## Finding: V2 does not check the mask sum (closed in V3)

In V2 the rowcheck uses prover-sent sums $\sigma_M$ in place of $\hat z_M(\alpha)$, and lineval proves them with $\eta_A = 1$ fixed. The lineval sum then reads $e + \sum_M \eta_M \hat z_M(\alpha) = \sum_M \eta_M \sigma_M$ with $e = \sum_{c \in C} s(c)$ for the committed mask $s$. The honest mask has $e = 0$, but nothing checks it. A prover can therefore set $\sigma_A = \hat z_A(\alpha) + e$ undetected, and the verifier accepts any witness of the shifted relation $(Az + e) \circ Bz = Cz$.

- [`v2_chain`](../../../Varuna/Composition.lean#L83): the V2 checks, with [`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L151) discharging the matrix claims, yield exactly the shifted relation on $R$.
- [`shifted_witness_accepts`](../../../Varuna/Composition.lean#L166): every witness of the shifted relation passes both LCs at every challenge, with no inspector reporting a break.
- [`xIsZero_false`](../../../Varuna/Composition.lean#L243) and [`xIsZero_shifted`](../../../Varuna/Composition.lean#L248): the shifted relation is strictly weaker. The constraint $x \cdot 1 = 0$ at $x = 5$ is false, and satisfied with $e = -5$.
- [`v2_chain_nonZK`](../../../Varuna/Composition.lean#L142) and [`satisfies_of_rows`](../../../Varuna/Bridge.lean#L96): NonZK mode has no mask, so $e = 0$ and the chain gives the R1CS relation.

This was confirmed end to end against snarkVM V2. With a prover-only patch in hiding mode, the unmodified V2 verifier accepted a proof of $5 \cdot 1 = 0$; the honest prover refuses that statement. The patch is kept outside this repository.

V3 closes it by sampling $\eta_A$ in prepare-third, after the mask commitment and the matrix-sum claims, and multiplying the $A$ terms by that challenge (`verifier.rs`, `third.rs`). The lineval combination is then $e + \eta_A(t_A - \sigma_A) + \eta_B(t_B - \sigma_B) + \eta_C(t_C - \sigma_C)$.

- [`v3_chain`](../../../Varuna/Composition.lean): an accepting lineval with no batch break forces $e = 0$ and the unshifted rows on $R$.
- [`v3_shifted_residual_ne`](../../../Varuna/Composition.lean): the V2 messages $\sigma_A = t_A + e$ do not make that residual identically zero when $e \ne 0$ and $\eta_A \ne 1$.
- [`V3Endpoint.sound`](../../../Varuna/Endpoint.lean) composes the $h_0$ opening, the matrix sumchecks, and `v3_chain`. [`V3Endpoint.sound_r1cs`](../../../Varuna/Endpoint.lean) ends at `satisfies` in either mode.
- The V3 transcript domain is `VARUNA-2026-V3` ([`v3Init`](../../../Varuna/Statement.lean), [`v2Init_ne_v3Init`](../../../Varuna/Statement.lean)).

## 1. Soundness of the AHP

### 1.1 The soundness notion S1 that step 2 needs (Lean)

S1 should be round-by-round knowledge soundness, because step 3 then costs $Q \cdot \varepsilon_{\text{round}}$. Each Varuna check is a polynomial identity at a fresh challenge, so the RBR doomed state is "some residual is nonzero", and the bad challenges are its roots. Lean provides this per check as computed data: [`inspectResidual`](../../../Varuna/AHP.lean#L56), [`inspectResidual_accepts`](../../../Varuna/AHP.lean#L68), and the three extractors [`rowcheck_extract`](../../../Varuna/AHP.lean#L155), [`univariate_extract`](../../../Varuna/AHP.lean#L272), [`matrix_extract`](../../../Varuna/AHP.lean#L379). [`ahp_error`](../../../Varuna/Probability.lean#L191) gives the adaptive union bound across $\alpha, \beta, \gamma$.

### 1.2 S1 error of the unbatched AHP, including ZK (Lean)

The spec (lines 444–452) gives $\frac{2|R|}{|\mathbb F\setminus R|} + \frac{2|C|}{|\mathbb F\setminus C|} + \frac{3|K|}{|\mathbb F|}$.

Lean proves the shape of the bound over any finite challenge set $S$:

- [`card_filter_inspectResidual_le`](../../../Varuna/Probability.lean#L41): a residual of degree $d$ has at most $d$ bad challenges in $S$.
- [`ahp_error`](../../../Varuna/Probability.lean#L191): an adaptive prover breaks on at most $(d_R + d_L + d_M)\,|S|^2$ of the $|S|^3$ triples.

- [`ahp_error_concrete`](../../../Varuna/Degree.lean#L70): the same bound with the residual degrees computed from degree bounds on the prover's polynomials, by [`natDegree_rowcheckResidual_le`](../../../Varuna/Degree.lean#L30), [`natDegree_univariateResidual_le`](../../../Varuna/Degree.lean#L43), and [`natDegree_matrixResidual_le`](../../../Varuna/Degree.lean#L55). For example, the rowcheck residual has degree at most $\max(\deg z_A + \deg z_B,\ \deg z_C,\ \deg h_0 + |R|)$.

$S$ is where snarkVM's 252-bit AHP challenges enter (`crypto_hash/poseidon.rs:473-476`). Masked witnesses are covered, since the residuals are over arbitrary polynomials. ZK enters through the input bounds, which carry the query bound $b$ (e.g. `deg h_0 ≤ 2|R| + 2b − 2`, `second.rs:66`). The combiner terms are 1.3.

### 1.3 S1 error of each AHP batching step (Lean)

- **Selectors are indicators of $H_i$ on $H$:** [`selectorPoly_eval_indicator`](../../../Varuna/Selectors.lean#L59).
- **Batched zerocheck:** [`batchedZerocheck_extract`](../../../Varuna/Selectors.lean#L81). A batched rowcheck that is a multiple of $v_H$ gives each circuit's rowcheck on its own domain, or a lucky combination at some point.
- **Batched sumchecks:** [`batchedSumcheck_extract`](../../../Varuna/Selectors.lean#L152) and [`sum_selectorPoly_mul`](../../../Varuna/Selectors.lean#L112). This covers lineval ($\mu, \rho$) and matrix ($\delta$) batching: per-circuit sums, or a lucky combination.
- **Cost of a lucky combination:** at most 1 per free weight ([`card_filter_linear_le_one`](../../../Varuna/Probability.lean#L59), [`card_filter_inspectBatch_pair`](../../../Varuna/Probability.lean#L68)), i.e. $1/|S|$ per family.
- **V2 extra round:** [`alpha_independent_of_prepareThird`](../../../Varuna/Batching.lean#L345) and [`prepareThird_challenge_eq`](../../../Varuna/Batching.lean#L353).

### 1.4 Assumptions underpinning S1 (Lean)

S1 is information-theoretic and does not need the AGM. Every theorem here is `assert_axioms`-bounded to `propext`, `Classical.choice`, `Quot.sound` ([`TrustBoundary.lean`](../../../Varuna/TrustBoundary.lean)). S1's remaining hypotheses are visible in the statements: primitive roots ([`EvalDomain`](../../../Varuna/Domain.lean#L69)) and degree bounds (`hdeg`), which the PC enforces (2.4).

## 2. Soundness of AHP + PCS compilation

### 2.1 The primitive P (Lean; algebraic projection)

P is Marlin's public-coin preprocessing argument of knowledge. [`PreprocessingAHP`](../../../Varuna/Soundness.lean#L216) is that interaction: a list of rounds, each an absorbed message and a squeezed challenge, plus [`ProofView`](../../../Varuna/Soundness.lean#L89), the polynomials read off those rounds. [`PreprocessingAHP.sound`](../../../Varuna/Soundness.lean#L224) requires $\alpha$, $\beta$, and $\gamma$ to be challenges of the rounds and applies [`knowledgeSoundness`](../../../Varuna/Soundness.lean#L184). Group elements still come with SRS representations ([`represent`](../../../Varuna/Algebraic.lean#L100)); the object does not carry group elements itself.

### 2.2 The property S2 that step 3 needs (Lean)

S2 is RBR knowledge soundness, charged per oracle query. [`fs_query_charge`](../../../Varuna/FSBound.lean#L48): with at most $b$ bad answers per query, at most $Q\,b\,|S|^{Q-1}$ of $|S|^Q$ lazy-oracle tapes let a deterministic adversary hit one. [`fs_break_count`](../../../Varuna/FSBound.lean#L83): a V2 output with a break at any squeeze is such a hit, if its challenges were answered on its queries. [`squeezeBad`](../../../Varuna/FSBound.lean#L108) is the bad set of each of the six squeezes: Schwartz–Zippel roots at $\alpha$, $\beta$, $\gamma$, and one-weight `inspectBatch` breaks at the three combiner squeezes. [`fs_v2_squeeze_charge`](../../../Varuna/FSBound.lean#L222) puts those sets on the transcript prefixes and charges the resulting break count. Poseidon = RO stays a floor.

### 2.3 Compilation yields S2 from S1 (Lean)

Under the algebraic restriction, every PC step either gives the polynomial fact S1 uses or a computed trapdoor break:

- an accepted opening with a wrong value: [`inspectOpening_break`](../../../Varuna/Algebraic.lean#L180)
- a violated degree bound: [`inspectDegree_break`](../../../Varuna/Algebraic.lean#L302)
- a batched opening: [`batchedOpening_extract`](../../../Varuna/OpeningBatch.lean#L61) per point, [`acrossPoints_extract`](../../../Varuna/OpeningBatch.lean#L90) across points

[`V2Endpoint.sound`](../../../Varuna/Endpoint.lean#L129) composes the opening reduction with the AHP in one theorem. A no-break opening of the rowcheck quotient $h_0$ ([`value_correct_of_inspect_none`](../../../Varuna/Algebraic.lean#L205)), the three matrix sumchecks with their degree bounds ([`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L185)), and [`v2_chain`](../../../Varuna/Composition.lean#L79) give $(Az + e) \circ Bz = Cz$ on $R$. [`V2Endpoint.sound_nonZK`](../../../Varuna/Endpoint.lean#L170) ends at the R1CS relation.

[`V3Endpoint.sound`](../../../Varuna/Endpoint.lean#L221) is the V3 composition. Each matrix has its own nonzero domain. The $\gamma$ check is `matrixEval` $= 0$ plus [`inspectResidual`](../../../Varuna/AHP.lean#L57), which [`inspectResidual_accepts`](../../../Varuna/AHP.lean#L69) turns into the residual identity [`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L185) consumes. [`sound_of_openings`](../../../Varuna/Endpoint.lean#L301) does the same for $\hat z$, $h_1$, $g_1$, and the three matrix witnesses: a no-break opening plus the scalar check the verifier runs is the polynomial check. [`sound_of_combined_matrix`](../../../Varuna/Endpoint.lean#L377) replaces the three $\gamma$ checks by one $\delta$-combination ([`inspectBatch_accepts`](../../../Varuna/Batching.lean#L169)). [`matrix_sumcheck_of_selector`](../../../Varuna/Endpoint.lean#L429) turns a selector-batched sum on a common domain ([`batchedSumcheck_extract`](../../../Varuna/Selectors.lean#L152)) into $|K|\sigma = \hat M(\alpha,\beta)$ via [`matrix_sumcheck_value_of_sum`](../../../Varuna/MatrixSumcheck.lean#L152). [`knowledgeSoundness_bls`](../../../Varuna/Soundness.lean#L245) restates the Marlin capstone at `ZMod bls12_377_r`; primality of the modulus is a `Fact`.

### 2.4 Properties of SonicPCS (Lean; hiding and SE excluded)

- **Extractability:** from the algebraic restriction, named as the floor `algebraicAdversary` ([`ModellingFloor`](../../../Varuna/Match.lean#L33)).
- **Evaluation binding:** [`inspectOpening_break`](../../../Varuna/Algebraic.lean#L180) and [`pairingBreak_of_double_opening`](../../../Varuna/SonicPC.lean#L352); hardness is the `pairingHardness` floor.
- **Degree bounds:** [`inspectDegree_break`](../../../Varuna/Algebraic.lean#L302). [`natDegree_X_mul_add_C_lt`](../../../Varuna/Algebraic.lean#L333) turns $\deg g_1 \le |C|-2$ (`third.rs:60`) into `hdeg`.
- **Hiding** (ZK only) and **simulation extractability** ([SE-KZG], [WM]): excluded, since Ironwood claims neither. Note that padding makes proofs non-unique (`varuna-padding.tex:256`), which matters for [WM]'s unique-response condition.

### 2.5 Loss from batching SonicPCS openings (Lean)

Both levels reduce to a lucky combination: [`batchedOpening_extract`](../../../Varuna/OpeningBatch.lean#L61) and [`acrossPoints_extract`](../../../Varuna/OpeningBatch.lean#L90). With one free 168-bit challenge per combination (`sonic_pc/mod.rs:301, 505-546`), each costs at most $1/|S|$ ([`card_filter_linear_le_one`](../../../Varuna/Probability.lean#L59)), so the three points cost about $2^{-166}$. The randomizers are transcript-derived, so [`fs_query_charge`](../../../Varuna/FSBound.lean#L48) multiplies by $Q$: $Q = 2^{64}$ gives about $2^{-102}$. The target security level should be fixed together with $Q$.

## 3. Soundness of the Fiat–Shamir transform (Lean; Poseidon = RO excluded)

- **Schedule:** [`V2Transcript`](../../../Varuna/FiatShamir.lean#L129), [`challenge_eq_ro`](../../../Varuna/FiatShamir.lean#L159), and squeeze counts pinned to snarkVM ([`sample_v2_second_round_squeeze`](../../../Varuna/SpotCheck.lean#L52)).
- **Statement binding:** [`v2Init`](../../../Varuna/Statement.lean#L42) models `init_sponge` (`varuna.rs:136-154`). [`v2Init_injective`](../../../Varuna/Statement.lean#L77) and [`before_ne_of_inputs_ne`](../../../Varuna/Statement.lean#L88): different public inputs never share a challenge prefix, and equal challenges there are an RO collision ([`collision_of_inputs_ne`](../../../Varuna/Statement.lean#L106)).
- **Query charging:** [`fs_query_charge`](../../../Varuna/FSBound.lean#L48).
- **Poseidon = RO:** a floor.

## 4. Succinctness (Lean count; asymptotics from the spec)

[`ProofShape`](../../../Varuna/ProofSize.lean#L30) counts snarkVM's `Proof` (`data_structures/proof.rs`). For $i$ circuits and $J$ instances in ZK mode, that is $J + 3i + 8$ in $\mathbb G_1$ and $1 + 6i + 3J + 3$ in $\mathbb F$ ([`g1_eq`](../../../Varuna/ProofSize.lean#L63), [`fr_eq`](../../../Varuna/ProofSize.lean#L68)).

The spec's $9\,\mathbb G_1 + 10\,\mathbb F$ omits the three KZG witnesses and the `random_v` values ([`spec_single_proof`](../../../Varuna/ProofSize.lean#L74)). Its batch $\mathbb F$ count $1 + 9i$ is right only when $J = i$ ([`spec_batch_scalars_iff`](../../../Varuna/ProofSize.lean#L86)). Verifier time (2 pairings plus $O(\sum |x| + \log |R_{\max}|)$) is the spec's; Lean has no cost model.

## 5. Zero knowledge (Lean AHP simulator; commitment hiding excluded)

The AHP simulator is honest-verifier, query bound 1. [`maskAt`](../../../Varuna/ZK.lean#L39) is the constant mask that sends one opening outside the domain to any chosen field element and leaves the domain values unchanged ([`masked_eval_at_query`](../../../Varuna/ZK.lean#L48), [`masked_agrees_on_domain`](../../../Varuna/ZK.lean#L43)). [`simulateRowcheck`](../../../Varuna/ZK.lean#L63) then makes the rowcheck accept at that challenge ([`simulateRowcheck_accepts`](../../../Varuna/ZK.lean#L67)).

[`simulateLineval`](../../../Varuna/ZK.lean#L103) builds the lineval polynomial from the public input and a mask, with no witness. [`simulateLineval_eq_real`](../../../Varuna/ZK.lean#L109) moves a real witness into the ZK mask, and [`simulateLineval_witness`](../../../Varuna/ZK.lean#L122) shows the honest sumcheck witness agrees. [`simulateLineval_accepts`](../../../Varuna/ZK.lean#L133) is the simulated check. In non-ZK mode the mask is dropped ([`linevalPolyEta_nonZK_ignores_mask`](../../../Varuna/ZK.lean#L83)), so the witness cannot be moved.

Hiding commitments (`random_v`, bound 1) and simulation extractability stay excluded. The mask also bears on soundness, as in the finding above.

## Areas the plan does not list

1. **How the three V2 checks compose (Lean).** [`v2_chain`](../../../Varuna/Composition.lean#L83), [`sum_linevalPoly`](../../../Varuna/Lineval.lean#L163), [`linevalTarget_eq_mzPoly`](../../../Varuna/Lineval.lean#L115), [`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L151). This is where the finding comes from.
2. **From domain identities to R1CS (Lean).** [`satisfies_iff_zmod`](../../../Varuna/Bridge.lean#L64) and [`satisfies_of_rows`](../../../Varuna/Bridge.lean#L96).
3. **Challenge space (Lean).** Every count takes an arbitrary finite $S$.
4. **Degree bounds (Lean).** See 2.4.
5. **Public input and reindexing (Lean).** [`reindexBySubdomain`](../../../Varuna/PublicInput.lean#L34), [`reindex_witness_mod_ne_zero`](../../../Varuna/PublicInput.lean#L46), [`assignment_at_input_position`](../../../Varuna/PublicInput.lean#L73): $\hat z$ equals the verifier's $\hat x$ at every input position, given canonical generators (`hgen`).
6. **Index = circuit (floor, now precise).** The hypotheses `hidx*` of [`satisfies_of_rows`](../../../Varuna/Bridge.lean#L96) state exactly what the floor assumes.
7. **Completeness (Lean).** [`rowcheckResidual_honest`](../../../Varuna/AHP.lean#L127), [`univariateResidual_honest`](../../../Varuna/AHP.lean#L200), [`matrixResidual_honest`](../../../Varuna/AHP.lean#L342), [`kzgCheck_honest`](../../../Varuna/SonicPC.lean#L259), [`accepts_of_residuals_zero`](../../../Varuna/AHP.lean#L401).
8. **Lean vs snarkVM (Lean fingerprint).** [`Fingerprint.lean`](../../../Varuna/Fingerprint.lean) re-checks one captured snarkVM V2 hiding-mode proof ([`fixtures/fingerprint`](../../../fixtures/fingerprint/PROVENANCE.md), from the pinned tree with test-only instrumentation). The verifier sees only combined openings, so the capture is on the prover side, re-assembled in the verifier's LC shape. Kernel `decide` over the BLS12-377 scalar field checks three things:
   - every coefficient snarkVM assembles equals Lean's formula ([`matrix_coeffs`](../../../Varuna/Fingerprint.lean#L203), [`lineval_coeffs`](../../../Varuna/Fingerprint.lean#L195), [`rowcheck_coeffs`](../../../Varuna/Fingerprint.lean#L189));
   - each LC vanishes, both as snarkVM assembled it and in Lean's scalar form ([`matrix_vanishes`](../../../Varuna/Fingerprint.lean#L231), [`matrix_model`](../../../Varuna/Fingerprint.lean#L244));
   - the scalar forms are the model ([`linevalEval_eq_scalar`](../../../Varuna/Fingerprint.lean#L87), [`matrixTerm_eq_scalar`](../../../Varuna/Fingerprint.lean#L97)).

   The fixture uses unequal $|K_M|$, so the selector scale is exercised ([`selB_ne_one`](../../../Varuna/Fingerprint.lean#L263)). It also shows $\mathrm{row}(\gamma)\,\mathrm{col}(\gamma) \ne \mathrm{row\_col}(\gamma)$ ([`product_form_differs`](../../../Varuna/Fingerprint.lean#L267)): Lean's `matrixBPoly` agrees with the deployed $b$ only on $K$, which is all [`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L151) uses. [`SpotCheck.lean`](../../../Varuna/SpotCheck.lean) samples the source, and the finding above was confirmed by running snarkVM. Not covered: the group-level MSM / pairing assembly and byte encodings (a floor).

## Summary

| Item | Status | Main Lean anchors |
| --- | --- | --- |
| Mask-sum finding | Closed in V3 | `v3_chain`, `v3_shifted_residual_ne` |
| 1.1 S1 notion | Lean | `inspectResidual`, `ahp_error` |
| 1.2 Unbatched error | Lean | `ahp_error_concrete`, `card_filter_inspectResidual_le` |
| 1.3 AHP batching error | Lean | `batchedZerocheck_extract`, `batchedSumcheck_extract` |
| 1.4 Assumptions | Lean | `TrustBoundary.lean` |
| 2.1 Primitive P | Lean (algebraic projection) | `PreprocessingAHP.sound`, `ProofView` |
| 2.2 S2 | Lean | `fs_v2_squeeze_charge`, `fs_query_charge` |
| 2.3 Compilation | Lean | `V3Endpoint.sound_of_openings`, `matrix_sumcheck_of_selector` |
| 2.4 PCS properties | Lean (hiding, SE excluded) | `inspectOpening_break`, `inspectDegree_break` |
| 2.5 PC batching loss | Lean | `batchedOpening_extract`, `acrossPoints_extract` |
| 3 Fiat–Shamir | Lean | `v2Init_injective`, `fs_query_charge` |
| 4 Succinctness | Lean count | `ProofShape.g1_eq`, `spec_batch_scalars_iff` |
| 5 Zero knowledge | Lean AHP simulator (hiding excluded) | `simulateLineval_eq_real`, `masked_eval_at_query` |
