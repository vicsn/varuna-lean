# Security analysis plan: how each point is tackled

This maps every item of the Varuna security-analysis plan to three things: the answer, what the Lean kernel checks, and what is left. Lean links are relative to the repository root. snarkVM paths refer to the pinned `snarkVM/` submodule (`Varuna.snarkVMPin`). The spec is `protocol-docs/snark/varuna/varuna-spec-prod.tex`.

**Status.** **Lean**: kernel-checked here. **Partial**: Lean checks the core; a composed or concrete statement is missing. **Spec**: argued in the spec only. **Excluded**: a category Ironwood also assumes or does not claim (hash = random oracle, algebraic adversary, hardness, byte encodings, zero knowledge); named as a floor where it is an assumption.

## Finding: the verifier does not check the mask sum (ZK mode)

In V2 the rowcheck uses prover-sent sums $\sigma_M$ in place of $\hat z_M(\alpha)$, and lineval proves them with $\eta_A = 1$ fixed. The lineval sum then reads $e + \sum_M \eta_M \hat z_M(\alpha) = \sum_M \eta_M \sigma_M$ with $e = \sum_{c \in C} s(c)$ for the committed mask $s$. The honest mask has $e = 0$, but nothing checks it. A prover can therefore set $\sigma_A = \hat z_A(\alpha) + e$ undetected, and the verifier accepts any witness of the shifted relation $(Az + e) \circ Bz = Cz$.

- [`v2_chain`](../../../Varuna/Composition.lean#L83): the V2 checks, with [`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L151) discharging the matrix claims, yield exactly the shifted relation on $R$.
- [`shifted_witness_accepts`](../../../Varuna/Composition.lean#L166): every witness of the shifted relation passes both LCs at every challenge, with no inspector reporting a break.
- [`xIsZero_false`](../../../Varuna/Composition.lean#L243) and [`xIsZero_shifted`](../../../Varuna/Composition.lean#L248): the shifted relation is strictly weaker. The constraint $x \cdot 1 = 0$ at $x = 5$ is false, and satisfied with $e = -5$.
- [`v2_chain_nonZK`](../../../Varuna/Composition.lean#L142) and [`satisfies_of_rows`](../../../Varuna/Bridge.lean#L96): NonZK mode has no mask, so $e = 0$ and the chain gives the R1CS relation.

This was confirmed end to end against the pinned snarkVM. With a prover-only patch in hiding mode (the mode `console/network` uses for proving keys), the unmodified verifier accepted a proof of $5 \cdot 1 = 0$; the honest prover refuses that statement. The patch is kept outside this repository.

Either change below closes the gap, and either needs a new `VarunaVersion`, since it changes what verifiers accept:

- enforce $e = 0$ (for example, commit the mask in the form $X\,t(X) + v_C(X)\,r(X)$ with a checked degree bound)
- absorb a claimed mask sum before $\alpha$ and use it in the lineval target, or sample $\eta_A$ as Marlin does

## 1. Soundness of the AHP

### 1.1 The soundness notion S1 that step 2 needs (Lean)

S1 should be round-by-round knowledge soundness, because step 3 then costs $Q \cdot \varepsilon_{\text{round}}$. Each Varuna check is a polynomial identity at a fresh challenge, so the RBR doomed state is "some residual is nonzero", and the bad challenges are its roots. Lean provides this per check as computed data: [`inspectResidual`](../../../Varuna/AHP.lean#L56), [`inspectResidual_accepts`](../../../Varuna/AHP.lean#L68), and the three extractors [`rowcheck_extract`](../../../Varuna/AHP.lean#L155), [`univariate_extract`](../../../Varuna/AHP.lean#L272), [`matrix_extract`](../../../Varuna/AHP.lean#L379). [`ahp_error`](../../../Varuna/Probability.lean#L191) gives the adaptive union bound across $\alpha, \beta, \gamma$.

### 1.2 S1 error of the unbatched AHP, including ZK (Partial)

The spec (lines 444–452) gives $\frac{2|R|}{|\mathbb F\setminus R|} + \frac{2|C|}{|\mathbb F\setminus C|} + \frac{3|K|}{|\mathbb F|}$.

Lean proves the shape of the bound over any finite challenge set $S$:

- [`card_filter_inspectResidual_le`](../../../Varuna/Probability.lean#L41): a residual of degree $d$ has at most $d$ bad challenges in $S$.
- [`ahp_error`](../../../Varuna/Probability.lean#L191): an adaptive prover breaks on at most $(d_R + d_L + d_M)\,|S|^2$ of the $|S|^3$ triples.

$S$ is where snarkVM's 252-bit AHP challenges enter (`crypto_hash/poseidon.rs:473-476`). Masked witnesses are covered, since the residuals are over arbitrary polynomials. Still open: the concrete degrees are inputs, not instantiated. They should include the ZK bound $b$ (`deg h_0 ≤ 2|R| + 2b − 2`, `second.rs:66`). The combiner terms are 1.3.

### 1.3 S1 error of each AHP batching step (Lean)

- **Selectors are indicators of $H_i$ on $H$:** [`selectorPoly_eval_indicator`](../../../Varuna/Selectors.lean#L59).
- **Batched zerocheck:** [`batchedZerocheck_extract`](../../../Varuna/Selectors.lean#L81). A batched rowcheck that is a multiple of $v_H$ gives each circuit's rowcheck on its own domain, or a lucky combination at some point.
- **Batched sumchecks:** [`batchedSumcheck_extract`](../../../Varuna/Selectors.lean#L152) and [`sum_selectorPoly_mul`](../../../Varuna/Selectors.lean#L112). This covers lineval ($\mu, \rho$) and matrix ($\delta$) batching: per-circuit sums, or a lucky combination.
- **Cost of a lucky combination:** at most 1 per free weight ([`card_filter_linear_le_one`](../../../Varuna/Probability.lean#L59), [`card_filter_inspectBatch_pair`](../../../Varuna/Probability.lean#L68)), i.e. $1/|S|$ per family.
- **V2 extra round:** [`alpha_independent_of_prepareThird`](../../../Varuna/Batching.lean#L345) and [`prepareThird_challenge_eq`](../../../Varuna/Batching.lean#L353).

### 1.4 Assumptions underpinning S1 (Lean)

S1 is information-theoretic and does not need the AGM. Every theorem here is `assert_axioms`-bounded to `propext`, `Classical.choice`, `Quot.sound` ([`TrustBoundary.lean`](../../../Varuna/TrustBoundary.lean)). S1's remaining hypotheses are visible in the statements: primitive roots ([`EvalDomain`](../../../Varuna/Domain.lean#L69)) and degree bounds (`hdeg`), which the PC enforces (2.4).

## 2. Soundness of AHP + PCS compilation

### 2.1 The primitive P (Partial)

P is Marlin's public-coin preprocessing argument of knowledge. Lean works in its algebraic-adversary projection, which is Ironwood's model: group elements come with SRS representations ([`represent`](../../../Varuna/Algebraic.lean#L100)), and [`ProofView`](../../../Varuna/Soundness.lean#L89) holds the represented polynomials. P is not defined as an interactive object.

### 2.2 The property S2 that step 3 needs (Partial)

S2 is RBR knowledge soundness, charged per oracle query. [`fs_query_charge`](../../../Varuna/FSBound.lean#L48): with at most $b$ bad answers per query, at most $Q\,b\,|S|^{Q-1}$ of $|S|^Q$ lazy-oracle tapes let a deterministic adversary hit one. [`fs_break_count`](../../../Varuna/FSBound.lean#L83): a V2 output with a break at any squeeze is such a hit, if its challenges were answered on its queries. The per-round bad sets are the inspectors from 1.1. Still open: no single theorem derives every V2 squeeze's bad set from the transcript.

### 2.3 Compilation yields S2 from S1 (Partial)

Under the algebraic restriction, every PC step either gives the polynomial fact S1 uses or a computed trapdoor break:

- an accepted opening with a wrong value: [`inspectOpening_break`](../../../Varuna/Algebraic.lean#L180)
- a violated degree bound: [`inspectDegree_break`](../../../Varuna/Algebraic.lean#L293)
- a batched opening: [`batchedOpening_extract`](../../../Varuna/OpeningBatch.lean#L61) per point, [`acrossPoints_extract`](../../../Varuna/OpeningBatch.lean#L90) across points

Still open: one theorem composing these with [`v2_chain`](../../../Varuna/Composition.lean#L83).

### 2.4 Properties of SonicPCS (Lean; hiding and SE excluded)

- **Extractability:** from the algebraic restriction, named as the floor `algebraicAdversary` ([`ModellingFloor`](../../../Varuna/Match.lean#L33)).
- **Evaluation binding:** [`inspectOpening_break`](../../../Varuna/Algebraic.lean#L180) and [`pairingBreak_of_double_opening`](../../../Varuna/SonicPC.lean#L352); hardness is the `pairingHardness` floor.
- **Degree bounds:** [`inspectDegree_break`](../../../Varuna/Algebraic.lean#L293). [`natDegree_X_mul_add_C_lt`](../../../Varuna/Algebraic.lean#L324) turns $\deg g_1 \le |C|-2$ (`third.rs:60`) into `hdeg`.
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

## 5. Zero knowledge (Excluded)

Ironwood makes no ZK claim. As deployed, ZK mode uses hiding commitments with bound 1 on top of masking (`first.rs:51`; `random_v` at `sonic_pc/mod.rs:769`), and the spec sketches perfect ZK with query bound $b$ (lines 456–468). Lean has the parameters only ([`SNARKMode`](../../../Varuna/AHP.lean#L37), [`maskPoly`](../../../Varuna/AHP.lean#L45)). The finding above shows the mask also bears on soundness.

## Areas the plan does not list

1. **How the three V2 checks compose (Lean).** [`v2_chain`](../../../Varuna/Composition.lean#L83), [`sum_linevalPoly`](../../../Varuna/Lineval.lean#L163), [`linevalTarget_eq_mzPoly`](../../../Varuna/Lineval.lean#L115), [`matrix_sumcheck_value`](../../../Varuna/MatrixSumcheck.lean#L151). This is where the finding comes from.
2. **From domain identities to R1CS (Lean).** [`satisfies_iff_zmod`](../../../Varuna/Bridge.lean#L64) and [`satisfies_of_rows`](../../../Varuna/Bridge.lean#L96).
3. **Challenge space (Lean).** Every count takes an arbitrary finite $S$.
4. **Degree bounds (Lean).** See 2.4.
5. **Public input and reindexing (Lean).** [`reindexBySubdomain`](../../../Varuna/PublicInput.lean#L34), [`reindex_witness_mod_ne_zero`](../../../Varuna/PublicInput.lean#L46), [`assignment_at_input_position`](../../../Varuna/PublicInput.lean#L73): $\hat z$ equals the verifier's $\hat x$ at every input position, given canonical generators (`hgen`).
6. **Index = circuit (floor, now precise).** The hypotheses `hidx*` of [`satisfies_of_rows`](../../../Varuna/Bridge.lean#L96) state exactly what the floor assumes.
7. **Completeness (Lean).** [`rowcheckResidual_honest`](../../../Varuna/AHP.lean#L127), [`univariateResidual_honest`](../../../Varuna/AHP.lean#L200), [`matrixResidual_honest`](../../../Varuna/AHP.lean#L342), [`kzgCheck_honest`](../../../Varuna/SonicPC.lean#L259), [`accepts_of_residuals_zero`](../../../Varuna/AHP.lean#L401).
8. **Lean vs snarkVM (Partial).** [`sample_selector_eval`](../../../Varuna/SpotCheck.lean#L139) and the rest of [`SpotCheck.lean`](../../../Varuna/SpotCheck.lean) sample the pinned tree, and the finding above was confirmed by running snarkVM. There is still no Ironwood-style captured-proof fingerprint: the verifier sees only combined openings, so a capture needs prover instrumentation.

## Summary

| Item | Status | Main Lean anchors |
| --- | --- | --- |
| Mask-sum finding | Lean + PoC | `v2_chain`, `shifted_witness_accepts` |
| 1.1 S1 notion | Lean | `inspectResidual`, `ahp_error` |
| 1.2 Unbatched error | Partial | `card_filter_inspectResidual_le`, `ahp_error` |
| 1.3 AHP batching error | Lean | `batchedZerocheck_extract`, `batchedSumcheck_extract` |
| 1.4 Assumptions | Lean | `TrustBoundary.lean` |
| 2.1 Primitive P | Partial | `represent`, `ProofView` |
| 2.2 S2 | Partial | `fs_query_charge`, `fs_break_count` |
| 2.3 Compilation | Partial | `inspectOpening_break`, `inspectDegree_break` |
| 2.4 PCS properties | Lean (hiding, SE excluded) | `inspectOpening_break`, `inspectDegree_break` |
| 2.5 PC batching loss | Lean | `batchedOpening_extract`, `acrossPoints_extract` |
| 3 Fiat–Shamir | Lean | `v2Init_injective`, `fs_query_charge` |
| 4 Succinctness | Lean count | `ProofShape.g1_eq`, `spec_batch_scalars_iff` |
| 5 Zero knowledge | Excluded | none |
