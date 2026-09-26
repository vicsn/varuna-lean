# Security analysis plan: how each point is tackled

This maps every item of the Varuna security-analysis plan to three things: the answer (from the literature or `protocol-docs`), what the Lean kernel checks, and what is left. Lean links are relative to the repository root. snarkVM paths refer to the pinned `snarkVM/` submodule (`Varuna.snarkVMPin`). The spec is `protocol-docs/snark/varuna/varuna-spec-prod.tex`.

**Status.** **Lean**: kernel-checked here. **Partial**: Lean checks the algebraic core; the probabilistic or compiled statement is not in Lean. **Spec**: argued in the spec, not in Lean. **Open**: argued in neither.

**What Lean proves, overall.** [`knowledgeSoundness`](../../../Varuna/Soundness.lean#L178) holds at a generic field. If the three V2 linear combinations vanish, the batch sum vanishes, and no Schwartz–Zippel or batch break is returned ([`ProofView.inspect`](../../../Varuna/Soundness.lean#L144) `= none`), then:

- Hadamard holds on `H`
- the lineval sum identity holds
- the matrix identity holds on `K`
- every batch claim is zero

There is no adversary, no probability, no zero knowledge, and no cost model. The probability of avoiding a break is the open `goodChal` node on the [proof map](proof-map.html).

## 1. Soundness of the AHP

### 1.1 The soundness notion S1 that step 2 needs (Partial)

Marlin's compiler needs AHP knowledge soundness against unbounded provers that send bounded-degree polynomials. If step 3 goes through round-by-round (RBR) Fiat–Shamir (see 2.2), S1 must be RBR knowledge soundness. Varuna fits that shape. Each check is a polynomial identity tested at a fresh challenge. The RBR "doomed" state is "some residual is a nonzero polynomial". Leaving that state requires the challenge to hit the residual's root set.

Lean encodes this per-check structure, with the break as returned data:

- [`inspectResidual`](../../../Varuna/AHP.lean#L56) returns the challenge when a nonzero residual vanishes at it.
- [`inspectResidual_accepts`](../../../Varuna/AHP.lean#L68): accepted and no break implies the residual is zero.
- [`rowcheck_extract`](../../../Varuna/AHP.lean#L155), [`univariate_extract`](../../../Varuna/AHP.lean#L283), and [`matrix_extract`](../../../Varuna/AHP.lean#L390) apply this to the three LCs; [`knowledgeSoundness`](../../../Varuna/Soundness.lean#L178) composes them.

Not in Lean: an RBR state function across the six rounds, an extractor that outputs a witness, and any probability.

### 1.2 S1 error of the unbatched AHP, including ZK (Spec; Lean has the per-check lemma)

The spec (lines 444–452, adapted from Marlin §5.3.3) gives

$$
\frac{2|R|}{|\mathbb F\setminus R|} + \frac{2|C|}{|\mathbb F\setminus C|} + \frac{3|K|}{|\mathbb F|}.
$$

Three points should be tightened:

- **ZK raises the degrees.** snarkVM asserts $\deg h_0 \le 2|R| + 2b - 2$ (`ahp/prover/round_functions/second.rs:66`) and $\deg s \le 2|C| + 2b - 3$ (`first.rs:121`). The numerators should carry $b$.
- **Two terms are missing.** Combining the three lineval claims with $\eta_B, \eta_C$ costs up to $1/|S|$, and so does combining the matrix sumchecks with $\delta$.
- **Challenges are not uniform over $\mathbb F$.** AHP challenges are 252-bit integers (`get_fe` uses `size_in_bits() - 1`, `crypto_hash/poseidon.rs:473-476`). So $|S| = 2^{252}$, minus the excluded domain points: the verifier rejects $\alpha \in R$, $\beta \in C$, $\gamma \in K$ (`ahp/verifier/verifier.rs:175, 212, 252`).

Lean has the pieces that sit underneath each term:

- [`card_szBadSet_le_natDegree`](../../../Varuna/Domain.lean#L310): the bad set has at most as many points as the degree.
- [`rowcheck_sound`](../../../Varuna/AHP.lean#L146), [`univariate_sound`](../../../Varuna/AHP.lean#L274), [`matrix_sound`](../../../Varuna/AHP.lean#L382): a challenge outside the bad set rejects a nonzero residual.
- Residuals are over arbitrary polynomials, so masked witnesses are covered. [`SNARKMode`](../../../Varuna/AHP.lean#L37) and [`maskPoly`](../../../Varuna/AHP.lean#L45) parameterize the lineval mask.

No degree is computed for the concrete residuals, and nothing sums the terms.

### 1.3 S1 error of each AHP batching step (Partial)

The batching steps are:

- instance and circuit combiners $\tau, \nu$ in the rowcheck
- $\eta_B, \eta_C$ across the three matrices
- $\mu, \rho$ in lineval
- $\delta$ in the matrix sumcheck
- selectors $s_{R,R_i}$, which lift each identity to the common domain

Each combination has first coefficient $1$ and independent challenges elsewhere. A combination that vanishes while some claim does not costs at most $1/|S|$ per family; Schwartz–Zippel then applies to the batched residual. The spec defers this to [chenBBZ23, §3.1] without numbers (line 454).

The V2 extra round belongs here. $\eta_B, \eta_C$ are squeezed after the sums $\sigma_{M,i,j}$ are absorbed, so the prover must fix the sums before seeing them.

Lean checks the following:

- **Lucky combination as data**, at the field level: [`inspectBatch`](../../../Varuna/Batching.lean#L150) and [`inspectBatch_accepts`](../../../Varuna/Batching.lean#L169).
- **First coefficient is 1:** [`circuitCombiners`](../../../Varuna/Batching.lean#L52), [`MatrixCombiners.ofEtaBC`](../../../Varuna/Batching.lean#L79), [`DeltaCombiners.first`](../../../Varuna/Batching.lean#L97).
- **Selectors:** [`selectorPoly`](../../../Varuna/Batching.lean#L200), [`selector_mul_vanishing`](../../../Varuna/Batching.lean#L225), [`lift_residual`](../../../Varuna/Batching.lean#L232). [`selectorPoly_eval`](../../../Varuna/Batching.lean#L251) matches snarkVM's formula, including the $|H_i|/|H|$ scale.
- **Ordering:** [`alpha_independent_of_prepareThird`](../../../Varuna/Batching.lean#L345) and [`prepareThird_challenge_eq`](../../../Varuna/Batching.lean#L353).

Not in Lean:

- the soundness direction of the batched polynomial identity; only the honest [`batched_rowcheck_two`](../../../Varuna/Batching.lean#L240) is proved
- the $\mu, \rho, \delta$ batching of lineval and the matrix sumcheck
- the error numbers

### 1.4 Assumptions underpinning S1 (Lean)

S1 is information-theoretic and does not need the AGM. The AGM (or Marlin's "other concrete assumptions") enters only through PC extractability at compilation (see 2.4).

Lean confirms the algebraic side. Every AHP theorem and `knowledgeSoundness` is `assert_axioms`-bounded to `propext`, `Classical.choice`, and `Quot.sound` ([`TrustBoundary.lean`](../../../Varuna/TrustBoundary.lean)).

S1 does carry two assumptions, both visible as hypotheses:

- the field has a primitive root of each domain order ([`EvalDomain.hω`](../../../Varuna/Domain.lean#L69))
- the prover's polynomials respect degree bounds (`hdeg` in `knowledgeSoundness`), which the PCS must enforce

## 2. Soundness of AHP + PCS compilation

### 2.1 The primitive P (Open; Lean has the algebraic view)

Marlin compiles an AHP and an extractable PC into a public-coin preprocessing interactive argument of knowledge with a universal SRS. Varuna follows that compilation directly, not a BCS-style IOP. Plonk's preprocessed idealised low-degree protocol (def. 4.1) is the same object as the AHP with the PC abstracted, and is a reasonable name for it.

Lean works in that idealised view. [`ProofView`](../../../Varuna/Soundness.lean#L85) holds the committed polynomials themselves, as an extractor would produce them, not commitments. P is not defined as an interactive object.

### 2.2 The property S2 that step 3 needs (Open)

Varuna has six rounds, plus the PC's own challenges. Plain knowledge soundness loses roughly $Q^{\text{rounds}}$ under Fiat–Shamir. The usable notions are RBR knowledge soundness or state-restoration knowledge soundness, each with a loss of about $Q \cdot \varepsilon_{\text{round}}$.

[WM] shows that Fiat–Shamir-compiled Plonk, Sonic, and Marlin are simulation-extractable, given:

- forking soundness
- unique responses
- trapdoor-less zero knowledge

That is the likely route for Varuna. [BCP] would make this cheap only if P were an IOP with preprocessing, which Marlin's PC-compiled argument is not.

Lean supplies what any Fiat–Shamir proof needs from the schedule. Each challenge is the random oracle applied to exactly the prefix before it: [`V2Transcript.before`](../../../Varuna/FiatShamir.lean#L144), [`challenge_eq_ro`](../../../Varuna/FiatShamir.lean#L157), [`challenge_of_same_prefix`](../../../Varuna/FiatShamir.lean#L174). The V2 ordering is covered in 1.3. There is no S2 definition.

### 2.3 Compilation yields S2 from S1 (Open)

This is not in Lean. A proof would reuse:

- [`pairingBreak_of_double_opening`](../../../Varuna/SonicPC.lean#L352): two accepting openings of one commitment at one point, with different values, give a pairing-product identity with a nonzero scalar
- [`inspectBinding_none_same_point`](../../../Varuna/Soundness.lean#L167)
- [`kzgCheck_honest`](../../../Varuna/SonicPC.lean#L259) and [`kzgCheck_batch`](../../../Varuna/SonicPC.lean#L409)

Extracting polynomials from commitments round by round is where the AGM is used. Working with `ProofView` assumes that step.

### 2.4 Properties of SonicPCS (Partial)

- **Extractability.** Straight-line extractability with degree bounds (Marlin, AGM) is needed for 2.3. It is not in Lean and is not a named floor: [`ModellingFloor`](../../../Varuna/Match.lean#L33) lists pairing hardness and the SRS, not extractability. It should be added.
- **Evaluation binding.** Reduced to a pairing break by `pairingBreak_of_double_opening`; hardness is the `pairingHardness` floor.
- **Degree bounds.** Enforced with shifted powers (`polycommit/sonic_pc/mod.rs:102-139`; $g_1$ is bounded by $|C|-2$ at `third.rs:60`). [`PolynomialInfo.degreeBound`](../../../Varuna/SonicPC.lean#L40) and [`respectsDegreeBound`](../../../Varuna/SonicPC.lean#L60) exist, but [`kzgCheck`](../../../Varuna/SonicPC.lean#L219) models only the unshifted check. S1 takes the bound as the hypothesis `hdeg`.
- **Hiding.** Needed only for ZK (see 5.1). snarkVM's ZK mode uses hiding bound 1 (`first.rs:51`; `random_v` at `sonic_pc/mod.rs:769`). `kzgCheck` is non-hiding.
- **Simulation extractability.** Needed if a proof must not be mauled into a proof of another statement, as with Aleo transitions ([SE-KZG], [WM]). [WM]'s unique-response condition interacts with padding, which makes proofs non-unique (`protocol-docs/snark/varuna/varuna-padding.tex:256`). Not in Lean.

### 2.5 Loss from batching SonicPCS openings (Partial)

Openings are batched at two levels, both with 168-bit challenges (`squeeze_short_nonnative_field_element`, `poseidon.rs:206`):

1. **Per query point:** polynomials are combined with one challenge each (`sonic_pc/mod.rs:301`).
2. **Across $\alpha, \beta, \gamma$:** the verifier combines the pairing checks with randomizers from a sponge clone that has absorbed the proofs (`sonic_pc/mod.rs:505-546`).

Each combination costs at most $2^{-168}$, so the three points give about $2^{-166}$ before Fiat–Shamir. The randomizers are derived from the transcript, so a prover can grind them. In the ROM the bound is therefore multiplied by the number of oracle queries $Q$: $Q = 2^{64}$ gives about $2^{-102}$. The target security level should be fixed together with $Q$.

Lean has only [`kzgCheck_batch`](../../../Varuna/SonicPC.lean#L409): two claims at one point, combined with $\xi$, still verify. That is completeness. The soundness loss is not stated; it would be an `inspectBatch`-shaped break on openings.

## 3. Soundness of the Fiat–Shamir transform (Partial)

With S2 as RBR or state-restoration knowledge soundness, Fiat–Shamir with an ideal hash gives a knowledge-sound argument with a loss of about $Q \cdot \varepsilon_{\text{round}}$. The plan is right that the proof work moves to step 2. Two implementation conditions are not automatic, though, and belong here:

- the transcript must bind the whole statement, or weak Fiat–Shamir attacks apply
- every prover message must be absorbed before the next squeeze

snarkVM's `init_sponge` absorbs the protocol name, batch sizes, all public inputs, and the circuit commitments (`snark/varuna/varuna.rs:136-154`). Each round absorbs its commitments and sums before squeezing.

Lean has:

- **The V2 schedule:** [`V2Challenge`](../../../Varuna/FiatShamir.lean#L74), [`V2Transcript`](../../../Varuna/FiatShamir.lean#L127), [`V2Transcript.challenge`](../../../Varuna/FiatShamir.lean#L153).
- **Squeeze counts pinned to snarkVM:** [`secondRoundSqueezeCount`](../../../Varuna/FiatShamir.lean#L264), [`sample_v2_second_round_squeeze`](../../../Varuna/SpotCheck.lean#L52).
- **Forks and collisions as data:** [`inspectFork`](../../../Varuna/FiatShamir.lean#L189), [`inspectCollision`](../../../Varuna/FiatShamir.lean#L219).
- **Poseidon = RO** as the named floor `ModellingFloor.poseidonRO`.

Not in Lean: the Fiat–Shamir theorem itself (the forking lemma is `hyp` on the proof map), and what `init` contains. [`V2Transcript.init`](../../../Varuna/FiatShamir.lean#L127) is opaque, so statement binding is checked only by reading snarkVM.

## 4. Succinctness (Spec)

The spec (lines 470–488) gives:

- **Single proof:** $9\,\mathbb G_1 + 10\,\mathbb F$.
- **Batch of $i$ circuits and $j$ instances:** $(5 + j + 3i)\,\mathbb G_1 + (1 + 9i)\,\mathbb F$.
- **Verifier:** 2 pairings plus $O(\sum|x| + \log|R_{\max}|)$.

Counting snarkVM's `Proof` (`snark/varuna/data_structures/proof.rs:36-54, 117-126, 225-243`) for $i$ circuits and $J$ instances in total gives:

- **Commitments:** $J + 3i + 5$ in $\mathbb G_1$ ($J + 3i + 4$ in NonZK, which has no mask).
- **KZG witnesses:** $3$ in $\mathbb G_1$, one per query point.
- **Field elements:** $1 + 6i + 3J$, plus $3$ `random_v` values in ZK mode.

The spec's $\mathbb G_1$ counts match the commitments alone. Its $\mathbb F$ count assumes one instance per circuit. The two should be reconciled.

This is not in Lean and is not a kernel concern. Lean pins only the counts that drive it: three zero-evaluation LCs ([`lcWithZeroEval`](../../../Varuna/AHP.lean#L84)) and three query points ([`queryChallengeNames`](../../../Varuna/Match.lean#L79)).

## 5. Zero knowledge (Open)

### 5.1 Does the PCS need to be hiding?

The spec's sketch relies on masked polynomials being $b$-wise independent off $R$, with the verifier rejecting queries in $R$ (`verifier.rs:175, 212, 252`). Compilation adds roughly one more "evaluation" per commitment, at the SRS trapdoor. KZG witnesses are functions of the polynomial. So a non-hiding PC is enough only if the mask degree covers the openings plus the commitment.

As deployed, ZK mode uses hiding commitments with bound 1 on top of masking. Lean has only the parameters: `SNARKMode`, `maskPoly`, and `PolynomialInfo.hidingBound`. `kzgCheck` is the non-hiding check.

### 5.2 Proving zero knowledge

The spec (lines 456–468) sketches perfect ZK with query bound $b$. The cleanest order is:

1. honest-verifier ZK of the AHP with query bound $b$ (step 1)
2. Marlin's compiler theorem: ZK is preserved given a hiding PC or enough masking
3. Fiat–Shamir in the programmable ROM

For simulation extractability, [WM] needs a trapdoor-less simulator, which argues for proving ZK at the AHP level.

This is not in Lean. The extra ZK constraint row ($\rho_C = \rho_A \rho_B$, spec round 1) is not modelled in [`R1CS.lean`](../../../Varuna/R1CS.lean).

## Areas the plan does not list

1. **How the three V2 checks compose.** snarkVM never commits $\hat z_M$, so soundness depends on a chain:
    - The rowcheck LC uses the prover-sent sums $\sigma_{M,i,j}$ in place of $\hat z_M(\alpha)$ (`ahp/ahp.rs:250-259`).
    - Lineval proves those sums, with $\hat M(\alpha,\beta)$ replaced by fourth-round claims (`ahp.rs:326-337`).
    - The matrix sumcheck proves those claims.

    Lean proves the three identities separately. `ProofView` evaluates `zA`, `zB`, `zC` at $\alpha$ directly, as in Marlin, so the chain is not in Lean. Relatedly, [`linevalPoly`](../../../Varuna/AHP.lean#L263) is the verifier's LC with constants in place of $\hat M(\alpha, X)$. It is correct at $\beta$, but it is not the polynomial the Schwartz–Zippel step needs. `knowledgeSoundness` is generic in `f`, so nothing proved depends on it.
2. **From domain identities to R1CS.** [`satisfies_iff_hadamard`](../../../Varuna/R1CS.lean#L465) is over the `Int` carrier; the AHP is over a Mathlib field. No lemma turns Hadamard on $H$ plus lincheck into `satisfies`; the proof-map node `r1csRel` is still an object.
3. **Challenge space.** Error terms should use $|S|$, not $|\mathbb F|$: 252-bit AHP challenges and 168-bit PC challenges (see 1.2 and 2.5).
4. **Degree bounds.** S1 needs them and the PCS enforces them. In Lean they are only the hypothesis `hdeg`.
5. **Public input and reindexing.** $\hat z = \hat x + v_X \hat w$ is [`assignmentPoly`](../../../Varuna/AHP.lean#L253) / [`eval_assignmentPoly`](../../../Varuna/AHP.lean#L257). `reindex_by_subdomain` is not modelled (see the header of [`Indexer.lean`](../../../Varuna/Indexer.lean)).
6. **Index = circuit.** Soundness is relative to the verifying key. That the key encodes the intended circuit is the floor `indexEqualsCircuit`. [`holographicEval_at_nodes`](../../../Varuna/Indexer.lean#L85) proves only that an honest index encodes the matrix.
7. **Completeness.** Lean has [`rowcheckResidual_honest`](../../../Varuna/AHP.lean#L127), [`univariateResidual_honest`](../../../Varuna/AHP.lean#L200), [`matrixResidual_honest`](../../../Varuna/AHP.lean#L353), [`kzgCheck_honest`](../../../Varuna/SonicPC.lean#L259), and [`accepts_of_residuals_zero`](../../../Varuna/AHP.lean#L412).
8. **Lean vs snarkVM.** [`SpotCheck.lean`](../../../Varuna/SpotCheck.lean) samples identities against the pinned tree; it caught the missing $|H_i|/|H|$ selector scale. There is no captured-proof fingerprint.

## Summary

| Item | Status | Main Lean anchors |
| --- | --- | --- |
| 1.1 S1 notion | Partial | `inspectResidual`, `*_extract`, `knowledgeSoundness` |
| 1.2 Unbatched error | Spec | `card_szBadSet_le_natDegree`, `*_sound` |
| 1.3 AHP batching error | Partial | `inspectBatch`, `selectorPoly_eval`, `alpha_independent_of_prepareThird` |
| 1.4 Assumptions | Lean | `TrustBoundary.lean` |
| 2.1 Primitive P | Open | `ProofView` |
| 2.2 S2 | Open | `challenge_eq_ro` |
| 2.3 Compilation | Open | `pairingBreak_of_double_opening` |
| 2.4 PCS properties | Partial | `pairingBreak_of_double_opening`, `respectsDegreeBound` |
| 2.5 PC batching loss | Partial | `kzgCheck_batch` |
| 3 Fiat–Shamir | Partial | `V2Transcript`, `inspectFork`, `ModellingFloor` |
| 4 Succinctness | Spec | none |
| 5.1 Hiding | Open | `SNARKMode`, `PolynomialInfo` |
| 5.2 ZK proof | Open | none |

For a soundness claim, the largest gaps are, in order:

1. the V2 composition chain (area 1 above)
2. soundness of the batched identity (1.3)
3. PC extractability and the compilation theorem, including naming the missing floor (2.3–2.4)
4. the RBR or Fiat–Shamir theorem (2.2, 3)
