# Captured V3 proof: provenance

`v3_lc_capture.json` holds the field elements of one honest snarkVM
`VarunaVersion::V3` batch proof in hiding (ZK) mode, over two circuits with
two instances each (`prove_batch`, checked by the stock `verify_batch`).
`Varuna/Fingerprint/Capture.lean` is its Lean transcription, and
`Varuna/Fingerprint.lean` re-checks it in the kernel. The captured `η_A` is the
squeezed prepare-third challenge, and `etaA_ne_one` records that it is not the
constant `1`.

| Item | Value |
| --- | --- |
| snarkVM | pinned submodule `29343ebbb7970e4240b4444346aeb26e31009bd7`, tag `v4.11.0` (`Varuna.snarkVMPin`) |
| Instrumentation | `capture.patch` (test-only, every hook under `#[cfg(test)]`) |
| Test | `snark::varuna::tests::fingerprint_capture::capture_zero_eval_lc_fingerprint` |
| Mode | `VarunaHidingMode`, `VarunaVersion::V3`, BLS12-377, Poseidon sponge |
| Domain separator | `VARUNA-2026-V3` |
| Batch domains | `|R| = 8`, `|C| = 16`, `|K| = 16` |
| Circuit `c0` | `Unbalanced`, five constraints; `|R_0| = 8`, `|C_0| = 16`, `|X_0| = 2`, `|K_A| = 16`, `|K_B| = |K_C| = 8` |
| Instances of `c0` | public `x = 3` (witness `a = 1`, `b = 2`) and `x = 5` (witness `a = 2`, `b = 7`) |
| Circuit `c1` | `Product`, `u = pq`, `r = u²`; `|R_1| = 4`, `|C_1| = 8`, `|X_1| = 4`, `|K_A| = |K_B| = |K_C| = 4` |
| Instances of `c1` | public `(p, q, r) = (2, 3, 36)` and `(5, 7, 1225)` |
| RNG | `TestRng::fixed(0x07A0_2026)` |
| SHA-256 | `aee3b208a968d3934e939a532e08c194020581611792925459f53b8c76083c46` |

Circuits are numbered in snarkVM's batch order, by circuit id (`c0` is
`42b42e28…`, `c1` is `45467f8e…`; the full ids are in the JSON). Instances are
numbered in the order passed to `prove_batch`. The two circuits differ on every
domain: `c0` spans the batch `R`, `C`, and `K`, while `c1` is smaller on all
three and has the larger input domain. So the circuit and instance combiners,
the selector scale at `α`, `β`, and `γ`, the per-circuit `δ`s, and the
per-circuit `v_X(β)` all enter the checked coefficients.

## What is captured, and why on the prover side

The verifier never sees the individual evaluations inside a zero-evaluation
linear combination: `rowcheck_zerocheck`, `lineval_sumcheck`, and
`matrix_sumcheck` are virtual commitments opened only as combinations, and
the verifier inserts `0` for them. The values therefore come from the prover.

The capture re-runs `construct_linear_combinations` on a *verifier view* of the
prover's polynomials: the prover-only matrix numerators and denominators
(`a_poly_M`, `b_poly_M`) are removed and the index polynomials
(`row_M`, `col_M`, `row_col_M`, `row_col_val_M`) are added. Every LC then has the
deployed verifier's shape, including the four-term `b` with the committed
`row_col`, and each term is the committed polynomial evaluated at the LC's
query point. The capture asserts in Rust that each LC vanishes, and the
captured proof verifies with the stock V3 verifier.

Alongside the LC terms it records the independent inputs the coefficients are
built from:

- for the batch: domain sizes, the challenges `α, β, γ, η_A, η_B, η_C`, and the
  openings of `h_0`, `h_1`, `g_1`, `h_2`, and the mask;
- for each circuit: domain sizes, the first- and third-round circuit
  combiners, `δ_A, δ_B, δ_C`, the fourth-round sums, and the matrix openings at
  `γ`;
- for each instance: the first- and third-round instance combiners, the
  third-round sums `σ_A, σ_B, σ_C`, `x̂(β)`, and `ŵ(β)`;
- inverse witnesses `|C|^{-1}`, `(v_{R_i}(α) |R|)^{-1}`, `(v_{C_i}(β) |C|)^{-1}`,
  and `(v_{K_M}(γ) |K|)^{-1}` per circuit (the kernel cannot compute modular
  inverses by reduction; each witness is checked by multiplication).

Circuit-labelled LC terms are renamed from `circuit_{id}_…` to `c{i}_…`.

## Regenerating

```sh
git -C snarkVM worktree add /tmp/snarkvm-fp 29343ebbb7970e4240b4444346aeb26e31009bd7
git -C /tmp/snarkvm-fp apply "$PWD/fixtures/fingerprint/capture.patch"
(cd /tmp/snarkvm-fp && VARUNA_FINGERPRINT_OUT="$OLDPWD/fixtures/fingerprint/v3_lc_capture.json" \
  cargo test -p snarkvm-algorithms --release --lib -- \
  snark::varuna::tests::fingerprint_capture::capture_zero_eval_lc_fingerprint --exact)
scripts/fingerprint_to_lean.py && lean-fmt < Varuna/Fingerprint/Capture.lean > /tmp/c.lean \
  && mv /tmp/c.lean Varuna/Fingerprint/Capture.lean
lake build --wfail
```

The capture is deterministic for a fixed seed, so regenerating reproduces the
same file and SHA-256.

## Trust

The re-check uses kernel `decide` over `ZMod q` (the BLS12-377 scalar prime),
not `native_decide`, so it adds no compiler trust and stays in the standard
census (`propext`, `Classical.choice`, `Quot.sound`). What remains trusted is
that this capture came from the pinned snarkVM, as recorded above.
