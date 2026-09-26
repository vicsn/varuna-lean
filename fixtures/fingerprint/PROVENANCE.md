# Captured V2 proof: provenance

`v2_lc_capture.json` holds the field elements of one honest snarkVM
`VarunaVersion::V2` proof in hiding (ZK) mode. `Varuna/Fingerprint/Capture.lean`
is its Lean transcription, and `Varuna/Fingerprint.lean` re-checks it in the
kernel.

| Item | Value |
| --- | --- |
| snarkVM | pinned submodule `38a8fabc67d2e3b0b1b9079936e8208210839beb` (`Varuna.snarkVMPin`) |
| Instrumentation | `capture.patch` (test-only, every hook under `#[cfg(test)]`) |
| Test | `snark::varuna::tests::fingerprint_capture::capture_zero_eval_lc_fingerprint` |
| Mode | `VarunaHidingMode`, `VarunaVersion::V2`, BLS12-377, Poseidon sponge |
| Circuit | `Unbalanced`, public `x = 3`, five constraints; `|R| = 8`, `|C| = 16`, `|X| = 2`, `|K_A| = |K| = 16`, `|K_B| = |K_C| = 8` |
| RNG | `TestRng::fixed(0x07A0_2026)` |
| SHA-256 | `752eca7c58dd89a43f68cb92347a12b0fb37191d5fc43a2aca06ae54c0f85be8` |

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
captured proof verifies with the stock verifier.

Alongside the LC terms it records the independent inputs the coefficients are
built from: domain sizes, the challenges `α, β, γ, η_B, η_C, δ_A, δ_B, δ_C`, the
third- and fourth-round sums, `x̂(β)`, and the inverse witnesses `|C|^{-1}` and
`(v_{K_M}(γ) |K|)^{-1}` (the kernel cannot compute modular inverses by
reduction; each witness is checked by multiplication).

## Regenerating

```sh
git -C snarkVM worktree add /tmp/snarkvm-fp 38a8fabc67d2e3b0b1b9079936e8208210839beb
git -C /tmp/snarkvm-fp apply "$PWD/fixtures/fingerprint/capture.patch"
(cd /tmp/snarkvm-fp && VARUNA_FINGERPRINT_OUT="$OLDPWD/fixtures/fingerprint/v2_lc_capture.json" \
  cargo test -p snarkvm-algorithms --release --lib fingerprint_capture)
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
