/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Probability

/-!
# Concrete residual degrees

`ahp_error` takes the residual degrees `d_R, d_L, d_M` as inputs. This file
computes them from degree bounds on the prover's polynomials, so the
composed error `(d_R + d_L + d_M) | S | ^2` out of ` | S | ^3` is stated for the
actual residual constructors (`ahp_error_concrete`).

The bounds are the generic polynomial-degree facts : a product's degree is at
most the sum, a difference's at most the max, and `v_H` has degree ` | H | `.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- Rowcheck residual degree: `max(max(a+b, c), d + |H|)` for input bounds
`deg z_A ≤ a`, `deg z_B ≤ b`, `deg z_C ≤ c`, `deg h₀ ≤ d`. -/
theorem natDegree_rowcheckResidual_le (H : EvalDomain F) {zA zB zC h0 : F[X]} {a b c d : ℕ}
    (hA : zA.natDegree ≤ a) (hB : zB.natDegree ≤ b) (hC : zC.natDegree ≤ c)
    (hd : h0.natDegree ≤ d) :
    (rowcheckResidual H zA zB zC h0).natDegree ≤ max (max (a + b) c) (d + H.n) := by
  unfold rowcheckResidual rowcheckPoly
  refine (natDegree_sub_le _ _).trans (max_le_max ?_ ?_)
  · refine (natDegree_sub_le _ _).trans (max_le_max ?_ hC)
    exact natDegree_mul_le.trans (add_le_add hA hB)
  · refine natDegree_mul_le.trans (add_le_add hd ?_)
    exact le_of_eq H.natDegree_vanishing

/-- Univariate residual degree: `max(max(max(a, e + |K|), 1 + g), 0)` for
`deg f ≤ a`, `deg w.h ≤ e`, `deg w.g ≤ g`. -/
theorem natDegree_univariateResidual_le (K : EvalDomain F) {f : F[X]} {w : UnivariateWitness F}
    {a e g : ℕ} (hf : f.natDegree ≤ a) (he : w.h.natDegree ≤ e) (hg : w.g.natDegree ≤ g) :
    (univariateResidual K f w).natDegree ≤ max (max (max a (e + K.n)) (1 + g)) 0 := by
  unfold univariateResidual
  refine (natDegree_sub_le _ _).trans (max_le_max ?_ (natDegree_C _).le)
  refine (natDegree_sub_le _ _).trans (max_le_max ?_ ?_)
  · refine (natDegree_sub_le _ _).trans (max_le_max hf ?_)
    exact natDegree_mul_le.trans (add_le_add he (le_of_eq K.natDegree_vanishing))
  · exact natDegree_mul_le.trans (add_le_add natDegree_X_le hg)

/-- Matrix residual degree: `max(max(a, b + (1 + g)), h + |K|)` for
`deg a ≤ da`, `deg b ≤ db`, `deg g ≤ g`, `deg h ≤ dh`. -/
theorem natDegree_matrixResidual_le (K : EvalDomain F) {a b g h : F[X]} {σ : F}
    {da db dg dh : ℕ} (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hg : g.natDegree ≤ dg)
    (hh : h.natDegree ≤ dh) :
    (matrixResidual K a b g h σ).natDegree ≤ max (max da (db + (1 + dg))) (dh + K.n) := by
  unfold matrixResidual
  refine (natDegree_sub_le _ _).trans (max_le_max ?_ ?_)
  · refine (natDegree_sub_le _ _).trans (max_le_max ha ?_)
    refine natDegree_mul_le.trans (add_le_add hb ?_)
    refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C _).le.trans (Nat.zero_le _)))
    exact natDegree_mul_le.trans (add_le_add natDegree_X_le hg)
  · exact natDegree_mul_le.trans (add_le_add hh (le_of_eq K.natDegree_vanishing))

/-- Composed single-instance AHP error with the concrete residual degrees
plugged in. Over `S^3`, at most `(d_R + d_L + d_M) | S | ^2` challenge triples
break, where the degrees are the bounds above. -/
theorem ahp_error_concrete [DecidableEq F] (S : Finset F)
    (H K : EvalDomain F) {zA zB zC h0 f : F[X]} {w : UnivariateWitness F} {a b g h : F[X]} {σ : F}
    {dzA dzB dzC dh0 df dwh dwg da db dg dh : ℕ}
    (hzA : zA.natDegree ≤ dzA) (hzB : zB.natDegree ≤ dzB) (hzC : zC.natDegree ≤ dzC)
    (hh0 : h0.natDegree ≤ dh0) (hf : f.natDegree ≤ df) (hwh : w.h.natDegree ≤ dwh)
    (hwg : w.g.natDegree ≤ dwg) (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db)
    (hg : g.natDegree ≤ dg) (hh : h.natDegree ≤ dh) :
    ((tapes S 3).filter fun t =>
        hitsB (ahpBad S (rowcheckResidual H zA zB zC h0)
          (fun _ => univariateResidual K f w) (fun _ _ => matrixResidual K a b g h σ)) [] t
          = true).card ≤
      ((max (max (dzA + dzB) dzC) (dh0 + H.n)) +
        (max (max (max df (dwh + K.n)) (1 + dwg)) 0) +
        (max (max da (db + (1 + dg))) (dh + K.n))) * S.card ^ 2 :=
  ahp_error S _ _ _ (natDegree_rowcheckResidual_le H hzA hzB hzC hh0)
    (fun _ => natDegree_univariateResidual_le K hf hwh hwg)
    (fun _ _ => natDegree_matrixResidual_le K ha hb hg hh)

end Varuna