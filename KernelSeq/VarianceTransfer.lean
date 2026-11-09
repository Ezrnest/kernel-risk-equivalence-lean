import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Quantitative variance transfer

Algebraic and norm-comparison steps for variance transfer, with operator
trace, Loewner, and Hilbert–Schmidt bounds as explicit premises.
-/

namespace KernelSeq

/-- Absorb the empirical variance on the right of the trace comparison.
The factor `2` is valid on the manuscript's good event `δ ≤ 1/4`. -/
theorem variance_error_absorption {a b N E δ : ℝ}
    (hb : 0 ≤ b) (hN : 0 ≤ N) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4)
    (htrace : |a - b| ≤ δ * (a + E ^ 2 * N)) :
    |a - b| ≤ 2 * δ * (b + E ^ 2 * N) := by
  have ha : a ≤ b + |a - b| := by linarith [le_abs_self (a - b)]
  have hstep := mul_le_mul_of_nonneg_left ha hδ
  have hsmall := mul_le_mul_of_nonneg_right hδsmall (abs_nonneg (a - b))
  have hmain : 0 ≤ δ * (b + E ^ 2 * N) :=
    mul_nonneg hδ (add_nonneg hb (mul_nonneg (sq_nonneg E) hN))
  nlinarith

/-- A scalar norm comparison controls both squared norms. -/
theorem squared_comparison_of_abs_sub_le {a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (h : |a - b| ≤ d) :
    |a ^ 2 - b ^ 2| ≤ d * (2 * b + d) ∧ a ^ 2 ≤ (b + d) ^ 2 := by
  have hab := (abs_le.mp h).2
  have hasum : a + b ≤ 2 * b + d := by linarith
  have hmul := mul_le_mul h hasum (add_nonneg ha hb) hd
  have hidentity : |a ^ 2 - b ^ 2| = |a - b| * (a + b) := by
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring,
      abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  constructor
  · rw [hidentity]
    exact hmul
  · nlinarith

/-- The square-root comparison between the empirical and population
squared Hilbert–Schmidt norms. -/
theorem variance_sqrt_comparison {W Q d : ℝ}
    (hW : 0 ≤ W) (hQ : 0 ≤ Q) (hd : 0 ≤ d)
    (h : |Real.sqrt W - Real.sqrt Q| ≤ d) :
    |W - Q| ≤ d * (2 * Real.sqrt Q + d) ∧
      W ≤ (Real.sqrt Q + d) ^ 2 := by
  simpa only [Real.sq_sqrt hW, Real.sq_sqrt hQ] using
    squared_comparison_of_abs_sub_le (Real.sqrt_nonneg W)
      (Real.sqrt_nonneg Q) hd h

/-- Squared-norm comparison in an arbitrary normed additive group. In the
manuscript the group will be a Hilbert--Schmidt operator space. -/
theorem variance_norm_comparison {F : Type*} [SeminormedAddCommGroup F]
    (x y : F) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ ‖x - y‖ * (2 * ‖y‖ + ‖x - y‖) ∧
      ‖x‖ ^ 2 ≤ (‖y‖ + ‖x - y‖) ^ 2 :=
  squared_comparison_of_abs_sub_le (norm_nonneg x) (norm_nonneg y)
    (norm_nonneg (x - y)) (abs_norm_sub_norm_le x y)

/-- Quantitative variance comparison with explicit constant
`C_E = 2 * (1 + E^2)`. The trace and square-root bounds are premises;
this theorem does not assert their operator-theoretic derivation. -/
theorem quantitative_variance_comparison {a W Q N E δ d : ℝ}
    (hW : 0 ≤ W) (hQ : 0 ≤ Q) (hN : 0 ≤ N) (hd : 0 ≤ d)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4)
    (htrace : |a - W| ≤ δ * (a + E ^ 2 * N))
    (hsqrt : |Real.sqrt W - Real.sqrt Q| ≤ d) :
    |a - Q| ≤ d * (2 * Real.sqrt Q + d) +
      (2 * (1 + E ^ 2)) * δ * ((Real.sqrt Q + d) ^ 2 + N) := by
  obtain ⟨hWdiff, hWupper⟩ := variance_sqrt_comparison hW hQ hd hsqrt
  have habsorb := variance_error_absorption hW hN hδ hδsmall htrace
  have hWupper' : W + E ^ 2 * N ≤
      (1 + E ^ 2) * ((Real.sqrt Q + d) ^ 2 + N) := by
    nlinarith [mul_nonneg (sq_nonneg E) (sq_nonneg (Real.sqrt Q + d))]
  have hscale := mul_le_mul_of_nonneg_left hWupper' (by positivity : 0 ≤ 2 * δ)
  have htri : |a - Q| ≤ |a - W| + |W - Q| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (a - W) (W - Q)
  nlinarith

end KernelSeq
