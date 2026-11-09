import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar relative risk comparison

Pointwise and arbitrary-index supremum forms of scalar quadratic risk transfer.
The variance scale is strictly positive; the bias is allowed to vanish.
-/

namespace KernelSeq

/-- The uniform upper bound in the scalar risk-transfer lemma. -/
noncomputable def relativeRiskBound (u v V : ℝ) : ℝ :=
  2 * u + u ^ 2 + (1 + u) * v / Real.sqrt V + v ^ 2 / V

/-- The scalar comparison, with the manuscript's complete hypotheses. -/
theorem scalar_quadratic_risk_transfer (b d u v V : ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hV : 0 < V) (h : d ≤ u * b + v) :
    (2 * b * d + d ^ 2) / (b ^ 2 + V) ≤ relativeRiskBound u v V := by
  have hden : 0 < b ^ 2 + V := add_pos_of_nonneg_of_pos (sq_nonneg b) hV
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hs_sq : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hnum : 2 * b * d + d ^ 2 ≤
      (2 * u + u ^ 2) * b ^ 2 + 2 * (1 + u) * b * v + v ^ 2 := by
    have hlinear := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * b by positivity)
    have hquadratic := mul_le_mul_of_nonneg_left h
      (show 0 ≤ u * b + v + d by positivity)
    nlinarith only [hlinear, hquadratic]
  have hb_ratio : b ^ 2 / (b ^ 2 + V) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hcross_ratio : 2 * b / (b ^ 2 + V) ≤ 1 / Real.sqrt V := by
    apply (div_le_div_iff₀ hden hs).2
    nlinarith only [sq_nonneg (b - Real.sqrt V), hs_sq]
  have hinv_ratio : 1 / (b ^ 2 + V) ≤ 1 / V := by
    apply (div_le_div_iff₀ hden hV).2
    nlinarith only [sq_nonneg b]
  calc
    (2 * b * d + d ^ 2) / (b ^ 2 + V) ≤
        ((2 * u + u ^ 2) * b ^ 2 + 2 * (1 + u) * b * v + v ^ 2) /
          (b ^ 2 + V) := div_le_div_of_nonneg_right hnum hden.le
    _ = (2 * u + u ^ 2) * (b ^ 2 / (b ^ 2 + V)) +
        ((1 + u) * v) * (2 * b / (b ^ 2 + V)) +
        v ^ 2 * (1 / (b ^ 2 + V)) := by ring
    _ ≤ (2 * u + u ^ 2) * 1 +
        ((1 + u) * v) * (1 / Real.sqrt V) + v ^ 2 * (1 / V) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hb_ratio (by positivity))
          (mul_le_mul_of_nonneg_left hcross_ratio (by positivity)))
        (mul_le_mul_of_nonneg_left hinv_ratio (sq_nonneg v))
    _ = relativeRiskBound u v V := by unfold relativeRiskBound; ring

/-- The value set has an upper bound even when the index type is infinite. -/
theorem scalar_quadratic_risk_bddAbove {Θ : Type*} (b d : Θ → ℝ) (u v V : ℝ)
    (hb : ∀ θ, 0 ≤ b θ) (hd : ∀ θ, 0 ≤ d θ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hV : 0 < V)
    (h : ∀ θ, d θ ≤ u * b θ + v) :
    BddAbove (Set.range (fun θ => (2 * b θ * d θ + d θ ^ 2) / (b θ ^ 2 + V))) := by
  refine ⟨relativeRiskBound u v V, ?_⟩
  rintro _ ⟨θ, rfl⟩
  exact scalar_quadratic_risk_transfer _ _ _ _ _ (hb θ) (hd θ) hu hv hV (h θ)

/-- The exact nonempty-index supremum statement in the manuscript. -/
theorem scalar_quadratic_risk_transfer_uniform {Θ : Type*} [Nonempty Θ]
    (b d : Θ → ℝ) (u v V : ℝ)
    (hb : ∀ θ, 0 ≤ b θ) (hd : ∀ θ, 0 ≤ d θ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hV : 0 < V)
    (h : ∀ θ, d θ ≤ u * b θ + v) :
    sSup (Set.range (fun θ => (2 * b θ * d θ + d θ ^ 2) / (b θ ^ 2 + V))) ≤
      relativeRiskBound u v V := by
  have hbounded := scalar_quadratic_risk_bddAbove b d u v V hb hd hu hv hV h
  apply (csSup_le_iff hbounded (Set.range_nonempty _)).2
  rintro _ ⟨θ, rfl⟩
  exact scalar_quadratic_risk_transfer _ _ _ _ _ (hb θ) (hd θ) hu hv hV (h θ)

end KernelSeq
