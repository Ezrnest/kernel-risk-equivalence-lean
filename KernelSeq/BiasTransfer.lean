import KernelSeq.ScalarRisk
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Deterministic bias transfer

Squared-norm perturbation and normalized comparison for bias transfer.
These statements hold in any normed additive commutative group, hence in the
manuscript's real Hilbert space. They do not assume the bias is nonzero.
The operator interaction estimate and probabilistic hypotheses remain upstream.
-/

namespace KernelSeq

/-- Squaring two nonnegative numbers whose difference is controlled. -/
theorem abs_sq_sub_sq_le (a b d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : 0 ≤ d) (hab : |a - b| ≤ d) :
    |a ^ 2 - b ^ 2| ≤ 2 * b * d + d ^ 2 := by
  calc
    |a ^ 2 - b ^ 2| = |a - b| * (a + b) := by
      rw [← abs_of_nonneg (add_nonneg ha hb), ← abs_mul]
      congr 1
      ring
    _ ≤ d * (a + b) := mul_le_mul_of_nonneg_right hab (add_nonneg ha hb)
    _ ≤ d * (2 * b + d) := by
      apply mul_le_mul_of_nonneg_left _ hd
      linarith [(abs_le.mp hab).2]
    _ = 2 * b * d + d ^ 2 := by ring

/-- Squared-norm perturbation, the first step of the manuscript's bias proof. -/
theorem norm_sq_perturbation {E : Type*} [NormedAddCommGroup E] (r e : E) :
    |‖r - e‖ ^ 2 - ‖r‖ ^ 2| ≤ 2 * ‖r‖ * ‖e‖ + ‖e‖ ^ 2 := by
  apply abs_sq_sub_sq_le _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have h := abs_norm_sub_norm_le (r - e) r
  simpa only [sub_sub_cancel_left, norm_neg] using h

/-- Total-risk normalization of the bias perturbation, with explicit error coefficients. -/
theorem bias_relative_risk_bound {E : Type*} [NormedAddCommGroup E]
    (r e : E) (u v V : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hV : 0 < V)
    (he : ‖e‖ ≤ u * ‖r‖ + v) :
    |‖r - e‖ ^ 2 - ‖r‖ ^ 2| / (‖r‖ ^ 2 + V) ≤ relativeRiskBound u v V := by
  calc
    |‖r - e‖ ^ 2 - ‖r‖ ^ 2| / (‖r‖ ^ 2 + V) ≤
        (2 * ‖r‖ * ‖e‖ + ‖e‖ ^ 2) / (‖r‖ ^ 2 + V) :=
      div_le_div_of_nonneg_right (norm_sq_perturbation r e) (by positivity)
    _ ≤ relativeRiskBound u v V :=
      scalar_quadratic_risk_transfer _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
        hu hv hV he

/-- Uniform bias comparison with common coefficients over any nonempty target family. -/
theorem bias_relative_risk_bound_uniform {Θ E : Type*} [Nonempty Θ]
    [NormedAddCommGroup E] (r e : Θ → E) (u v V : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hV : 0 < V)
    (he : ∀ θ, ‖e θ‖ ≤ u * ‖r θ‖ + v) :
    sSup (Set.range (fun θ =>
      |‖r θ - e θ‖ ^ 2 - ‖r θ‖ ^ 2| / (‖r θ‖ ^ 2 + V))) ≤
      relativeRiskBound u v V := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨θ, rfl⟩
  exact bias_relative_risk_bound _ _ _ _ _ hu hv hV (he θ)

end KernelSeq
