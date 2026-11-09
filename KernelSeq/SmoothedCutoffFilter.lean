import KernelSeq.SmoothResidualFilter
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact

/-!
# Smoothed spectral cutoffs

Every cutoff satisfying the manuscript's stated `C¹`, monotonicity, range and
plateau conditions gives an admissible scale-regular filter. The derivative
bound and all regularity estimates are derived here, rather than supplied as
an additional filter certificate.
-/

namespace KernelSeq.ResidualFilter

open MeasureTheory Set
noncomputable section

/-- The regularity, monotonicity, range, and support conditions on a smooth cutoff. -/
structure SmoothCutoffProfile (χ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 χ
  monotone : Monotone χ
  range : ∀ u, χ u ∈ Icc (0 : ℝ) 1
  below : ∀ u, u ≤ 1 → χ u = 0
  above : ∀ u, 2 ≤ u → χ u = 1

def smoothedCutoff (lam : ℝ) (χ : ℝ → ℝ) (t : ℝ) : ℝ := χ (t / lam) / t

/-- An actual scalar bound obtained from the derivative on the compact
transition interval; no derivative bound is part of `SmoothCutoffProfile`. -/
def cutoffDerivativeBound (χ : ℝ → ℝ) : ℝ :=
  max 0 (sSup ((fun u => |deriv χ u|) '' Icc (1 : ℝ) 2))

theorem cutoffDerivativeBound_nonneg (χ : ℝ → ℝ) : 0 ≤ cutoffDerivativeBound χ := le_max_left _ _

private theorem SmoothCutoffProfile.deriv_eq_zero_of_plateau {χ : ℝ → ℝ}
    (hχ : SmoothCutoffProfile χ) {u : ℝ} (hu : u ≤ 1 ∨ 2 ≤ u) : deriv χ u = 0 := by
  rcases hu with hu | hu
  · apply IsLocalMin.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun x => by
      rw [hχ.below u hu]
      exact (hχ.range x).1)
  · apply IsLocalMax.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun x => by
      rw [hχ.above u hu]
      exact (hχ.range x).2)

theorem SmoothCutoffProfile.deriv_le_bound {χ : ℝ → ℝ} (hχ : SmoothCutoffProfile χ) (u : ℝ) :
    |deriv χ u| ≤ cutoffDerivativeBound χ := by
  by_cases hu : u ∈ Icc (1 : ℝ) 2
  · have hb : BddAbove ((fun u => |deriv χ u|) '' Icc (1 : ℝ) 2) :=
      isCompact_Icc.bddAbove_image hχ.contDiff.continuous_deriv_one.abs.continuousOn
    exact (le_csSup hb ⟨u, hu, rfl⟩).trans (le_max_right _ _)
  · rw [hχ.deriv_eq_zero_of_plateau (by
      simp only [mem_Icc, not_and_or, not_le] at hu
      exact hu.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)), abs_zero]
    exact cutoffDerivativeBound_nonneg _

theorem smoothedCutoff_eq_zero_of_le {lam : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : SmoothCutoffProfile χ) {t : ℝ} (ht : t ≤ lam) :
    smoothedCutoff lam χ t = 0 := by
  simp [smoothedCutoff, hχ.below (t / lam) ((div_le_one hlam).2 ht)]

theorem smoothedCutoff_shrinkage {lam : ℝ} {χ : ℝ → ℝ}
    (_hlam : 0 < lam) (hχ : SmoothCutoffProfile χ) (t : ℝ) :
    shrinkage (smoothedCutoff lam χ) t = χ (t / lam) := by
  by_cases ht : t = 0
  · subst t
    simp [shrinkage, hχ.below 0 (by norm_num)]
  · unfold shrinkage smoothedCutoff
    field_simp

theorem smoothedCutoff_residual {lam : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : SmoothCutoffProfile χ) (t : ℝ) :
    residual (smoothedCutoff lam χ) t = 1 - χ (t / lam) := by
  rw [residual, smoothedCutoff_shrinkage hlam hχ]

theorem smoothedCutoff_spectralFilter {lam M : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : SmoothCutoffProfile χ) :
    SpectralFilter M (smoothedCutoff lam χ) := by
  constructor
  · exact ((hχ.contDiff.continuous.comp (continuous_id.div_const lam)).measurable.div
      measurable_id).comp measurable_subtype_coe
  · intro t ht
    exact div_nonneg (hχ.range _).1 ht.1
  · intro t _
    rw [smoothedCutoff_shrinkage hlam hχ]
    exact hχ.range _

theorem smoothedCutoff_inverse_size {lam : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : SmoothCutoffProfile χ) {t : ℝ} :
    (t + lam) * smoothedCutoff lam χ t ≤ 2 := by
  by_cases htl : t ≤ lam
  · simp [smoothedCutoff_eq_zero_of_le hlam hχ htl]
  · have htp : 0 < t := hlam.trans (lt_of_not_ge htl)
    have hq : χ (t / lam) / t ≤ 1 / t :=
      div_le_div_of_nonneg_right (hχ.range _).2 htp.le
    calc
      _ ≤ (t + lam) * (1 / t) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ 2 := by rw [mul_one_div]; apply (div_le_iff₀ htp).2; linarith

theorem smoothedCutoff_residual_contDiff {lam : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : SmoothCutoffProfile χ) :
    ContDiff ℝ 1 (residual (smoothedCutoff lam χ)) := by
  have heq : residual (smoothedCutoff lam χ) = fun t => 1 - χ (t / lam) :=
    funext (smoothedCutoff_residual hlam hχ)
  rw [heq]
  exact contDiff_const.sub (hχ.contDiff.comp (contDiff_id.div_const lam))

theorem smoothedCutoff_residual_deriv {lam : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : SmoothCutoffProfile χ) (t : ℝ) :
    deriv (residual (smoothedCutoff lam χ)) t = -(deriv χ (t / lam) / lam) := by
  have heq : residual (smoothedCutoff lam χ) = fun t => 1 - χ (t / lam) :=
    funext (smoothedCutoff_residual hlam hχ)
  rw [heq]
  have hd : HasDerivAt χ (deriv χ (t / lam)) (t / lam) :=
    (hχ.contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hh := (hd.comp t ((hasDerivAt_id t).div_const lam)).const_sub 1
  simpa only [one_div, div_eq_mul_inv, Function.comp_apply, id_eq, mul_one, mul_comm] using hh.deriv

def smoothedCutoffSmoothConstant (χ : ℝ → ℝ) : ℝ := 3 + 9 * cutoffDerivativeBound χ

theorem smoothedCutoff_combined_bound {lam : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : SmoothCutoffProfile χ) {t : ℝ} (ht : 0 ≤ t) :
    |residual (smoothedCutoff lam χ) t| +
      (t + lam) * |deriv (residual (smoothedCutoff lam χ)) t| ≤
        smoothedCutoffSmoothConstant χ * (lam / (t + lam)) ^ (1 : ℝ) := by
  rw [smoothedCutoff_residual hlam hχ, smoothedCutoff_residual_deriv hlam hχ,
    Real.rpow_one, abs_neg, abs_div, abs_of_pos hlam]
  have hq := hχ.range (t / lam)
  rw [abs_of_nonneg (sub_nonneg.mpr hq.2)]
  have hK := cutoffDerivativeBound_nonneg χ
  have hder := hχ.deriv_le_bound (t / lam)
  have hden : 0 < t + lam := add_pos_of_nonneg_of_pos ht hlam
  by_cases htt : t ≤ 2 * lam
  · have hbd : 1 - χ (t / lam) + (t + lam) * (|deriv χ (t / lam)| / lam) ≤
        1 + 3 * cutoffDerivativeBound χ := by
      have hd : |deriv χ (t / lam)| / lam ≤ cutoffDerivativeBound χ / lam :=
        div_le_div_of_nonneg_right hder hlam.le
      have hdm := mul_le_mul_of_nonneg_left hd hden.le
      have h3 : (t + lam) * (cutoffDerivativeBound χ / lam) ≤ 3 * cutoffDerivativeBound χ := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hlam).2
        nlinarith
      linarith [hq.1]
    have hfac : 1 + 3 * cutoffDerivativeBound χ ≤
        smoothedCutoffSmoothConstant χ * (lam / (t + lam)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hden).2
      unfold smoothedCutoffSmoothConstant
      nlinarith
    exact hbd.trans hfac
  · have hz : 2 ≤ t / lam := (le_div_iff₀ hlam).2 (by linarith)
    rw [hχ.above _ hz, hχ.deriv_eq_zero_of_plateau (Or.inr hz)]
    simp only [sub_self, abs_zero, zero_div, mul_zero, add_zero]
    unfold smoothedCutoffSmoothConstant
    positivity

/-- The original smooth-condition constant is derived solely from `χ`, and is
uniform in the regularization and spectral interval, including `M=0`. -/
theorem smoothedCutoff_contract {lam M : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hχ : SmoothCutoffProfile χ) :
    Contract lam M 1 (2 * smoothedCutoffSmoothConstant χ) (smoothedCutoff lam χ) := by
  have hB : 1 ≤ smoothedCutoffSmoothConstant χ := by
    unfold smoothedCutoffSmoothConstant
    linarith [cutoffDerivativeBound_nonneg χ]
  have hB2 : 2 ≤ smoothedCutoffSmoothConstant χ := by
    unfold smoothedCutoffSmoothConstant
    linarith [cutoffDerivativeBound_nonneg χ]
  have h := contract_of_smooth_condition_nonnegative_interval
    (B := smoothedCutoffSmoothConstant χ) hlam hM (by norm_num : (0 : ℝ) < 1)
    (smoothedCutoff_spectralFilter hlam hχ)
    (smoothedCutoff_residual_contDiff hlam hχ).contDiffOn.absolutelyContinuousOnInterval
    (fun t _ => (smoothedCutoff_inverse_size hlam hχ).trans hB2)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact smoothedCutoff_combined_bound hlam hχ ht.1)
  simpa only [max_eq_left hB, max_eq_left (by norm_num : (1 : ℝ) ≤ 2), mul_comm] using h

end
end KernelSeq.ResidualFilter
