import KernelSeq.SmoothedCutoffFilter
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The original smooth spherical cutoff with partial retention

The transition profile has the exact plateaus and value at one from the
high-dimensional construction. A genuine smooth witness is provided for
every weight in `[0,1]`, and any profile with these properties satisfies the
original residual contract with a constant independent of the scale.
-/

namespace KernelSeq.ResidualFilter

open MeasureTheory Set
open scoped ContDiff
noncomputable section

structure PhaseCutoffProfile (w : ℝ) (χ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ χ
  monotone : Monotone χ
  range : ∀ u, χ u ∈ Icc (0 : ℝ) 1
  below : ∀ u, u ≤ 1/2 → χ u = 0
  at_one : χ 1 = w
  above : ∀ u, 2 ≤ u → χ u = 1

def phaseCutoffProfile (w u : ℝ) : ℝ :=
  w*Real.smoothTransition (2*u-1)+(1-w)*Real.smoothTransition (u-1)

theorem phaseCutoffProfile_isProfile {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    PhaseCutoffProfile w (phaseCutoffProfile w) := by
  constructor
  · have h1 : ContDiff ℝ ∞ (fun u : ℝ => Real.smoothTransition (2*u-1)) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    have h2 : ContDiff ℝ ∞ (fun u : ℝ => Real.smoothTransition (u-1)) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    exact (contDiff_const.mul h1).add (contDiff_const.mul h2)
  · intro u v huv
    exact add_le_add
      (mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone (by linarith : 2*u-1 ≤ 2*v-1)) hw0)
      (mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone (by linarith : u-1 ≤ v-1)) (sub_nonneg.mpr hw1))
  · intro u
    unfold phaseCutoffProfile
    constructor
    · exact add_nonneg (mul_nonneg hw0 (Real.smoothTransition.nonneg _))
        (mul_nonneg (sub_nonneg.mpr hw1) (Real.smoothTransition.nonneg _))
    · have h1 := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (2*u-1)) hw0
      have h2 := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (u-1)) (sub_nonneg.mpr hw1)
      linarith
  · intro u hu
    rw [phaseCutoffProfile, Real.smoothTransition.zero_of_nonpos (by linarith : 2*u-1 ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : u-1 ≤ 0), mul_zero, mul_zero, add_zero]
  · norm_num [phaseCutoffProfile, Real.smoothTransition.zero, Real.smoothTransition.one]
  · intro u hu
    rw [phaseCutoffProfile, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2*u-1),
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ u-1), mul_one, mul_one]
    ring

theorem phaseCutoff_shrinkage {lam w : ℝ} {χ : ℝ → ℝ}
    (hχ : PhaseCutoffProfile w χ) (t : ℝ) :
    shrinkage (smoothedCutoff lam χ) t = χ (t/lam) := by
  by_cases ht : t = 0
  · subst t
    simp [shrinkage, hχ.below 0 (by norm_num)]
  · unfold shrinkage smoothedCutoff
    field_simp

theorem phaseCutoff_shrinkage_at_scale {lam w : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : PhaseCutoffProfile w χ) :
    shrinkage (smoothedCutoff lam χ) lam = w := by
  rw [phaseCutoff_shrinkage hχ, div_self hlam.ne', hχ.at_one]

theorem phaseCutoff_shrinkage_zero_of_le_half {lam w t : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : PhaseCutoffProfile w χ) (ht : t ≤ lam/2) :
    shrinkage (smoothedCutoff lam χ) t = 0 := by
  rw [phaseCutoff_shrinkage hχ]
  exact hχ.below _ ((div_le_iff₀ hlam).mpr (by linarith))

theorem phaseCutoff_shrinkage_one_of_ge_twice {lam w t : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : PhaseCutoffProfile w χ) (ht : 2*lam ≤ t) :
    shrinkage (smoothedCutoff lam χ) t = 1 := by
  rw [phaseCutoff_shrinkage hχ]
  exact hχ.above _ ((le_div_iff₀ hlam).mpr ht)

theorem phaseCutoff_spectralFilter {lam M w : ℝ} {χ : ℝ → ℝ}
    (hχ : PhaseCutoffProfile w χ) : SpectralFilter M (smoothedCutoff lam χ) := by
  constructor
  · exact ((hχ.contDiff.continuous.comp (continuous_id.div_const lam)).measurable.div
      measurable_id).comp measurable_subtype_coe
  · intro t ht
    exact div_nonneg (hχ.range _).1 ht.1
  · intro t _
    rw [phaseCutoff_shrinkage hχ]
    exact hχ.range _

def phaseCutoffDerivativeBound (χ : ℝ → ℝ) : ℝ :=
  max 0 (sSup ((fun u => |deriv χ u|) '' Icc (1/2 : ℝ) 2))

theorem phaseCutoffDerivativeBound_nonneg (χ : ℝ → ℝ) :
    0 ≤ phaseCutoffDerivativeBound χ := le_max_left _ _

private theorem PhaseCutoffProfile.deriv_plateau {w u : ℝ} {χ : ℝ → ℝ}
    (hχ : PhaseCutoffProfile w χ) (hu : u ≤ 1/2 ∨ 2 ≤ u) : deriv χ u = 0 := by
  rcases hu with hu | hu
  · apply IsLocalMin.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun x => by rw [hχ.below u hu]; exact (hχ.range x).1)
  · apply IsLocalMax.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun x => by rw [hχ.above u hu]; exact (hχ.range x).2)

theorem PhaseCutoffProfile.deriv_le_bound {w : ℝ} {χ : ℝ → ℝ}
    (hχ : PhaseCutoffProfile w χ) (u : ℝ) : |deriv χ u| ≤ phaseCutoffDerivativeBound χ := by
  have hC1 : ContDiff ℝ 1 χ := hχ.contDiff.of_le (by norm_num)
  by_cases hu : u ∈ Icc (1/2 : ℝ) 2
  · have hb : BddAbove ((fun u => |deriv χ u|) '' Icc (1/2 : ℝ) 2) :=
      isCompact_Icc.bddAbove_image hC1.continuous_deriv_one.abs.continuousOn
    exact (le_csSup hb ⟨u,hu,rfl⟩).trans (le_max_right _ _)
  · rw [hχ.deriv_plateau (by
      simp only [mem_Icc, not_and_or, not_le] at hu
      exact hu.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)), abs_zero]
    exact phaseCutoffDerivativeBound_nonneg _

theorem phaseCutoff_inverse_size {lam w t : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : PhaseCutoffProfile w χ) :
    (t+lam)*smoothedCutoff lam χ t ≤ 3 := by
  by_cases ht : t ≤ lam/2
  · rw [smoothedCutoff, hχ.below _ ((div_le_iff₀ hlam).mpr (by linarith)), zero_div, mul_zero]
    norm_num
  · have htp : 0 < t := by linarith
    have hq := div_le_div_of_nonneg_right (hχ.range (t/lam)).2 htp.le
    unfold smoothedCutoff
    exact (mul_le_mul_of_nonneg_left hq (by positivity)).trans (by
      rw [mul_one_div]
      exact (div_le_iff₀ htp).mpr (by linarith))

theorem phaseCutoff_residual_contDiff {lam w : ℝ} {χ : ℝ → ℝ}
    (hχ : PhaseCutoffProfile w χ) : ContDiff ℝ 1 (residual (smoothedCutoff lam χ)) := by
  have he : residual (smoothedCutoff lam χ) = fun t => 1-χ (t/lam) :=
    funext (fun t => by rw [residual, phaseCutoff_shrinkage hχ])
  rw [he]
  exact contDiff_const.sub ((hχ.contDiff.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).comp (contDiff_id.div_const lam))

theorem phaseCutoff_residual_deriv {lam w : ℝ} {χ : ℝ → ℝ}
    (hχ : PhaseCutoffProfile w χ) (t : ℝ) :
    deriv (residual (smoothedCutoff lam χ)) t = -(deriv χ (t/lam)/lam) := by
  have he : residual (smoothedCutoff lam χ) = fun t => 1-χ (t/lam) :=
    funext (fun t => by rw [residual, phaseCutoff_shrinkage hχ])
  rw [he]
  have hd : HasDerivAt χ (deriv χ (t/lam)) (t/lam) :=
    (hχ.contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  simpa only [one_div, div_eq_mul_inv, Function.comp_apply, id_eq, mul_one, mul_comm] using
    ((hd.comp t ((hasDerivAt_id t).div_const lam)).const_sub 1).deriv

def phaseCutoffSmoothConstant (χ : ℝ → ℝ) : ℝ := 3+9*phaseCutoffDerivativeBound χ

def phaseCutoffContractConstant (χ : ℝ → ℝ) : ℝ := 2*phaseCutoffSmoothConstant χ

theorem phaseCutoff_combined_bound {lam w t : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hχ : PhaseCutoffProfile w χ) (ht : 0 ≤ t) :
    |residual (smoothedCutoff lam χ) t|+(t+lam)*|deriv (residual (smoothedCutoff lam χ)) t| ≤
      phaseCutoffSmoothConstant χ*(lam/(t+lam))^(1:ℝ) := by
  rw [phaseCutoff_residual_deriv hχ, residual, phaseCutoff_shrinkage hχ, Real.rpow_one,
    abs_neg, abs_div, abs_of_pos hlam]
  have hq := hχ.range (t/lam)
  rw [abs_of_nonneg (sub_nonneg.mpr hq.2)]
  have hK := phaseCutoffDerivativeBound_nonneg χ
  have hden : 0 < t+lam := by positivity
  by_cases htt : t ≤ 2*lam
  · have hder := div_le_div_of_nonneg_right (hχ.deriv_le_bound (t/lam)) hlam.le
    have hmul := mul_le_mul_of_nonneg_left hder hden.le
    have h3 : (t+lam)*(phaseCutoffDerivativeBound χ/lam) ≤ 3*phaseCutoffDerivativeBound χ := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hlam).mpr
      nlinarith
    calc
      _ ≤ 1+3*phaseCutoffDerivativeBound χ := by linarith [hq.1]
      _ ≤ _ := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hden).mpr
        unfold phaseCutoffSmoothConstant
        nlinarith
  · have hz : 2 ≤ t/lam := (le_div_iff₀ hlam).mpr (by linarith)
    rw [hχ.above _ hz,hχ.deriv_plateau (Or.inr hz),sub_self,abs_zero,zero_div,mul_zero,add_zero]
    unfold phaseCutoffSmoothConstant
    positivity

theorem phaseCutoff_contract {lam M w : ℝ} {χ : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hχ : PhaseCutoffProfile w χ) :
    Contract lam M 1 (phaseCutoffContractConstant χ) (smoothedCutoff lam χ) := by
  have hB : 3 ≤ phaseCutoffSmoothConstant χ := by
    unfold phaseCutoffSmoothConstant
    linarith [phaseCutoffDerivativeBound_nonneg χ]
  have hh := contract_of_smooth_condition_nonnegative_interval
    (B := phaseCutoffSmoothConstant χ) hlam hM (by norm_num : (0:ℝ)<1)
    (phaseCutoff_spectralFilter hχ)
    (phaseCutoff_residual_contDiff hχ).contDiffOn.absolutelyContinuousOnInterval
    (fun t _ => (phaseCutoff_inverse_size hlam hχ).trans hB)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact phaseCutoff_combined_bound hlam hχ ht.1)
  simpa only [phaseCutoffContractConstant, max_eq_left (by linarith : 1 ≤ phaseCutoffSmoothConstant χ),
    max_eq_left (by norm_num : (1:ℝ)≤2), mul_comm] using hh

end
end KernelSeq.ResidualFilter
