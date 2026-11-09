import KernelSeq.ResidualFilter
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Every positive real residual order is admissible

The inverse is the divided difference of the power residual, with its
removable value at zero. Bernoulli's inequality proves its inverse bound. The weighted
residual is identically one. In particular, orders below one half are
included without an additional regularity premise.
-/

namespace KernelSeq.ResidualFilter
open Set
open scoped Topology
noncomputable section

def powerResidual (lam ρ t : ℝ) : ℝ := (lam / (t + lam)) ^ ρ

def powerResidualInverse (lam ρ t : ℝ) : ℝ := -dslope (powerResidual lam ρ) 0 t

private theorem powerResidual_hasDerivAt {lam ρ t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    HasDerivAt (powerResidual lam ρ)
      ((-(lam / (t + lam) ^ 2)) * ρ * (lam / (t + lam)) ^ (ρ - 1)) t := by
  have hd : 0 < t + lam := add_pos_of_nonneg_of_pos ht hlam
  have hh := ((hasDerivAt_const t lam).div ((hasDerivAt_id t).add_const lam) hd.ne').rpow_const
    (p := ρ) (Or.inl (ne_of_gt (div_pos hlam hd)))
  simp only [id_eq, Pi.div_apply, zero_mul, zero_sub] at hh
  convert hh using 1 <;> first | rfl | ring

theorem powerResidualInverse_zero {lam ρ : ℝ} (hlam : 0 < lam) :
    powerResidualInverse lam ρ 0 = ρ / lam := by
  rw [powerResidualInverse, dslope_same, (powerResidual_hasDerivAt (ρ := ρ) hlam le_rfl).deriv]
  simp only [zero_add, div_self hlam.ne', Real.one_rpow, mul_one]
  field_simp

theorem powerResidualInverse_of_ne_zero {lam ρ t : ℝ} (hlam : 0 < lam) (ht : t ≠ 0) :
    powerResidualInverse lam ρ t = (1 - powerResidual lam ρ t) / t := by
  rw [powerResidualInverse, dslope_of_ne _ ht]
  simp only [slope_def_field, sub_zero, powerResidual, zero_add, div_self hlam.ne', Real.one_rpow]
  ring

theorem powerResidualInverse_residual {lam ρ : ℝ} (hlam : 0 < lam) (t : ℝ) :
    residual (powerResidualInverse lam ρ) t = powerResidual lam ρ t := by
  have hh := sub_smul_dslope (powerResidual lam ρ) 0 t
  have hz : powerResidual lam ρ 0 = 1 := by simp [powerResidual, hlam.ne']
  simp only [sub_zero, smul_eq_mul, hz] at hh
  unfold residual shrinkage powerResidualInverse
  linarith

private theorem powerResidual_continuousAt {lam ρ t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    ContinuousAt (powerResidual lam ρ) t := (powerResidual_hasDerivAt (ρ := ρ) hlam ht).continuousAt

theorem powerResidualInverse_spectralFilter {lam M ρ : ℝ} (hlam : 0 < lam) (hρ : 0 < ρ) :
    SpectralFilter M (powerResidualInverse lam ρ) := by
  have hrange (t : ℝ) (ht : 0 ≤ t) : powerResidual lam ρ t ∈ Icc (0 : ℝ) 1 := by
    have hd : 0 < t + lam := add_pos_of_nonneg_of_pos ht hlam
    exact ⟨Real.rpow_nonneg (div_nonneg hlam.le hd.le) _,
      Real.rpow_le_one (div_nonneg hlam.le hd.le) ((div_le_one hd).2 (le_add_of_nonneg_left ht)) hρ.le⟩
  constructor
  · apply Continuous.measurable
    change Continuous ((Icc (0 : ℝ) M).restrict (powerResidualInverse lam ρ))
    rw [← continuousOn_iff_continuous_restrict]
    intro t ht
    apply ContinuousAt.continuousWithinAt
    unfold powerResidualInverse
    apply ContinuousAt.neg
    by_cases ht0 : t = 0
    · subst t
      exact continuousAt_dslope_same.mpr (powerResidual_hasDerivAt (ρ := ρ) hlam le_rfl).differentiableAt
    · exact (continuousAt_dslope_of_ne ht0).mpr (powerResidual_continuousAt hlam ht.1)
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [powerResidualInverse_zero hlam]
      positivity
    · rw [powerResidualInverse_of_ne_zero hlam ht0]
      exact div_nonneg (sub_nonneg.mpr (hrange t ht.1).2) ht.1
  · intro t ht
    have hh := powerResidualInverse_residual (ρ := ρ) hlam t
    unfold residual at hh
    have hr := hrange t ht.1
    exact ⟨by linarith [hr.2], by linarith [hr.1]⟩

private theorem one_sub_rpow_bound {r ρ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (_hρ : 0 < ρ) :
    1 - r ^ ρ ≤ max ρ 1 * (1 - r) := by
  rcases le_total ρ 1 with hρ1 | h1ρ
  · rw [max_eq_right hρ1, one_mul]
    linarith [Real.self_le_rpow_of_le_one hr0 hr1 hρ1]
  · rw [max_eq_left h1ρ]
    have hh := one_add_mul_self_le_rpow_one_add (by linarith : -1 ≤ r - 1) h1ρ
    simp only [add_sub_cancel] at hh
    linarith

theorem powerResidualInverse_inverse_bound {lam ρ t : ℝ}
    (hlam : 0 < lam) (hρ : 0 < ρ) (ht : 0 ≤ t) :
    (t + lam) * powerResidualInverse lam ρ t ≤ max ρ 1 := by
  by_cases ht0 : t = 0
  · subst t
    rw [zero_add, powerResidualInverse_zero hlam]
    simpa only [mul_div_cancel₀ _ hlam.ne'] using le_max_left ρ 1
  · have htP : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hd : 0 < t + lam := add_pos_of_nonneg_of_pos ht hlam
    have hr0 : 0 ≤ lam / (t + lam) := div_nonneg hlam.le hd.le
    have hr1 : lam / (t + lam) ≤ 1 := (div_le_one hd).2 (le_add_of_nonneg_left ht)
    have hh := one_sub_rpow_bound hr0 hr1 hρ
    rw [powerResidualInverse_of_ne_zero hlam ht0, powerResidual]
    rw [← mul_div_assoc, div_le_iff₀ htP]
    have heq : (t + lam) * (1 - lam / (t + lam)) = t := by field_simp; ring
    have hh' := mul_le_mul_of_nonneg_left hh hd.le
    calc
      _ ≤ (t + lam) * (max ρ 1 * (1 - lam / (t + lam))) := hh'
      _ = max ρ 1 * t := by rw [mul_left_comm, heq]

theorem powerResidualInverse_weightedResidual {lam ρ : ℝ} (hlam : 0 < lam) (u : ℝ) :
    weightedResidual lam ρ (powerResidualInverse lam ρ) u = 1 := by
  rw [weightedResidual, powerResidualInverse_residual hlam, powerResidual]
  have hd : spectralCoordinate lam u + lam = lam * Real.exp u := by unfold spectralCoordinate; ring
  have hdP : 0 < spectralCoordinate lam u + lam := by rw [hd]; positivity
  rw [← Real.mul_rpow (div_nonneg hdP.le hlam.le) (div_nonneg hlam.le hdP.le)]
  have : ((spectralCoordinate lam u + lam) / lam) *
      (lam / (spectralCoordinate lam u + lam)) = 1 := by field_simp
  rw [this, Real.one_rpow]

/-- The complete positive-order family, with uniform constant `max ρ 1+1`. -/
theorem powerResidualInverse_contract {lam M ρ : ℝ}
    (hlam : 0 < lam) (hρ : 0 < ρ) :
    Contract lam M ρ (max ρ 1 + 1) (powerResidualInverse lam ρ) := by
  constructor
  · exact hρ
  · intro u hu
    have ht : 0 ≤ spectralCoordinate lam u := spectralCoordinate_nonneg hlam.le hu.1
    have hnonneg := (powerResidualInverse_spectralFilter (M := spectralCoordinate lam u) hlam hρ).nonneg
      _ ⟨ht, le_rfl⟩
    have hF0 : 0 ≤ inverseProfile lam (powerResidualInverse lam ρ) u :=
      mul_nonneg (add_nonneg ht hlam.le) hnonneg
    rw [abs_of_nonneg hF0, powerResidualInverse_weightedResidual hlam, abs_one]
    simpa only [inverseProfile] using (add_le_add_left (powerResidualInverse_inverse_bound hlam hρ ht) 1)
  · intro u _ v _
    rw [powerResidualInverse_weightedResidual hlam, powerResidualInverse_weightedResidual hlam]
    simp only [sub_self, abs_zero]
    positivity

end
end KernelSeq.ResidualFilter
