import KernelSeq.SmoothResidualFilter
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Generalized ridge with a fixed real exponent

The inverse is `t^(p-1)/(t^p+λ^p)` for every real `p≥1`, with its values at
zero supplied by real powers.
All constants are independent of λ and the spectral upper bound.
-/

namespace KernelSeq.ResidualFilter
open MeasureTheory Set
open scoped Interval
noncomputable section

def generalizedRidge (lam p t : ℝ) : ℝ := t ^ (p - 1) / (t ^ p + lam ^ p)

private theorem mul_rpow_sub_one {p : ℝ} (hp : 0 < p) (t : ℝ) :
    t * t ^ (p - 1) = t ^ p := by
  by_cases ht : t = 0
  · simp [ht, Real.zero_rpow hp.ne']
  · rw [mul_comm, ← Real.rpow_add_one ht]
    congr 1
    ring

theorem generalizedRidge_zero_one {lam : ℝ} : generalizedRidge lam 1 0 = lam⁻¹ := by
  simp [generalizedRidge]

theorem generalizedRidge_one (lam : ℝ) : generalizedRidge lam 1 = ridge lam := by
  ext t
  simp [generalizedRidge, ridge]

theorem generalizedRidge_zero_of_one_lt {lam p : ℝ} (hp : 1 < p) :
    generalizedRidge lam p 0 = 0 := by
  simp [generalizedRidge, Real.zero_rpow (sub_pos.mpr hp).ne']

theorem generalizedRidge_shrinkage {lam p t : ℝ} (hp : 1 ≤ p) :
    shrinkage (generalizedRidge lam p) t = t ^ p / (t ^ p + lam ^ p) := by
  unfold shrinkage generalizedRidge
  rw [← mul_div_assoc, mul_rpow_sub_one (zero_lt_one.trans_le hp)]

theorem generalizedRidge_residual {lam p t : ℝ} (hlam : 0 < lam) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    residual (generalizedRidge lam p) t = lam ^ p / (t ^ p + lam ^ p) := by
  have hd : 0 < t ^ p + lam ^ p := add_pos_of_nonneg_of_pos
    (Real.rpow_nonneg ht _) (Real.rpow_pos_of_pos hlam _)
  rw [residual, generalizedRidge_shrinkage hp]
  field_simp
  ring

theorem generalizedRidge_spectralFilter {lam M p : ℝ} (hlam : 0 < lam) (hp : 1 ≤ p) :
    SpectralFilter M (generalizedRidge lam p) := by
  have hc : Continuous (fun t : ℝ => t ^ (p - 1)) := Real.continuous_rpow_const (sub_nonneg.mpr hp)
  have hc' : Continuous (fun t : ℝ => t ^ p) := Real.continuous_rpow_const (zero_le_one.trans hp)
  have hd : ∀ t : Icc (0 : ℝ) M, (t : ℝ) ^ p + lam ^ p ≠ 0 := fun t =>
    ne_of_gt (add_pos_of_nonneg_of_pos (Real.rpow_nonneg t.property.1 _) (Real.rpow_pos_of_pos hlam _))
  constructor
  · exact ((hc.comp continuous_subtype_val).div
      ((hc'.comp continuous_subtype_val).add continuous_const) hd).measurable
  · intro t ht
    exact div_nonneg (Real.rpow_nonneg ht.1 _) (add_nonneg (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg hlam.le _))
  · intro t ht
    rw [generalizedRidge_shrinkage hp]
    have hd' : 0 < t ^ p + lam ^ p := add_pos_of_nonneg_of_pos
      (Real.rpow_nonneg ht.1 _) (Real.rpow_pos_of_pos hlam _)
    exact ⟨div_nonneg (Real.rpow_nonneg ht.1 _) hd'.le,
      (div_le_one hd').2 (le_add_of_nonneg_right (Real.rpow_nonneg hlam.le _))⟩

/-- The elementary inverse bound uses a split at `t=λ`, including zero. -/
theorem generalizedRidge_inverse_bound {lam p t : ℝ}
    (hlam : 0 < lam) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    (t + lam) * generalizedRidge lam p t ≤ 2 := by
  have htP : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg ht _
  have hLp : 0 ≤ lam ^ p := (Real.rpow_pos_of_pos hlam p).le
  have hd : 0 < t ^ p + lam ^ p := add_pos_of_nonneg_of_pos (Real.rpow_nonneg ht _) (Real.rpow_pos_of_pos hlam _)
  unfold generalizedRidge
  rw [← mul_div_assoc, div_le_iff₀ hd]
  rcases le_total t lam with htl | hlt
  · have hpow := Real.rpow_le_rpow ht htl (sub_nonneg.mpr hp)
    have hid := mul_rpow_sub_one (zero_lt_one.trans_le hp) lam
    have hle : (t + lam) * t ^ (p - 1) ≤ (2 * lam) * lam ^ (p - 1) :=
      mul_le_mul (by linarith) hpow htP (by positivity)
    nlinarith [Real.rpow_nonneg ht p]
  · have hid := mul_rpow_sub_one (zero_lt_one.trans_le hp) t
    have hle : (t + lam) * t ^ (p - 1) ≤ (2 * t) * t ^ (p - 1) :=
      mul_le_mul_of_nonneg_right (by linarith) htP
    nlinarith

private theorem generalizedRidge_power_bound {lam p t : ℝ}
    (hlam : 0 < lam) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    (t + lam) ^ p ≤ (2 : ℝ) ^ (p - 1) * (t ^ p + lam ^ p) := by
  have hh := NNReal.rpow_add_le_mul_rpow_add_rpow (⟨t, ht⟩ : NNReal) (⟨lam, hlam.le⟩ : NNReal) hp
  exact_mod_cast hh

theorem generalizedRidge_residual_bound {lam p t : ℝ}
    (hlam : 0 < lam) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    |residual (generalizedRidge lam p) t| ≤
      (2 : ℝ) ^ (p - 1) * (lam / (t + lam)) ^ p := by
  have hd : 0 < t ^ p + lam ^ p := add_pos_of_nonneg_of_pos
    (Real.rpow_nonneg ht _) (Real.rpow_pos_of_pos hlam _)
  have htlam : 0 < t + lam := add_pos_of_nonneg_of_pos ht hlam
  rw [generalizedRidge_residual hlam hp ht, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hlam.le _) hd.le),
    Real.div_rpow hlam.le htlam.le]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hd (Real.rpow_pos_of_pos htlam p)).2
  convert mul_le_mul_of_nonneg_left (generalizedRidge_power_bound hlam hp ht)
    (Real.rpow_nonneg hlam.le p) using 1; ring

theorem generalizedRidge_residual_absolutelyContinuous {lam M p : ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hp : 1 ≤ p) :
    AbsolutelyContinuousOnInterval (residual (generalizedRidge lam p)) 0 M := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) M, t ^ p + lam ^ p ≠ 0 := by
    intro t ht
    exact ne_of_gt (add_pos_of_nonneg_of_pos (Real.rpow_nonneg ((uIcc_of_le hM ▸ ht).1) _)
      (Real.rpow_pos_of_pos hlam _))
  have hpow : ContDiffOn ℝ 1 (fun t : ℝ => t ^ p) (uIcc 0 M) :=
    (Real.contDiff_rpow_const_of_le (n := 1) (by simpa using hp)).contDiffOn
  have hg : ContDiffOn ℝ 1 (fun t : ℝ => lam ^ p / (t ^ p + lam ^ p)) (uIcc 0 M) :=
    contDiffOn_const.div (hpow.add contDiffOn_const) hd
  exact (hg.congr (fun t ht => generalizedRidge_residual hlam hp ((uIcc_of_le hM ▸ ht).1))).absolutelyContinuousOnInterval

theorem generalizedRidge_residual_hasDerivAt {lam p t : ℝ}
    (hlam : 0 < lam) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    HasDerivAt (residual (generalizedRidge lam p))
      (-(lam ^ p * p * t ^ (p - 1)) / (t ^ p + lam ^ p) ^ 2) t := by
  have hd : 0 < t ^ p + lam ^ p := add_pos_of_nonneg_of_pos
    (Real.rpow_nonneg ht _) (Real.rpow_pos_of_pos hlam _)
  have heq : residual (generalizedRidge lam p) =ᶠ[nhds t]
      (fun x => lam ^ p / (x ^ p + lam ^ p)) := by
    have hh : ∀ᶠ x in nhds t, x ^ p + lam ^ p ≠ 0 :=
      ((Real.continuous_rpow_const (zero_le_one.trans hp)).add continuous_const).continuousAt.eventually_ne hd.ne'
    filter_upwards [hh] with x hx
    rw [residual, generalizedRidge_shrinkage hp]
    field_simp
    ring
  have hg := (hasDerivAt_const t (lam ^ p)).div
    ((Real.hasDerivAt_rpow_const (x := t) (p := p) (Or.inr hp)).add_const (lam ^ p)) hd.ne'
  apply heq.hasDerivAt_iff.mpr
  simp only [zero_mul, zero_sub] at hg
  convert hg using 1 <;> first | rfl | ring

/-- The combined residual/derivative inequality is proved at every admissible
point, which is stronger than the a.e. hypothesis of the general criterion. -/
theorem generalizedRidge_smooth_bound {lam p t : ℝ}
    (hlam : 0 < lam) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    |residual (generalizedRidge lam p) t| +
        (t + lam) * |deriv (residual (generalizedRidge lam p)) t| ≤
      ((1 + 2 * p) * (2 : ℝ) ^ (p - 1)) * (lam / (t + lam)) ^ p := by
  have hpp : 0 < p := zero_lt_one.trans_le hp
  have hLp : 0 < lam ^ p := Real.rpow_pos_of_pos hlam _
  have htp : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg ht _
  have hd : 0 < t ^ p + lam ^ p := add_pos_of_nonneg_of_pos (Real.rpow_nonneg ht _) hLp
  have hψ0 : 0 ≤ residual (generalizedRidge lam p) t := by
    rw [generalizedRidge_residual hlam hp ht]
    positivity
  have henergy : (t + lam) * |deriv (residual (generalizedRidge lam p)) t| =
      p * residual (generalizedRidge lam p) t * ((t + lam) * generalizedRidge lam p t) := by
    rw [(generalizedRidge_residual_hasDerivAt hlam hp ht).deriv,
      generalizedRidge_residual hlam hp ht, abs_div, abs_neg,
      abs_of_nonneg (mul_nonneg (mul_nonneg hLp.le hpp.le) htp), abs_of_pos (sq_pos_of_pos hd)]
    unfold generalizedRidge
    field_simp
  rw [henergy, abs_of_nonneg hψ0]
  have hi := generalizedRidge_inverse_bound hlam hp ht
  have hres := generalizedRidge_residual_bound hlam hp ht
  rw [abs_of_nonneg hψ0] at hres
  calc
    _ ≤ (1 + 2 * p) * residual (generalizedRidge lam p) t := by
      nlinarith [mul_nonneg (mul_nonneg hpp.le hψ0) (sub_nonneg.mpr hi)]
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hres (by linarith : 0 ≤ 1 + 2 * p)

/-- A λ-independent explicit smooth-condition constant. -/
def generalizedRidgeSmoothConstant (p : ℝ) : ℝ := 2 + (1 + 2 * p) * (2 : ℝ) ^ (p - 1)

/-- Generalized ridge satisfies the original scale-regular residual contract
for every fixed real exponent p≥1, without a derivative or size certificate. -/
theorem generalizedRidge_contract {lam M p : ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hp : 1 ≤ p) :
    Contract lam M p (max (generalizedRidgeSmoothConstant p) 1 * max 2 p)
      (generalizedRidge lam p) := by
  apply contract_of_smooth_condition_nonnegative_interval hlam hM (zero_lt_one.trans_le hp)
    (generalizedRidge_spectralFilter hlam hp)
    (generalizedRidge_residual_absolutelyContinuous hlam hM hp)
  · intro t ht
    exact (generalizedRidge_inverse_bound hlam hp ht.1).trans (by
      unfold generalizedRidgeSmoothConstant
      nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (p - 1)])
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (generalizedRidge_smooth_bound hlam hp ht.1).trans
      (mul_le_mul_of_nonneg_right (by simp [generalizedRidgeSmoothConstant])
        (Real.rpow_nonneg (div_nonneg hlam.le (add_nonneg ht.1 hlam.le)) _))

end
end KernelSeq.ResidualFilter
