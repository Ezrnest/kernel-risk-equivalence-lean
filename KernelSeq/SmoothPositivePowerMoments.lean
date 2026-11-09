import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial moments of nonnegative smooth power-series coefficients

Endpoint continuity bounds finite nonnegative coefficient sums. Repeated
actual differentiation of the power series and smoothness up to the endpoint
then give every fixed polynomial coefficient moment, without an additional
moment assumption on the dot-product kernel profile.
-/

namespace KernelSeq

open Filter Set FormalMultilinearSeries
open scoped Topology BigOperators ENNReal NNReal ContDiff
noncomputable section

theorem summable_nonneg_coeff_of_powerSeries_endpoint
    {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesWithinOnBall f p (Icc (0 : ℝ) 1) 0 1)
    (ha : ∀ j, 0 ≤ p.coeff j) (hf : ContinuousWithinAt f (Icc (0 : ℝ) 1) 1) :
    Summable p.coeff := by
  haveI : NeBot (𝓝[Ioo (0 : ℝ) 1] 1) := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨by norm_num, le_refl _⟩
  apply summable_of_sum_le ha
  intro J
  have hsum : Tendsto (fun x : ℝ => ∑ j ∈ J, x^j*p.coeff j)
      (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 (∑ j ∈ J, p.coeff j)) := by
    have hh : ContinuousAt (fun x : ℝ => ∑ j ∈ J, x^j*p.coeff j) 1 := by fun_prop
    simpa only [one_pow, one_mul] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hfl : Tendsto f (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 (f 1)) := hf.mono Ioo_subset_Icc_self
  apply le_of_tendsto_of_tendsto hsum hfl
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hball : x ∈ Metric.eball (0 : ℝ) (1 : ℝ≥0∞) := by
    change edist x (0 : ℝ) < (1 : ℝ≥0∞)
    rw [edist_dist, Real.dist_eq, sub_zero, abs_of_pos hx.1]
    exact ENNReal.ofReal_lt_one.mpr hx.2
  have hh := hp.hasSum (by simpa only [zero_add, insert_eq_of_mem (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)]
    using (Ioo_subset_Icc_self hx)) hball
  simp only [apply_eq_pow_smul_coeff, smul_eq_mul, zero_add] at hh
  exact (hh.summable.sum_le_tsum J (fun j _ => mul_nonneg (pow_nonneg hx.1.le _) (ha j))).trans_eq hh.tsum_eq

def scalarDerivPowerSeries (p : FormalMultilinearSeries ℝ ℝ ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries p.derivSeries

theorem scalarDerivPowerSeries_coeff (p : FormalMultilinearSeries ℝ ℝ ℝ) (j : ℕ) :
    (scalarDerivPowerSeries p).coeff j = (j+1 : ℝ)*p.coeff (j+1) := by
  simpa only [scalarDerivPowerSeries, FormalMultilinearSeries.coeff,
    ContinuousLinearMap.compFormalMultilinearSeries_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, Nat.cast_add, Nat.cast_one, nsmul_eq_mul] using p.derivSeries_coeff_one j

theorem powerSeries_derivWithin
    {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesWithinOnBall f p (Icc (0 : ℝ) 1) 0 1) :
    HasFPowerSeriesWithinOnBall (derivWithin f (Icc (0 : ℝ) 1))
      (scalarDerivPowerSeries p) (Icc (0 : ℝ) 1) 0 1 := by
  exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp_hasFPowerSeriesWithinOnBall
    (hp.fderivWithin_of_mem (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) (by norm_num))

theorem summable_smooth_nonneg_powerSeries_coeff_moment
    (r : ℕ) {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesWithinOnBall f p (Icc (0 : ℝ) 1) 0 1)
    (ha : ∀ j, 0 ≤ p.coeff j) (hf : ContDiffOn ℝ ∞ f (Icc (0 : ℝ) 1)) :
    Summable (fun j => p.coeff j*(j+1 : ℝ)^r) := by
  induction r generalizing f p with
  | zero =>
    simpa only [pow_zero, mul_one] using summable_nonneg_coeff_of_powerSeries_endpoint hp ha
      (hf.continuousOn 1 (by norm_num))
  | succ r IH =>
    have hq : ∀ j, 0 ≤ (scalarDerivPowerSeries p).coeff j := by
      intro j
      rw [scalarDerivPowerSeries_coeff]
      exact mul_nonneg (by positivity) (ha _)
    have hfs : ContDiffOn ℝ ∞ (derivWithin f (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) :=
      hf.derivWithin (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) (by simp)
    have hs := IH (powerSeries_derivWithin hp) hq hfs
    have hs' : Summable (fun j => p.coeff (j+1)*(j+1 : ℝ)^(r+1)) := by
      apply hs.congr
      intro j
      rw [scalarDerivPowerSeries_coeff, pow_succ]
      ring
    have htail : Summable (fun j => p.coeff (j+1)*((j+1 : ℝ)+1)^(r+1)) := by
      apply Summable.of_nonneg_of_le (fun j => mul_nonneg (ha _) (by positivity))
        (fun j => ?_) (hs'.mul_left ((2 : ℝ)^(r+1)))
      have hj : ((j+1 : ℝ)+1)^(r+1) ≤ (2*(j+1 : ℝ))^(r+1) := by
        gcongr
        nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
      have hm := mul_le_mul_of_nonneg_left hj (ha (j+1))
      rw [mul_pow] at hm
      nlinarith only [hm]
    exact (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add, Nat.cast_one] using htail)

/-- The original literal nonnegative power-series representation and
closed-interval smoothness imply every fixed polynomial moment. -/
theorem summable_coeff_natPower_of_smooth_positive_series
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (r : ℕ) :
    Summable (fun j => a j*(j+1 : ℝ)^r) := by
  have hs : Summable a := by simpa only [one_pow, mul_one] using (hseries 1 (by norm_num)).summable
  let p := FormalMultilinearSeries.ofScalars ℝ a
  have hrad : (1 : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable (r := 1)
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (ha _)] using hs
  have hp : HasFPowerSeriesWithinOnBall Φ p (Icc (0 : ℝ) 1) 0 1 := by
    refine ⟨hrad, by norm_num, ?_⟩
    intro t ht _
    have ht' : t ∈ Icc (-1 : ℝ) 1 := by
      simp only [zero_add, insert_eq_of_mem (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)] at ht
      exact ⟨by linarith [ht.1], ht.2⟩
    simpa only [p, ofScalars_apply_eq, smul_eq_mul, zero_add] using hseries t ht'
  have hh := summable_smooth_nonneg_powerSeries_coeff_moment r hp
    (by simpa only [p, coeff_ofScalars] using ha)
    (hΦ.mono (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩))
  simpa only [p, coeff_ofScalars] using hh

theorem summable_coeff_power_of_smooth_positive_series
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (r : ℕ) :
    Summable (fun j => a j*(j : ℝ)^r) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (ha j) (by positivity))
    (fun j => ?_) (summable_coeff_natPower_of_smooth_positive_series a ha Φ hseries hΦ r)
  apply mul_le_mul_of_nonneg_left _ (ha j)
  gcongr
  norm_num

/-- Any fixed real polynomial weight is allowed; negative exponents cause
no singularity because the weight is `j+1`. -/
theorem summable_coeff_rpow_of_smooth_positive_series
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (r : ℝ) :
    Summable (fun j => a j*(j+1 : ℝ)^r) := by
  obtain ⟨N, hN⟩ := exists_nat_gt r
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (ha j) (Real.rpow_nonneg (by positivity) _))
    (fun j => ?_) (summable_coeff_natPower_of_smooth_positive_series a ha Φ hseries hΦ N)
  have hj : (j+1 : ℝ)^r ≤ (j+1 : ℝ)^(N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hN.le
  simpa only [Real.rpow_natCast] using mul_le_mul_of_nonneg_left hj (ha j)

end
end KernelSeq
