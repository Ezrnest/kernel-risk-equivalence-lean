import KernelSeq.OriginalBiasAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A deterministic power-schedule engine for the original three scales

This module is only a scalar asymptotic tool. Applications must prove its
effective-dimension, inverse filter-dimension, leverage, and source-energy
bounds from the actual spectrum and target assumptions. No risk conclusion
or moment estimate is a hypothesis here.
-/

namespace KernelSeq
open Filter Asymptotics
open scoped Topology
noncomputable section

variable {J : Type*} {l : Filter J} {n f : J → ℝ}

/-- Logarithms of any nonnegative polynomially bounded quantity grow more
slowly than every positive power of the sample size. No limit for f is needed. -/
theorem log_exp_add_isBigO_rpow (hn : Tendsto n l atTop)
    (hf0 : ∀ᶠ i in l, 0 ≤ f i) {b ε : ℝ} (hε : 0 < ε)
    (hf : f =O[l] (fun i => n i ^ b)) :
    (fun i => Real.log (Real.exp 1 + f i)) =O[l] (fun i => n i ^ ε) := by
  obtain ⟨C, hC, hbound⟩ := hf.exists_pos
  let B := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  have hD : 0 < Real.exp 1 + C := by positivity
  have hlogD : 0 ≤ Real.log (Real.exp 1 + C) := by
    apply Real.log_nonneg
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : (fun i => Real.log (Real.exp 1 + f i)) =O[l] (fun i => Real.log (n i)) := by
    apply IsBigO.of_bound (Real.log (Real.exp 1 + C) + B)
    filter_upwards [hbound.bound, hf0, hn.eventually (eventually_ge_atTop (Real.exp 1))] with i hi hf hiN
    have hn1 : 1 ≤ n i := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hnP : 0 < n i := zero_lt_one.trans_le hn1
    have hnB : 1 ≤ n i ^ B := Real.one_le_rpow hn1 hB
    have hbB : n i ^ b ≤ n i ^ B := Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)
    have hfi : f i ≤ C * n i ^ B := by
      have hh : f i ≤ C * n i ^ b := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg (Real.rpow_nonneg hnP.le _)] using hi
      exact hh.trans (mul_le_mul_of_nonneg_left hbB hC.le)
    have hle : Real.exp 1 + f i ≤ (Real.exp 1 + C) * n i ^ B := by
      nlinarith [mul_le_mul_of_nonneg_left hnB (Real.exp_pos 1).le]
    have hlogn : 1 ≤ Real.log (n i) := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hiN
    have hlogf : 0 ≤ Real.log (Real.exp 1 + f i) := by
      apply Real.log_nonneg
      linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.norm_eq_abs, abs_of_nonneg hlogf, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hlogn)]
    calc
      _ ≤ Real.log ((Real.exp 1 + C) * n i ^ B) := Real.log_le_log (by positivity) hle
      _ = Real.log (Real.exp 1 + C) + B * Real.log (n i) := by
        rw [Real.log_mul hD.ne' (Real.rpow_pos_of_pos hnP B).ne', Real.log_rpow hnP]
      _ ≤ _ := by nlinarith
  exact hlog.trans ((isLittleO_log_rpow_atTop hε).comp_tendsto hn).isBigO

private theorem powerBigO_mul (hn : Tendsto n l atTop)
    {f g : J → ℝ} {a b : ℝ} (hf : f =O[l] (fun i => n i ^ a))
    (hg : g =O[l] (fun i => n i ^ b)) :
    (fun i => f i * g i) =O[l] (fun i => n i ^ (a + b)) := by
  apply (hf.mul hg).congr' Filter.EventuallyEq.rfl
  filter_upwards [hn.eventually (eventually_gt_atTop 0)] with i hi
  exact (Real.rpow_add hi a b).symm

private theorem powerBigO_pow (hn : Tendsto n l atTop)
    {f : J → ℝ} {a : ℝ} (hf : f =O[l] (fun i => n i ^ a)) (k : ℕ) :
    (fun i => f i ^ k) =O[l] (fun i => n i ^ (a * k)) := by
  apply (hf.pow k).congr' Filter.EventuallyEq.rfl
  filter_upwards [hn.eventually (eventually_gt_atTop 0)] with i hi
  rw [← Real.rpow_natCast, ← Real.rpow_mul hi.le]

private theorem powerBigO_tendsto_zero (hn : Tendsto n l atTop)
    {f : J → ℝ} {a : ℝ} (hf : f =O[l] (fun i => n i ^ a)) (ha : a < 0) :
    Tendsto f l (𝓝 0) := by
  apply hf.trans_tendsto
  have hh := (tendsto_rpow_neg_atTop (neg_pos.mpr ha)).comp hn
  simpa only [Function.comp_def, neg_neg] using hh

private theorem original_gamma_log_isBigO (hn : Tendsto n l atTop)
    {N : J → ℝ} {b ε : ℝ} (hN0 : ∀ᶠ i in l, 0 ≤ N i) (hb : 0 ≤ b) (hε : 0 < ε)
    (hN : N =O[l] (fun i => n i ^ b)) :
    (fun i => Real.log (Real.exp 1 + Real.sqrt (N i / dimensionLog (N i)))) =O[l]
      (fun i => n i ^ ε) := by
  have hone : (fun _ : J => (1 : ℝ)) =O[l] (fun i => n i ^ b) := by
    apply IsBigO.of_bound 1
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with i hi
    simpa only [norm_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) _)] using Real.one_le_rpow hi hb
  have hupper := log_exp_add_isBigO_rpow hn (hN0.mono fun i hi => by linarith) hε (hone.add hN)
  have hdom : (fun i => Real.log (Real.exp 1 + Real.sqrt (N i / dimensionLog (N i)))) =O[l]
      (fun i => Real.log (Real.exp 1 + (1 + N i))) := by
    apply IsBigO.of_bound 1
    filter_upwards [hN0] with i hi
    have hell := one_le_dimensionLog hi
    have hEll : 0 < dimensionLog (N i) := zero_lt_one.trans_le hell
    have hd : N i / dimensionLog (N i) ≤ N i := (div_le_iff₀ hEll).2 (by nlinarith)
    have hs : Real.sqrt (N i / dimensionLog (N i)) ≤ 1 + N i :=
      Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg (N i)]⟩
    have hleft : 0 ≤ Real.log (Real.exp 1 + Real.sqrt (N i / dimensionLog (N i))) := by
      apply Real.log_nonneg
      linarith [Real.add_one_le_exp (1 : ℝ), Real.sqrt_nonneg (N i / dimensionLog (N i))]
    have hright : 0 ≤ Real.log (Real.exp 1 + (1 + N i)) := by
      apply Real.log_nonneg
      linarith [Real.add_one_le_exp (1 : ℝ)]
    simp only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright, one_mul]
    exact Real.log_le_log (by positivity) (by linarith)
  exact hdom.trans hupper

/-- Sample-power bounds imply the exact variance compatibility scale. -/
theorem original_compatibility_of_sample_power_bounds (hn : Tendsto n l atTop)
    {N Q L : J → ℝ} {bN bQ bL : ℝ}
    (hrow : ∀ᶠ i in l, 0 ≤ N i ∧ 0 < Q i ∧ 0 ≤ L i)
    (hN : N =O[l] (fun i => n i ^ bN))
    (hQ : (fun i => (Q i)⁻¹) =O[l] (fun i => n i ^ bQ))
    (hL : L =O[l] (fun i => n i ^ bL))
    (hexp : 2 * bN + 2 * bQ + bL < 1) :
    Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0) := by
  let ε := (1 - (2 * bN + 2 * bQ + bL)) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hlog : (fun i => dimensionLog (N i)) =O[l] (fun i => n i ^ ε) :=
    log_exp_add_isBigO_rpow hn (hrow.mono fun _ hi => hi.1) hε hN
  have hi : (fun i => (n i)⁻¹) =O[l] (fun i => n i ^ (-1 : ℝ)) := by
    simpa only [Real.rpow_neg_one] using isBigO_refl (fun i => (n i)⁻¹) l
  have hp := powerBigO_mul hn (powerBigO_mul hn (powerBigO_mul hn
    (powerBigO_mul hn (powerBigO_pow hn hN 2) (powerBigO_pow hn hQ 2)) hL) hlog) hi
  let c := fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)
  have hb : (fun i => c i ^ 2) =O[l]
      (fun i => n i ^ (bN * 2 + bQ * 2 + bL + ε + -1)) := by
    apply hp.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hrow, hn.eventually (eventually_gt_atTop 0)] with i hr hnP
    dsimp only [c]
    rw [mul_pow, Real.sq_sqrt (div_nonneg
      (mul_nonneg hr.2.2 (zero_le_one.trans (one_le_dimensionLog hr.1))) hnP.le), div_pow]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have hc : Tendsto (fun i => c i ^ 2) l (𝓝 0) :=
    powerBigO_tendsto_zero hn hb (by dsimp only [ε]; norm_num; linarith)
  have hs : Tendsto (fun i => Real.sqrt (c i ^ 2)) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hc
  apply hs.congr'
  filter_upwards [hrow] with i hr
  exact Real.sqrt_sq (mul_nonneg (div_nonneg hr.1 hr.2.1.le) (Real.sqrt_nonneg _))

/-- Sample-power bounds imply the original source-balance scale, with the
two logarithmic factors in γ kept exactly as defined in the manuscript. -/
theorem original_source_scale_of_sample_power_bounds (hn : Tendsto n l atTop)
    {N Q L S : J → ℝ} {bN bQ bL bS : ℝ} (hbN : 0 ≤ bN)
    (hrow : ∀ᶠ i in l, 0 ≤ N i ∧ 0 < Q i ∧ 0 ≤ L i)
    (hN : N =O[l] (fun i => n i ^ bN))
    (hQ : (fun i => (Q i)⁻¹) =O[l] (fun i => n i ^ bQ))
    (hL : L =O[l] (fun i => n i ^ bL))
    (hS : S =O[l] (fun i => n i ^ bS)) (hexp : bS + bQ + bL < 0) :
    Tendsto (fun i => n i * S i * originalBiasGamma (L i) (n i) (N i) ^ 2 / Q i) l (𝓝 0) := by
  let ε := -(bS + bQ + bL) / 6
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hlog : (fun i => dimensionLog (N i)) =O[l] (fun i => n i ^ ε) :=
    log_exp_add_isBigO_rpow hn (hrow.mono fun _ hi => hi.1) hε hN
  have hinner := original_gamma_log_isBigO hn (hrow.mono fun _ hi => hi.1) hbN hε hN
  have hp := powerBigO_mul hn (powerBigO_mul hn (powerBigO_mul hn
    (powerBigO_mul hn hS hL) hlog) (powerBigO_pow hn hinner 2)) hQ
  have hb : (fun i => n i * S i * originalBiasGamma (L i) (n i) (N i) ^ 2 / Q i) =O[l]
      (fun i => n i ^ (bS + bL + ε + ε * 2 + bQ)) := by
    apply hp.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hrow, hn.eventually (eventually_gt_atTop 0)] with i hr hnP
    unfold originalBiasGamma
    rw [mul_pow, Real.sq_sqrt (div_nonneg
      (mul_nonneg hr.2.2 (zero_le_one.trans (one_le_dimensionLog hr.1))) hnP.le)]
    field_simp
  exact powerBigO_tendsto_zero hn hb (by dsimp only [ε]; linarith)

/-- Sample-power bounds imply the extra logarithmic expectation scale. -/
theorem original_expectation_scale_of_sample_power_bounds (hn : Tendsto n l atTop)
    {lam Q L : J → ℝ} {bLam bQ bL : ℝ}
    (hrow : ∀ᶠ i in l, 0 < lam i ∧ 0 < Q i)
    (hlam : (fun i => (lam i)⁻¹) =O[l] (fun i => n i ^ bLam))
    (hQ : (fun i => (Q i)⁻¹) =O[l] (fun i => n i ^ bQ))
    (hL : L =O[l] (fun i => n i ^ bL)) (hexp : bL < 1) :
    Tendsto (fun i => L i / n i * Real.log (Real.exp 1 + n i / (lam i * Q i))) l (𝓝 0) := by
  let ε := (1 - bL) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hnO : n =O[l] (fun i => n i ^ (1 : ℝ)) := by
    simpa only [Real.rpow_one] using isBigO_refl n l
  have hratio : (fun i => n i / (lam i * Q i)) =O[l] (fun i => n i ^ (1 + bLam + bQ)) := by
    exact (powerBigO_mul hn (powerBigO_mul hn hnO hlam) hQ).congr_left
      (fun i => by simp only [div_eq_mul_inv, mul_inv]; ring)
  have hratio0 : ∀ᶠ i in l, 0 ≤ n i / (lam i * Q i) := by
    filter_upwards [hrow, hn.eventually (eventually_ge_atTop 0)] with i hr hi
    exact div_nonneg hi (mul_pos hr.1 hr.2).le
  have hlog := log_exp_add_isBigO_rpow hn hratio0 hε hratio
  have hi : (fun i => (n i)⁻¹) =O[l] (fun i => n i ^ (-1 : ℝ)) := by
    simpa only [Real.rpow_neg_one] using isBigO_refl (fun i => (n i)⁻¹) l
  have hb := (powerBigO_mul hn (powerBigO_mul hn hL hi) hlog).congr_left
    (fun i => by rw [div_eq_mul_inv])
  exact powerBigO_tendsto_zero hn hb (by dsimp only [ε]; linarith)

private theorem power_schedule_bound (hn : Tendsto n l atTop)
    {lam : J → ℝ} {θ r : ℝ} (hlam0 : ∀ᶠ i in l, 0 < lam i)
    (hschedule : lam =Θ[l] (fun i => n i ^ (-θ))) :
    (fun i => lam i ^ r) =O[l] (fun i => n i ^ (-θ * r)) := by
  have hnp : ∀ᶠ i in l, 0 ≤ n i ^ (-θ) :=
    (hn.eventually (eventually_gt_atTop 0)).mono fun _ hi => Real.rpow_nonneg hi.le _
  have hh := Asymptotics.IsTheta.rpow (r := r) (hlam0.mono fun _ hi => hi.le) hnp hschedule
  apply hh.1.congr' Filter.EventuallyEq.rfl
  filter_upwards [hn.eventually (eventually_gt_atTop 0)] with i hi
  exact (Real.rpow_mul hi.le _ _).symm

/-- The complete scalar power-schedule engine for the manuscript's original
two conditional scales and additional expectation scale. The three strict
exponent tests are exactly the powers left after logarithms are absorbed.

The usual application has `p,ellExp,q≥0`, `q<1` and `a>0`; the proof only
needs `p≥0` and the displayed strict tests, so the scalar engine is slightly
more general. The inputs are scalar Big-O bounds, not risk conclusions. -/
theorem original_three_scales_of_power_bounds
    (n lam N Q L S : J → ℝ) (hn : Tendsto n l atTop)
    {θ p q ellExp a : ℝ} (hθ : 0 < θ) (hp : 0 ≤ p)
    (hrow : ∀ᶠ i in l, 0 < lam i ∧ 0 ≤ N i ∧ 0 < Q i ∧ 0 ≤ L i)
    (hschedule : lam =Θ[l] (fun i => n i ^ (-θ)))
    (hN : N =O[l] (fun i => lam i ^ (-p)))
    (hQ : (fun i => (Q i)⁻¹) =O[l] (fun i => lam i ^ q))
    (hL : L =O[l] (fun i => lam i ^ (-ellExp)))
    (hS : S =O[l] (fun i => lam i ^ a))
    (hcompat : θ * (2 * p + ellExp - 2 * q) < 1)
    (hsource : 0 < a + q - ellExp) (hexpect : θ * ellExp < 1) :
    Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0) ∧
      Tendsto (fun i => n i * S i * originalBiasGamma (L i) (n i) (N i) ^ 2 / Q i) l (𝓝 0) ∧
      Tendsto (fun i => L i / n i * Real.log (Real.exp 1 + n i / (lam i * Q i))) l (𝓝 0) := by
  have hLam0 := hrow.mono fun _ hi => hi.1
  have hNn : N =O[l] (fun i => n i ^ (θ * p)) := by
    apply (hN.trans (power_schedule_bound hn hLam0 hschedule)).congr_right
    intro i
    congr 1
    ring
  have hQn : (fun i => (Q i)⁻¹) =O[l] (fun i => n i ^ (-θ * q)) :=
    hQ.trans (power_schedule_bound hn hLam0 hschedule)
  have hLn : L =O[l] (fun i => n i ^ (θ * ellExp)) := by
    apply (hL.trans (power_schedule_bound hn hLam0 hschedule)).congr_right
    intro i
    congr 1
    ring
  have hSn : S =O[l] (fun i => n i ^ (-θ * a)) :=
    hS.trans (power_schedule_bound hn hLam0 hschedule)
  have hLamN : (fun i => (lam i)⁻¹) =O[l] (fun i => n i ^ θ) := by
    have hh := power_schedule_bound (r := -1) hn hLam0 hschedule
    simpa only [Real.rpow_neg_one, neg_mul, mul_neg, mul_one, neg_neg] using hh
  have hr : ∀ᶠ i in l, 0 ≤ N i ∧ 0 < Q i ∧ 0 ≤ L i := hrow.mono fun _ hi => hi.2
  refine ⟨original_compatibility_of_sample_power_bounds hn hr hNn hQn hLn ?_,
    original_source_scale_of_sample_power_bounds hn (mul_nonneg hθ.le hp) hr hNn hQn hLn hSn ?_,
    original_expectation_scale_of_sample_power_bounds hn
      (hrow.mono fun _ hi => ⟨hi.1, hi.2.2.1⟩) hLamN hQn hLn hexpect⟩
  · nlinarith
  · nlinarith [mul_pos hθ hsource]

end
end KernelSeq
