import KernelSeq.AngularRieszExpansion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.PSeries

/-!
# Actual angular integration by parts

These are genuine real Fourier moments on one period, with actual derivative
and endpoint identities. They are scalar foundations for the fixed symbol's
harmonic decomposition, not multiplier norm assumptions.
-/

open MeasureTheory
open scoped ContDiff

namespace KernelSeq
noncomputable section

def angularCosMoment (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ t in 0..(2 * Real.pi), f t * Real.cos ((n : ℝ) * t)

def angularSinMoment (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ t in 0..(2 * Real.pi), f t * Real.sin ((n : ℝ) * t)

theorem angular_periodic_deriv {f : ℝ → ℝ} {T : ℝ}
    (hf : Differentiable ℝ f) (hper : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  have h := ((hf (x + T)).hasDerivAt).comp x ((hasDerivAt_id x).add_const T)
  have he : (fun t : ℝ => f (t + T)) = f := funext hper
  change HasDerivAt (fun t : ℝ => f (t + T)) (deriv f (x + T) * 1) x at h
  rw [he, mul_one] at h
  exact h.deriv.symm

/-- Actual cosine-moment integration by parts, with the endpoint term
cancelled by the genuine periodicity of the original function. -/
theorem angularCosMoment_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f (2 * Real.pi)) (n : ℕ) :
    angularCosMoment (deriv f) n = (n : ℝ) * angularSinMoment f n := by
  have hcos (x : ℝ) : HasDerivAt (fun t : ℝ => Real.cos ((n : ℝ) * t))
      (-(n : ℝ) * Real.sin ((n : ℝ) * x)) x := by
    convert! ((hasDerivAt_id x).const_mul (n : ℝ)).cos using 1
    simp only [id_eq]
    ring
  have hd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hv : Continuous (fun x : ℝ => Real.cos ((n : ℝ) * x)) := by fun_prop
  have hv' : Continuous (fun x : ℝ => -(n : ℝ) * Real.sin ((n : ℝ) * x)) := by fun_prop
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hf.continuous.continuousOn hv.continuousOn
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt) (fun x _ => hcos x)
    (hd.intervalIntegrable 0 (2 * Real.pi)) (hv'.intervalIntegrable 0 (2 * Real.pi))
    (a := 0) (b := 2 * Real.pi)
  have hp : f (2 * Real.pi) = f 0 := by simpa only [zero_add] using hper 0
  have hi : (∫ x in 0..(2 * Real.pi), f x * (-(n : ℝ) * Real.sin ((n : ℝ) * x))) =
      -(n : ℝ) * angularSinMoment f n := by
    rw [angularSinMoment, ← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  simp only [hp, Real.cos_nat_mul_two_pi, mul_zero, Real.cos_zero, mul_one, sub_self,
    hi, angularCosMoment] at hb ⊢
  linarith

/-- The sine endpoint term vanishes for every actual integer frequency. -/
theorem angularSinMoment_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    angularSinMoment (deriv f) n = -(n : ℝ) * angularCosMoment f n := by
  have hsin (x : ℝ) : HasDerivAt (fun t : ℝ => Real.sin ((n : ℝ) * t))
      ((n : ℝ) * Real.cos ((n : ℝ) * x)) x := by
    convert! ((hasDerivAt_id x).const_mul (n : ℝ)).sin using 1
    simp only [id_eq]
    ring
  have hd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hv : Continuous (fun x : ℝ => Real.sin ((n : ℝ) * x)) := by fun_prop
  have hv' : Continuous (fun x : ℝ => (n : ℝ) * Real.cos ((n : ℝ) * x)) := by fun_prop
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hf.continuous.continuousOn hv.continuousOn
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt) (fun x _ => hsin x)
    (hd.intervalIntegrable 0 (2 * Real.pi)) (hv'.intervalIntegrable 0 (2 * Real.pi))
    (a := 0) (b := 2 * Real.pi)
  have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    have he : (n : ℝ) * (2 * Real.pi) = ((2 * n : ℕ) : ℝ) * Real.pi := by push_cast; ring
    rw [he, Real.sin_nat_mul_pi]
  have hi : (∫ x in 0..(2 * Real.pi), f x * ((n : ℝ) * Real.cos ((n : ℝ) * x))) =
      (n : ℝ) * angularCosMoment f n := by
    rw [angularCosMoment, ← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  simp only [hs, mul_zero, Real.sin_zero, sub_zero, zero_sub, hi, angularSinMoment] at hb ⊢
  linarith

theorem angularCosMoment_cubic_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f (2 * Real.pi)) (n : ℕ) :
    (n : ℝ) ^ 3 * angularCosMoment f n = angularSinMoment (deriv (deriv (deriv f))) n := by
  have hf1 : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  have hf2 : ContDiff ℝ ∞ (deriv (deriv f)) := hf1.deriv'
  have hp1 := angular_periodic_deriv (hf.differentiable (by simp)) hper
  rw [angularSinMoment_deriv (hf2.of_le (by simp)) n,
    angularCosMoment_deriv (hf1.of_le (by simp)) hp1 n,
    angularSinMoment_deriv (hf.of_le (by simp)) n]
  ring

theorem angularSinMoment_cubic_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f (2 * Real.pi)) (n : ℕ) :
    (n : ℝ) ^ 3 * angularSinMoment f n = -angularCosMoment (deriv (deriv (deriv f))) n := by
  have hf1 : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  have hf2 : ContDiff ℝ ∞ (deriv (deriv f)) := hf1.deriv'
  have hp1 := angular_periodic_deriv (hf.differentiable (by simp)) hper
  have hp2 := angular_periodic_deriv (hf1.differentiable (by simp)) hp1
  rw [angularCosMoment_deriv (hf2.of_le (by simp)) hp2 n,
    angularSinMoment_deriv (hf1.of_le (by simp)) n,
    angularCosMoment_deriv (hf.of_le (by simp)) hper n]
  ring

private theorem angularMoment_abs_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hgb : ∀ x, |g x| ≤ 1) :
    |∫ x in 0..(2 * Real.pi), f x * g x| ≤ ∫ x in 0..(2 * Real.pi), |f x| := by
  have hT : 0 ≤ 2 * Real.pi := by positivity
  calc
    _ ≤ ∫ x in 0..(2 * Real.pi), |f x * g x| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (f := fun x => f x * g x) hT)
    _ ≤ _ := intervalIntegral.integral_mono_on hT
      ((hf.mul hg).abs.intervalIntegrable _ _) (hf.abs.intervalIntegrable _ _)
      (fun x _ => by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hgb x) (abs_nonneg _)).trans_eq (mul_one _))

def angularThirdDerivativeL1 (f : ℝ → ℝ) : ℝ :=
  ∫ x in 0..(2 * Real.pi), |deriv (deriv (deriv f)) x|

private theorem angular_thirdDerivative_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (deriv (deriv (deriv f))) := by
  have h1 : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  have h2 : ContDiff ℝ ∞ (deriv (deriv f)) := h1.deriv'
  have h3 : ContDiff ℝ ∞ (deriv (deriv (deriv f))) := h2.deriv'
  exact h3.continuous

theorem angularThirdDerivativeL1_nonneg (f : ℝ → ℝ) : 0 ≤ angularThirdDerivativeL1 f := by
  exact intervalIntegral.integral_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    (fun _ _ => abs_nonneg _)

/-- Actual third derivatives give a cubic coefficient bound, with the
constant a genuine finite integral rather than a supplied decay certificate. -/
theorem angularCosMoment_decay {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f (2 * Real.pi)) {n : ℕ} (hn : 0 < n) :
    |angularCosMoment f n| ≤ angularThirdDerivativeL1 f / (n : ℝ) ^ 3 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc := angular_thirdDerivative_continuous hf
  apply (le_div_iff₀ (pow_pos hnp 3)).mpr
  calc
    _ = |(n : ℝ) ^ 3 * angularCosMoment f n| := by
      rw [abs_mul, abs_of_pos (pow_pos hnp 3), mul_comm]
    _ = |angularSinMoment (deriv (deriv (deriv f))) n| :=
      congrArg abs (angularCosMoment_cubic_deriv hf hper n)
    _ ≤ _ := angularMoment_abs_le hc (by fun_prop) (fun x => Real.abs_sin_le_one _)

theorem angularSinMoment_decay {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f (2 * Real.pi)) {n : ℕ} (hn : 0 < n) :
    |angularSinMoment f n| ≤ angularThirdDerivativeL1 f / (n : ℝ) ^ 3 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc := angular_thirdDerivative_continuous hf
  apply (le_div_iff₀ (pow_pos hnp 3)).mpr
  calc
    _ = |(n : ℝ) ^ 3 * angularSinMoment f n| := by
      rw [abs_mul, abs_of_pos (pow_pos hnp 3), mul_comm]
    _ = |angularCosMoment (deriv (deriv (deriv f))) n| := by
      rw [angularSinMoment_cubic_deriv hf hper n, abs_neg]
    _ ≤ _ := angularMoment_abs_le hc (by fun_prop) (fun x => Real.abs_cos_le_one _)

/-- The actual fixed symbol has proved cubic angular decay, including the
regularity and periodicity needed to obtain it. -/
theorem lipschitzAngularMoments_decay {n : ℕ} (hn : 0 < n) :
    |angularCosMoment lipschitzAngularProfile n| ≤
        angularThirdDerivativeL1 lipschitzAngularProfile / (n : ℝ) ^ 3 ∧
      |angularSinMoment lipschitzAngularProfile n| ≤
        angularThirdDerivativeL1 lipschitzAngularProfile / (n : ℝ) ^ 3 :=
  ⟨angularCosMoment_decay lipschitzAngularProfile_contDiff lipschitzAngularProfile_periodic hn,
    angularSinMoment_decay lipschitzAngularProfile_contDiff lipschitzAngularProfile_periodic hn⟩

/-- Genuine weighted absolute summability follows from the proved cubic
decay and the actual scalar p-series, with no summability certificate. -/
theorem angularMoments_weighted_summable {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) *
      (|angularCosMoment f (n + 1)| + |angularSinMoment f (n + 1)|)) := by
  let K := angularThirdDerivativeL1 f
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hbase
  apply Summable.of_nonneg_of_le (fun n => by positivity) ?_ (hshift.mul_left (2 * K))
  intro n
  have hn : 0 < n + 1 := by omega
  have hnp : 0 < (n : ℝ) + 1 := by positivity
  have hcos := angularCosMoment_decay hf hper hn
  have hsin := angularSinMoment_decay hf hper hn
  simp only [Nat.cast_add, Nat.cast_one] at hcos hsin
  calc
    _ ≤ ((n : ℝ) + 1) * (K / ((n : ℝ) + 1) ^ 3 + K / ((n : ℝ) + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (add_le_add hcos hsin) hnp.le
    _ = _ := by field_simp; ring

/-- Dividing by the actual chosen Riesz harmonic coefficients preserves
absolute summability. This is the scalar cost needed for the later angular
multiplier decomposition; the decomposition itself is a separate step. -/
theorem angularRieszMomentWeights_summable {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    Summable (fun n : ℕ =>
      (|angularCosMoment f (n + 1)| + |angularSinMoment f (n + 1)|) /
        angularRieszCoefficient n) := by
  have hsum := (angularMoments_weighted_summable hf hper).mul_left 4
  apply Summable.of_nonneg_of_le ?_ ?_ hsum
  · intro n
    have hp : 0 < angularRieszCoefficient n :=
      (by positivity : 0 < 1 / (4 * ((n : ℝ) + 1))).trans_le (angularRieszCoefficient_lower n)
    exact div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hp.le
  · intro n
    have hN : 0 < 4 * ((n : ℝ) + 1) := by positivity
    have hp : 0 < angularRieszCoefficient n :=
      (div_pos zero_lt_one hN).trans_le (angularRieszCoefficient_lower n)
    have hunit : 1 ≤ angularRieszCoefficient n * (4 * ((n : ℝ) + 1)) :=
      (div_le_iff₀ hN).mp (angularRieszCoefficient_lower n)
    apply (div_le_iff₀ hp).mpr
    have hnonneg : 0 ≤ |angularCosMoment f (n + 1)| + |angularSinMoment f (n + 1)| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hunit hnonneg]

theorem lipschitzAngularRieszMomentWeights_summable :
    Summable (fun n : ℕ =>
      (|angularCosMoment lipschitzAngularProfile (n + 1)| +
        |angularSinMoment lipschitzAngularProfile (n + 1)|) / angularRieszCoefficient n) :=
  angularRieszMomentWeights_summable lipschitzAngularProfile_contDiff lipschitzAngularProfile_periodic

end
end KernelSeq
