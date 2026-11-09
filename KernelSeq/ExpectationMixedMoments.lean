import KernelSeq.ConcentrationScale
import KernelSeq.OriginalBiasAsymptotics
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Genuine fractional second-moment Holder bounds

The fractional product is truly integrable from the two L2 inputs. Scalar
Holder supplies its moment bound; the original logarithmic exponent then
controls the effective-dimension factor uniformly, including zero values.
No mixed-moment or uniform-integrability estimate is assumed.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace KernelSeq
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem memLp_positive_rpow_of_two {δ : Ω → ℝ} (hδ : MemLp δ 2 μ)
    (hδ0 : 0 ≤ᵐ[μ] δ) {a : ℝ} (ha : 0 < a) :
    MemLp (fun ω => δ ω ^ a) (ENNReal.ofReal (2 / a)) μ := by
  have ht := hδ.norm_rpow_div (ENNReal.ofReal a)
  simp only [ENNReal.toReal_ofReal ha.le] at ht
  have he : (2 : ℝ≥0∞) / ENNReal.ofReal a = ENNReal.ofReal (2 / a) := by
    rw [ENNReal.ofReal_div_of_pos ha]
    norm_num
  rw [he] at ht
  apply ht.ae_eq
  filter_upwards [hδ0] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω]

/-- True Holder for any positive exponents adding to two, with the
fractional-product integrability derived from the genuine L2 inputs. -/
theorem fractional_second_moment_holder {δ η : Ω → ℝ}
    (hδ : MemLp δ 2 μ) (hη : MemLp η 2 μ)
    (hδ0 : 0 ≤ᵐ[μ] δ) (hη0 : 0 ≤ᵐ[μ] η)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 2) :
    Integrable (fun ω => δ ω ^ a * η ω ^ b) μ ∧
      (∫ ω, δ ω ^ a * η ω ^ b ∂μ) ≤
        (∫ ω, δ ω ^ 2 ∂μ) ^ (a / 2) * (∫ ω, η ω ^ 2 ∂μ) ^ (b / 2) := by
  let p := 2 / a
  let q := 2 / b
  have hpq : p.HolderConjugate q := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · dsimp only [p]
      apply (lt_div_iff₀ ha).mpr
      linarith
    · dsimp only [p, q]
      field_simp
      linarith
  have hFp : MemLp (fun ω => δ ω ^ a) (ENNReal.ofReal p) μ :=
    memLp_positive_rpow_of_two hδ hδ0 ha
  have hGq : MemLp (fun ω => η ω ^ b) (ENNReal.ofReal q) μ :=
    memLp_positive_rpow_of_two hη hη0 hb
  letI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 := hpq.ennrealOfReal
  have hint : Integrable (fun ω => δ ω ^ a * η ω ^ b) μ :=
    memLp_one_iff_integrable.mp (hGq.mul' hFp)
  refine ⟨hint, ?_⟩
  have hnδ : 0 ≤ᵐ[μ] (fun ω => δ ω ^ a) := hδ0.mono fun _ hi => Real.rpow_nonneg hi _
  have hnη : 0 ≤ᵐ[μ] (fun ω => η ω ^ b) := hη0.mono fun _ hi => Real.rpow_nonneg hi _
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hnδ hnη hFp hGq
  have hf : (∫ ω, (δ ω ^ a) ^ p ∂μ) = ∫ ω, δ ω ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hδ0] with ω hi
    rw [← Real.rpow_mul hi, show a * p = 2 by dsimp only [p]; field_simp, Real.rpow_two]
  have hg : (∫ ω, (η ω ^ b) ^ q ∂μ) = ∫ ω, η ω ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hη0] with ω hi
    rw [← Real.rpow_mul hi, show b * q = 2 by dsimp only [q]; field_simp, Real.rpow_two]
  have hp : 1 / p = a / 2 := by dsimp only [p]; field_simp
  have hq : 1 / q = b / 2 := by dsimp only [q]; field_simp
  rwa [hf, hg, hp, hq] at hh

/-- The exact mixed second-moment form in the expectation proof, m>2. -/
theorem mixed_second_moment_holder {δ η : Ω → ℝ}
    (hδ : MemLp δ 2 μ) (hη : MemLp η 2 μ)
    (hδ0 : 0 ≤ᵐ[μ] δ) (hη0 : 0 ≤ᵐ[μ] η) {m : ℝ} (hm : 2 < m) :
    Integrable (fun ω => δ ω ^ (2 - 4 / m) * η ω ^ (4 / m)) μ ∧
      (∫ ω, δ ω ^ (2 - 4 / m) * η ω ^ (4 / m) ∂μ) ≤
        (∫ ω, δ ω ^ 2 ∂μ) ^ (1 - 2 / m) * (∫ ω, η ω ^ 2 ∂μ) ^ (2 / m) := by
  have hm0 : 0 < m := by linarith
  have ha : 0 < 2 - 4 / m := by
    have hd : 4 / m < 2 := (div_lt_iff₀ hm0).mpr (by linarith)
    linarith
  have hb : 0 < 4 / m := by positivity
  have h := fractional_second_moment_holder hδ hη hδ0 hη0 ha hb (by ring : (2 - 4 / m) + 4 / m = 2)
  have h1 : (2 - 4 / m) / 2 = 1 - 2 / m := by ring
  have h2 : (4 / m) / 2 = 2 / m := by ring
  simpa only [h1, h2] using h

/-- The logarithmic exponent selected in the original mixed-moment proof. -/
def mixedMomentExponent (x : ℝ) : ℝ :=
  2 * Real.log (Real.exp 1 + Real.sqrt x)

theorem mixedMomentExponent_ge_two (x : ℝ) : 2 ≤ mixedMomentExponent x := by
  have h := Real.log_le_log (Real.exp_pos 1)
    (le_add_of_nonneg_right (Real.sqrt_nonneg x))
  rw [Real.log_exp] at h
  dsimp only [mixedMomentExponent]
  linarith

theorem mixedMomentExponent_gt_two {x : ℝ} (hx : 0 < x) :
    2 < mixedMomentExponent x := by
  have h := Real.log_lt_log (Real.exp_pos 1)
    (lt_add_of_pos_right (Real.exp 1) (Real.sqrt_pos.mpr hx))
  rw [Real.log_exp] at h
  dsimp only [mixedMomentExponent]
  linarith

/-- The effective-dimension factor is uniformly bounded at the actual
logarithmic exponent; the zero-dimension boundary is included. -/
theorem mixedMomentExponent_rpow_le_exp_two {x : ℝ} (hx : 0 ≤ x) :
    x ^ (2 / mixedMomentExponent x) ≤ Real.exp 2 := by
  have hm : 0 < mixedMomentExponent x := lt_of_lt_of_le (by norm_num)
    (mixedMomentExponent_ge_two x)
  by_cases hx0 : x = 0
  · rw [hx0] at hm
    rw [hx0, Real.zero_rpow (div_pos (by norm_num : (0 : ℝ) < 2) hm).ne']
    exact (Real.exp_pos 2).le
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  let B := Real.log (Real.exp 1 + Real.sqrt x)
  have hB : 0 < B := by
    have ht := mixedMomentExponent_ge_two x
    change 2 ≤ 2 * B at ht
    linarith
  have hlog : Real.log x ≤ 2 * B := by
    have h := Real.log_le_log (Real.sqrt_pos.mpr hxpos)
      (le_add_of_nonneg_left (Real.exp_pos 1).le)
    rw [Real.log_sqrt hx] at h
    dsimp only [B]
    linarith
  rw [Real.rpow_def_of_pos hxpos]
  apply Real.exp_le_exp.mpr
  have he : 2 / mixedMomentExponent x = 1 / B := by
    change 2 / (2 * B) = 1 / B
    field_simp
  rw [he]
  simpa only [div_eq_mul_inv, one_div, one_mul] using (div_le_iff₀ hB).mpr hlog

/-- Substitution of the two actual second-moment scales into Holder.
The constant may be zero, and the variance scale may vanish. -/
theorem mixed_second_moment_le_of_bounds {δ η : Ω → ℝ}
    (hδ : MemLp δ 2 μ) (hη : MemLp η 2 μ)
    (hδ0 : 0 ≤ᵐ[μ] δ) (hη0 : 0 ≤ᵐ[μ] η)
    {m C v x : ℝ} (hm : 2 < m) (hC : 0 ≤ C) (hv : 0 ≤ v) (hx : 0 ≤ x)
    (hU : (∫ ω, δ ω ^ 2 ∂μ) ≤ C * v)
    (hV : (∫ ω, η ω ^ 2 ∂μ) ≤ C * v * x) :
    (∫ ω, δ ω ^ (2 - 4 / m) * η ω ^ (4 / m) ∂μ) ≤
      C * v * x ^ (2 / m) := by
  have hm0 : 0 < m := by linarith
  have hb : 0 ≤ 2 / m := by positivity
  have ha : 0 ≤ 1 - 2 / m := by
    have ht : 2 / m < 1 := (div_lt_one hm0).mpr hm
    linarith
  have hh := (mixed_second_moment_holder hδ hη hδ0 hη0 hm).2
  calc
    _ ≤ (C * v) ^ (1 - 2 / m) * (C * v * x) ^ (2 / m) :=
      hh.trans (mul_le_mul
        (Real.rpow_le_rpow (integral_nonneg fun ω => sq_nonneg (δ ω)) hU ha)
        (Real.rpow_le_rpow (integral_nonneg fun ω => sq_nonneg (η ω)) hV hb)
        (Real.rpow_nonneg (integral_nonneg fun ω => sq_nonneg (η ω)) _)
        (Real.rpow_nonneg (mul_nonneg hC hv) _))
    _ = C * v * x ^ (2 / m) := by
      rw [Real.mul_rpow (mul_nonneg hC hv) hx, ← mul_assoc,
        ← Real.rpow_add_of_nonneg (mul_nonneg hC hv) ha hb,
        show (1 - 2 / m) + 2 / m = 1 by ring, Real.rpow_one]

/-- The exact logarithmic optimization: after multiplication by m², the
mixed moment is bounded by a universal constant times the squared original
gamma scale. This is a derived moment estimate, with no probability-rate
or mixed-moment certificate among its inputs. -/
theorem logarithmic_mixed_second_moment_le {δ η : Ω → ℝ}
    (hδ : MemLp δ 2 μ) (hη : MemLp η 2 μ)
    (hδ0 : 0 ≤ᵐ[μ] δ) (hη0 : 0 ≤ᵐ[μ] η)
    {C v x : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v) (hx : 0 < x)
    (hU : (∫ ω, δ ω ^ 2 ∂μ) ≤ C * v)
    (hV : (∫ ω, η ω ^ 2 ∂μ) ≤ C * v * x) :
    mixedMomentExponent x ^ 2 *
      (∫ ω, δ ω ^ (2 - 4 / mixedMomentExponent x) *
        η ω ^ (4 / mixedMomentExponent x) ∂μ) ≤
      (4 * C * Real.exp 2) *
        (Real.sqrt v * Real.log (Real.exp 1 + Real.sqrt x)) ^ 2 := by
  have hi := mixed_second_moment_le_of_bounds hδ hη hδ0 hη0
    (mixedMomentExponent_gt_two hx) hC hv hx.le hU hV
  have hxbound := mixedMomentExponent_rpow_le_exp_two hx.le
  have hm := mul_le_mul_of_nonneg_left
    (hi.trans (mul_le_mul_of_nonneg_left hxbound (mul_nonneg hC hv)))
    (sq_nonneg (mixedMomentExponent x))
  refine hm.trans_eq ?_
  dsimp only [mixedMomentExponent]
  simp only [mul_pow, Real.sq_sqrt hv]
  ring

/-- A measurable scalar envelope for the Schatten endpoint. It is useful
even when measurability of the endpoint infimum itself is not needed. -/
def mixedMomentAmplitude (m : ℝ) (δ η : Ω → ℝ) (ω : Ω) : ℝ :=
  m * δ ω ^ (1 - 2 / m) * η ω ^ (2 / m)

omit [MeasurableSpace Ω] in
theorem mixedMomentAmplitude_sq {δ η : Ω → ℝ} {m : ℝ} {ω : Ω}
    (hδ : 0 ≤ δ ω) (hη : 0 ≤ η ω) :
    mixedMomentAmplitude m δ η ω ^ 2 =
      m ^ 2 * (δ ω ^ (2 - 4 / m) * η ω ^ (4 / m)) := by
  have hd : (δ ω ^ (1 - 2 / m)) ^ 2 = δ ω ^ (2 - 4 / m) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hδ]
    congr 1
    ring
  have he : (η ω ^ (2 / m)) ^ 2 = η ω ^ (4 / m) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hη]
    congr 1
    ring
  simp only [mixedMomentAmplitude, mul_pow, hd, he]
  ring

/-- Genuine L2 measurability and integrability of the pointwise envelope,
derived solely from the two L2 factors. -/
theorem mixedMomentAmplitude_memLp {δ η : Ω → ℝ}
    (hδ : MemLp δ 2 μ) (hη : MemLp η 2 μ)
    (hδ0 : 0 ≤ᵐ[μ] δ) (hη0 : 0 ≤ᵐ[μ] η) {m : ℝ} (hm : 2 < m) :
    MemLp (mixedMomentAmplitude m δ η) 2 μ := by
  have hm0 : 0 < m := by linarith
  have ha : 0 ≤ 1 - 2 / m := by
    have ht := (div_lt_one hm0).mpr hm
    linarith
  have hb : 0 ≤ 2 / m := by positivity
  have hsδ := (Real.continuous_rpow_const ha).comp_aestronglyMeasurable
    hδ.aestronglyMeasurable
  have hsη := (Real.continuous_rpow_const hb).comp_aestronglyMeasurable
    hη.aestronglyMeasurable
  have hs : AEStronglyMeasurable (mixedMomentAmplitude m δ η) μ :=
    (hsδ.const_mul m).mul hsη
  apply (memLp_two_iff_integrable_sq hs).mpr
  apply ((mixed_second_moment_holder hδ hη hδ0 hη0 hm).1.const_mul (m ^ 2)).congr
  filter_upwards [hδ0, hη0] with ω hd he
  exact (mixedMomentAmplitude_sq hd he).symm

/-- A true second moment for the measurable Schatten envelope, at the
original logarithmic exponent. No measurability of an infimum is assumed. -/
theorem integral_mixedMomentAmplitude_sq_le {δ η : Ω → ℝ}
    (hδ : MemLp δ 2 μ) (hη : MemLp η 2 μ)
    (hδ0 : 0 ≤ᵐ[μ] δ) (hη0 : 0 ≤ᵐ[μ] η)
    {C v x : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v) (hx : 0 < x)
    (hU : (∫ ω, δ ω ^ 2 ∂μ) ≤ C * v)
    (hV : (∫ ω, η ω ^ 2 ∂μ) ≤ C * v * x) :
    (∫ ω, mixedMomentAmplitude (mixedMomentExponent x) δ η ω ^ 2 ∂μ) ≤
      (4 * C * Real.exp 2) *
        (Real.sqrt v * Real.log (Real.exp 1 + Real.sqrt x)) ^ 2 := by
  have heq : (∫ ω, mixedMomentAmplitude (mixedMomentExponent x) δ η ω ^ 2 ∂μ) =
      mixedMomentExponent x ^ 2 *
        (∫ ω, δ ω ^ (2 - 4 / mixedMomentExponent x) *
          η ω ^ (4 / mixedMomentExponent x) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hδ0, hη0] with ω hd he
    exact mixedMomentAmplitude_sq hd he
  rw [heq]
  exact logarithmic_mixed_second_moment_le hδ hη hδ0 hη0 hC hv hx hU hV

/-- The actual manuscript scales: an operator-norm second moment of order
L ell/n and an HS second moment of order L N/n give the original gamma².
No lower bound on either variance scale is imposed. -/
theorem integral_mixedMomentAmplitude_sq_le_originalBiasGamma {δ η : Ω → ℝ}
    (hδ : MemLp δ 2 μ) (hη : MemLp η 2 μ)
    (hδ0 : 0 ≤ᵐ[μ] δ) (hη0 : 0 ≤ᵐ[μ] η)
    {C L n N : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hn : 0 < n) (hN : 0 < N)
    (hU : (∫ ω, δ ω ^ 2 ∂μ) ≤ C * (L * dimensionLog N / n))
    (hV : (∫ ω, η ω ^ 2 ∂μ) ≤ C * (L * N / n)) :
    (∫ ω, mixedMomentAmplitude (mixedMomentExponent (N / dimensionLog N)) δ η ω ^ 2 ∂μ) ≤
      (4 * C * Real.exp 2) * originalBiasGamma L n N ^ 2 := by
  have hell : 0 < dimensionLog N := lt_of_lt_of_le zero_lt_one (one_le_dimensionLog hN.le)
  have he : C * (L * N / n) = C * (L * dimensionLog N / n) * (N / dimensionLog N) := by
    field_simp
  have hh := integral_mixedMomentAmplitude_sq_le hδ hη hδ0 hη0 hC
    (div_nonneg (mul_nonneg hL hell.le) hn.le) (div_pos hN hell) hU (hV.trans_eq he)
  simpa only [originalBiasGamma] using hh

end
end KernelSeq
