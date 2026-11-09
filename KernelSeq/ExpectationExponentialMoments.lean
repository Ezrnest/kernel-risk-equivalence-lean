import KernelSeq.NormalizedCovariance
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Genuine second moments from exponential threshold tails

The layer-cake formula and an actual Gamma integral supply the moment bound;
no integrated-tail or uniform-integrability certificate is assumed.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace KernelSeq
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem linear_exponential_threshold_tail {f : Ω → ℝ} {a K : ℝ}
    (ha : 0<a) (hK : 1≤K)
    (htail : ∀ z : ℝ, 0≤z → P {ω | a*(1+z)<f ω} ≤ ENNReal.ofReal (K*Real.exp (-z)))
    {t : ℝ} (_ht : 0≤t) :
    P {ω | t<f ω} ≤ ENNReal.ofReal (K*Real.exp (1-t/a)) := by
  by_cases hta : t<a
  · have he : 1≤Real.exp (1-t/a) := Real.one_le_exp_iff.mpr (by
      have hh := (div_lt_one ha).mpr hta
      linarith)
    have hb : 1≤K*Real.exp (1-t/a) := hK.trans (le_mul_of_one_le_right (by linarith) he)
    exact (measure_mono (subset_univ _)).trans (by
      rw [measure_univ, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hb)
  · let z := t/a-1
    have hz : 0≤z := by dsimp only [z]; exact sub_nonneg.mpr ((one_le_div ha).mpr (le_of_not_gt hta))
    have he : a*(1+z)=t := by dsimp only [z]; field_simp; ring
    have harg : -z=1-t/a := by dsimp only [z]; ring
    simpa only [he, harg] using htail z hz

/-- Actual layer-cake integration of an exponential linear threshold.
The constant and scaling are explicit and valid also for zero random variables. -/
theorem integral_sq_le_of_linear_exponential_tail {f : Ω → ℝ} {a K : ℝ}
    (hf : MemLp f 2 P) (hfn : 0≤ᵐ[P] f) (ha : 0<a) (hK : 1≤K)
    (htail : ∀ z : ℝ, 0≤z → P {ω | a*(1+z)<f ω} ≤ ENNReal.ofReal (K*Real.exp (-z))) :
    (∫ ω, f ω^2 ∂P) ≤ (2*K*Real.exp 1)*a^2 := by
  let C := 2*K*Real.exp 1
  have hC : 0≤C := by dsimp only [C]; positivity
  have hGamma : Real.Gamma 2=1 := by norm_num [Real.Gamma_nat_eq_factorial]
  have hcalc : (∫ t : ℝ in Ioi 0, t*Real.exp (-(a⁻¹*t))) = a^2 := by
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=2) (r:=a⁻¹)
      (by norm_num) (inv_pos.mpr ha)
    simpa only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one, one_div, inv_inv,
      Real.rpow_two, hGamma, mul_one] using hh
  have hg : IntegrableOn (fun t : ℝ => t*Real.exp (-(a⁻¹*t))) (Ioi 0) := by
    by_contra hnot
    rw [integral_undef hnot] at hcalc
    exact (sq_pos_of_pos ha).ne' hcalc.symm
  have hgC := hg.const_mul C
  have hgn : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun t => C*(t*Real.exp (-(a⁻¹*t)))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg hC (mul_nonneg ht.le (Real.exp_pos _).le)
  have hprimitive (x : ℝ) : (∫ t in 0..x, 2*t) = x^2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul P hfn hf.1.aemeasurable
    (g := fun t : ℝ => 2*t) (fun t _ => (by fun_prop : Continuous (fun t : ℝ => 2*t)).intervalIntegrable 0 t)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg (by norm_num) ht.le)
  simp_rw [hprimitive] at hlayer
  have hbound : (∫⁻ ω, ENNReal.ofReal (f ω^2) ∂P) ≤ ENNReal.ofReal (C*a^2) := by
    rw [hlayer]
    calc
      _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (C*(t*Real.exp (-(a⁻¹*t)))) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        calc
          _ ≤ ENNReal.ofReal (K*Real.exp (1-t/a))*ENNReal.ofReal (2*t) := by
            gcongr
            exact linear_exponential_threshold_tail ha hK htail ht.le
          _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity : 0≤K*Real.exp (1-t/a))]
            congr 1
            have he : 1-t/a=1+(-(a⁻¹*t)) := by ring
            rw [he, Real.exp_add]
            dsimp only [C]
            ring
      _ = ENNReal.ofReal (C*a^2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hgC hgn, integral_const_mul, hcalc]
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg a))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Eventually.of_forall (fun ω => sq_nonneg (f ω)))]
  exact hbound

end
end KernelSeq
