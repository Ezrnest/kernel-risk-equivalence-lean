import KernelSeq.SpectralSumIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Weighted integration for an absolutely continuous source profile

The identity is proved by genuine signed Fubini applied to the original
absolutely continuous primitive. This also establishes absolute integrability
of the second weighted integral. No pointwise differentiability assumption,
prescribed integration-by-parts identity or integrability of that second
integral is required.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped Topology
noncomputable section

private theorem integrable_upper_power_kernel {γ v : ℝ} (hγ : 0 < γ) (hv : 0 < v)
    (c : ℝ) :
    IntegrableOn ((Ici v).indicator (fun u : ℝ => c * u^(-γ-1))) (Ioi (0 : ℝ)) := by
  have hi : IntegrableOn (fun u : ℝ => c * u^(-γ-1)) (Ici v) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) hv).const_mul c
  exact (hi.integrable_indicator measurableSet_Ici).restrict

private theorem integral_upper_power_kernel {γ v : ℝ} (hγ : 0 < γ) (hv : 0 < v)
    (c : ℝ) :
    (∫ u in Ioi (0 : ℝ), (Ici v).indicator (fun u : ℝ => c * u^(-γ-1)) u) =
      c * (v^(-γ) / γ) := by
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have he : Ici v ∩ Ioi (0 : ℝ) = Ici v := by
    exact inter_eq_left.mpr (fun _ hu => hv.trans_le hu)
  rw [he, integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_Ioi_rpow_of_lt (by linarith) hv]
  congr 1
  rw [show -γ-1+1 = -γ by ring]
  ring

/-- The weighted Hardy/Fubini identity for the actual a.e. derivative of a
locally absolutely continuous function. The second weighted integral is
proved absolutely integrable from the first one. In particular the result
needs no additional endpoint or everywhere-differentiability premises. -/
theorem weighted_ac_integrable_and_integral
    (G : ℝ → ℝ) (hG0 : G 0 = 0)
    (hac : ∀ R, 0 ≤ R → AbsolutelyContinuousOnInterval G 0 R)
    {γ : ℝ} (hγ : 0 < γ)
    (hi : IntegrableOn (fun u => u^(-γ) * |deriv G u|) (Ioi (0 : ℝ))) :
    IntegrableOn (fun u => G u * u^(-γ-1)) (Ioi (0 : ℝ)) ∧
      (∫ u in Ioi (0 : ℝ), u^(-γ) * deriv G u) =
        γ * ∫ u in Ioi (0 : ℝ), G u * u^(-γ-1) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let K : ℝ × ℝ → ℝ :=
    {z : ℝ × ℝ | z.1 ≤ z.2}.indicator (fun z => deriv G z.1 * z.2^(-γ-1))
  have hKm : AEStronglyMeasurable K (μ.prod μ) :=
    ((((measurable_deriv G).comp measurable_fst).mul
      (measurable_snd.pow_const (-γ-1))).indicator
        (measurableSet_le measurable_fst measurable_snd)).aestronglyMeasurable
  have hKu (v : ℝ) (hv : 0 < v) : Integrable (fun u => K (v,u)) μ := by
    change IntegrableOn ((Ici v).indicator (fun u : ℝ => deriv G v * u^(-γ-1))) (Ioi (0 : ℝ))
    exact integrable_upper_power_kernel hγ hv (deriv G v)
  have hKnorm (v : ℝ) (hv : 0 < v) :
      (∫ u, ‖K (v,u)‖ ∂μ) = |deriv G v| * (v^(-γ)/γ) := by
    rw [← integral_upper_power_kernel hγ hv |deriv G v|]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [K, Set.indicator, mem_setOf_eq, mem_Ici, Real.norm_eq_abs]
    split_ifs <;> simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu.le _), abs_zero]
  have hK : Integrable K (μ.prod μ) := by
    apply (integrable_prod_iff hKm).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact hKu v hv
    · apply (hi.div_const γ).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [hKnorm v hv]
      ring
  have hprimitive (u : ℝ) (hu : 0 < u) :
      (∫ v, K (v,u) ∂μ) = G u * u^(-γ-1) := by
    change (∫ v in Ioi (0 : ℝ),
      {z : ℝ × ℝ | z.1 ≤ z.2}.indicator
        (fun z => deriv G z.1 * z.2^(-γ-1)) (v,u)) = _
    have heq : (fun v => {z : ℝ × ℝ | z.1 ≤ z.2}.indicator
        (fun z => deriv G z.1 * z.2^(-γ-1)) (v,u)) =
        (Iic u).indicator (fun v => deriv G v * u^(-γ-1)) := by
      funext v
      rfl
    rw [heq, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hs : Iic u ∩ Ioi (0 : ℝ) = Ioc 0 u := by ext v; simp; tauto
    rw [hs, integral_mul_const, ← intervalIntegral.integral_of_le hu.le,
      (hac u hu.le).integral_deriv_eq_sub, hG0, sub_zero]
  have hsecond : Integrable (fun u => G u * u^(-γ-1)) μ := by
    apply hK.integral_prod_right.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hprimitive u hu
  refine ⟨hsecond, ?_⟩
  have hswap : (∫ u, G u * u^(-γ-1) ∂μ) =
      (∫ v, v^(-γ) * deriv G v ∂μ) / γ := by
    calc
      _ = ∫ u, ∫ v, K (v,u) ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact (hprimitive u hu).symm
      _ = ∫ v, ∫ u, K (v,u) ∂μ ∂μ :=
        (integral_integral_swap (f := fun v u => K (v,u)) hK).symm
      _ = ∫ v, (v^(-γ) * deriv G v) / γ ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        have he := integral_upper_power_kernel hγ hv (deriv G v)
        change (∫ u in Ioi (0 : ℝ),
          {z : ℝ × ℝ | z.1 ≤ z.2}.indicator
            (fun z => deriv G z.1 * z.2^(-γ-1)) (v,u)) = _
        convert he using 1 <;> first | rfl | ring
      _ = _ := integral_div γ _
  change (∫ u, u^(-γ) * deriv G u ∂μ) = γ * ∫ u, G u * u^(-γ-1) ∂μ
  rw [hswap]
  field_simp

end
end KernelSeq
