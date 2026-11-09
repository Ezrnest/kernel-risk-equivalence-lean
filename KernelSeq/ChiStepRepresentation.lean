import KernelSeq.ChiMikhlin
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual chi as an integral of strict step profiles

Convexity of the exponential proves nonnegativity of the genuine derivative.
The actual limits at both infinities, together with the fundamental theorem
of calculus for nonnegative derivatives, give genuine integrability and total
mass one. No derivative-integrability or step-representation certificate is
assumed.
-/

open Set Filter MeasureTheory Topology

namespace KernelSeq
noncomputable section

/-- The stable derivative numerator is nonnegative by convexity of `exp`.
This includes the harmless zero-denominator convention at `x = 0`. -/
theorem chiTailFirst_nonneg {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ chiTailFirst a x := by
  have hj := convexOn_exp.2 (mem_univ (-a * x)) (mem_univ (-(a + 1) * x))
    ha0 (show 0 ≤ 1 - a by linarith) (show a + (1 - a) = 1 by ring)
  have hm : a * (-a * x) + (1 - a) * (-(a + 1) * x) = -x := by ring
  simp only [smul_eq_mul, hm] at hj
  exact div_nonneg (sub_nonneg.mpr hj) (sq_nonneg _)

/-- The actual removable chi has a nonnegative derivative everywhere,
including zero. -/
theorem interactionChi_deriv_nonneg {α : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (z : ℝ) :
    0 ≤ deriv (interactionChi α) z := by
  have hne : ∀ x : ℝ, x ≠ 0 → 0 ≤ deriv (interactionChi α) x := by
    intro x hx
    rw [interactionChi_deriv_pos α hx]
    exact chiTailFirst_nonneg (by linarith) (by linarith)
  by_cases hz : z = 0
  · subst z
    have hd : Continuous (deriv (interactionChi α)) :=
      (interactionChi_contDiff α (n := 1)).continuous_deriv le_rfl
    have ht : Tendsto (deriv (interactionChi α)) (𝓝[≠] (0 : ℝ))
        (𝓝 (deriv (interactionChi α) 0)) := hd.continuousAt.tendsto.mono_left inf_le_left
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hne x hx
  · exact hne z hz

/-- Monotonicity is derived from the genuine derivative, not postulated. -/
theorem interactionChi_monotone {α : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 2) :
    Monotone (interactionChi α) :=
  monotone_of_deriv_nonneg (fun z => (interactionChi_analyticAt α z).differentiableAt)
    (interactionChi_deriv_nonneg hα0 hα2)

/-- The actual stable tail ratio tends to zero for every positive decay
parameter. -/
theorem chiTail_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (chiTail a) atTop (𝓝 0) := by
  have haexp : Tendsto (fun x : ℝ => Real.exp (-a * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (by linarith : -a < 0)).2 tendsto_id)
  have hnum := Real.tendsto_exp_neg_atTop_nhds_zero.sub haexp
  have hden : Tendsto (fun x : ℝ => 1 - Real.exp (-x)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
  convert hnum.div hden (by norm_num : (1 : ℝ) - 0 ≠ 0) using 1 <;>
    first | rfl | norm_num

/-- The actual manuscript chi tends to zero at positive infinity. -/
theorem interactionChi_tendsto_atTop {α : ℝ} (hα0 : 0 < α) :
    Tendsto (interactionChi α) atTop (𝓝 0) := by
  apply (chiTail_tendsto_zero (show 0 < α / 2 by linarith)).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx
  exact (interactionChi_pos_formula α (ne_of_gt hx)).symm

/-- The actual manuscript chi tends to minus one at negative infinity. -/
theorem interactionChi_tendsto_atBot {α : ℝ} (hα2 : α < 2) :
    Tendsto (interactionChi α) atBot (𝓝 (-1)) := by
  have ht := (chiTail_tendsto_zero (show 0 < 1 - α / 2 by linarith)).const_sub (-1)
  have ht' : Tendsto (fun x : ℝ => -1 - chiTail (1 - α / 2) x) atTop (𝓝 (-1)) := by
    simpa only [sub_zero] using ht
  have hr : Tendsto (fun x : ℝ => interactionChi α (-x)) atTop (𝓝 (-1)) := by
    apply ht'.congr'
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx
    exact (interactionChi_neg_formula α (ne_of_gt hx)).symm
  simpa only [Function.comp_def, neg_neg] using hr.comp tendsto_neg_atBot_atTop

/-- The actual derivative is genuinely Lebesgue integrable. Nonnegativity
and the two actual limits establish this through the improper FTC. -/
theorem interactionChi_deriv_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    Integrable (deriv (interactionChi α)) := by
  have hα2 : α < 2 := by linarith
  have hd (x : ℝ) : HasDerivAt (interactionChi α) (deriv (interactionChi α) x) x :=
    (interactionChi_analyticAt α x).differentiableAt.hasDerivAt
  have hright : IntegrableOn (deriv (interactionChi α)) (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x)
      (fun x _ => interactionChi_deriv_nonneg hα0.le hα2.le x)
      (interactionChi_tendsto_atTop hα0)
  have hreflect (x : ℝ) : HasDerivAt (fun y : ℝ => -interactionChi α (-y))
      (deriv (interactionChi α) (-x)) x := by
    have hh := ((hd (-x)).comp x (hasDerivAt_id x).neg).neg
    convert hh using 1 <;> first | rfl | ring
  have hlimreflect : Tendsto (fun x : ℝ => -interactionChi α (-x)) atTop (𝓝 1) := by
    have hh := ((interactionChi_tendsto_atBot hα2).comp tendsto_neg_atTop_atBot).neg
    simpa only [Function.comp_def, neg_neg] using hh
  have hleftReflect : IntegrableOn (fun x : ℝ => deriv (interactionChi α) (-x)) (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hreflect x)
      (fun x _ => interactionChi_deriv_nonneg hα0.le hα2.le (-x)) hlimreflect
  have hleft : IntegrableOn (deriv (interactionChi α)) (Iio (0 : ℝ)) := by
    apply ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp
    have hset : (Neg.neg : ℝ → ℝ) ⁻¹' Iio (0 : ℝ) = Ioi (0 : ℝ) := by ext x; simp
    rw [hset]
    exact hleftReflect
  have hleftClosed : IntegrableOn (deriv (interactionChi α)) (Iic (0 : ℝ)) :=
    (integrableOn_Iic_iff_integrableOn_Iio (by finiteness)).mpr hleft
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hleftClosed, hright⟩

/-- The genuine derivative is a probability density: its integral is one. -/
theorem interactionChi_deriv_integral_eq_one {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∫ x : ℝ, deriv (interactionChi α) x) = 1 := by
  have hi := integral_of_hasDerivAt_of_tendsto
    (fun x => (interactionChi_analyticAt α x).differentiableAt.hasDerivAt)
    (interactionChi_deriv_integrable hα0 hα1)
    (interactionChi_tendsto_atBot (by linarith : α < 2))
    (interactionChi_tendsto_atTop hα0)
  simpa only [sub_neg_eq_add, zero_add] using hi

/-- The true L1 norm of the derivative is exactly one, uniformly in α. -/
theorem interactionChi_deriv_norm_integral_eq_one {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∫ x : ℝ, ‖deriv (interactionChi α) x‖) = 1 := by
  calc
    _ = ∫ x : ℝ, deriv (interactionChi α) x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => Real.norm_of_nonneg
        (interactionChi_deriv_nonneg hα0.le (by linarith : α ≤ 2) x)
    _ = 1 := interactionChi_deriv_integral_eq_one hα0 hα1

/-- Actual strict-step representation of the original removable profile.
The set integral is over `r < z`, including at `z = 0`. -/
theorem interactionChi_step_representation {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (z : ℝ) :
    interactionChi α z = -1 + ∫ r in Iio z, deriv (interactionChi α) r := by
  have hi := integral_Iic_of_hasDerivAt_of_tendsto'
    (fun x (_ : x ∈ Iic z) => (interactionChi_analyticAt α x).differentiableAt.hasDerivAt)
    (interactionChi_deriv_integrable hα0 hα1).integrableOn
    (interactionChi_tendsto_atBot (by linarith : α < 2))
  rw [integral_Iic_eq_integral_Iio] at hi
  linarith

/-- The same genuine representation as an ordinary integral of the actual
strict-step kernel, convenient for finite HS-valued Schur integration. -/
theorem interactionChi_step_representation_indicator {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (z : ℝ) :
    interactionChi α z = -1 + ∫ r : ℝ, if r < z then deriv (interactionChi α) r else 0 := by
  rw [interactionChi_step_representation hα0 hα1 z, ← integral_indicator measurableSet_Iio]
  rfl

end
end KernelSeq
