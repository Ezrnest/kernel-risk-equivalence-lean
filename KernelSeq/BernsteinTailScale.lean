import KernelSeq.ConcentrationScale
import KernelSeq.ProbabilityCalculus

/-!
# Explicit exponential thresholds for the intrinsic Bernstein expression

Scalar exponential inversion for the covariance operator-norm tail bound.
-/

namespace KernelSeq

open Filter MeasureTheory Topology
open scoped ENNReal

/-- A convenient Bernstein threshold, with harmless explicit constants. -/
noncomputable def bernsteinThreshold (v R s : ℝ) : ℝ :=
  2 * Real.sqrt (v * s) + 2 * R * s

theorem bernsteinThreshold_nonneg {v R s : ℝ} (hR : 0 ≤ R) (hs : 0 ≤ s) :
    0 ≤ bernsteinThreshold v R s := by
  unfold bernsteinThreshold
  positivity

/-- This threshold lies above the lower range required by the external
finite-dimensional leaf whenever its exponential parameter is at least one. -/
theorem bernsteinThreshold_admissible {v R s : ℝ}
    (hv : 0 ≤ v) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    Real.sqrt v + R / 3 ≤ bernsteinThreshold v R s := by
  have hvs : v ≤ v * s := le_mul_of_one_le_right hv hs
  have hroot := Real.sqrt_le_sqrt hvs
  have hRs : R ≤ R * s := le_mul_of_one_le_right hR hs
  unfold bernsteinThreshold
  nlinarith [Real.sqrt_nonneg v, Real.sqrt_nonneg (v * s)]

/-- The exact quadratic inequality behind exponential inversion, without an
asymptotic big-O assertion. -/
theorem bernsteinThreshold_exponent_ge {v R s : ℝ}
    (hv : 0 < v) (hR : 0 ≤ R) (hs : 0 ≤ s) :
    s ≤ bernsteinThreshold v R s ^ 2 /
      (2 * (v + R * bernsteinThreshold v R s / 3)) := by
  have ht := bernsteinThreshold_nonneg (v := v) hR hs
  have hden : 0 < 2 * (v + R * bernsteinThreshold v R s / 3) := by positivity
  apply (le_div_iff₀ hden).mpr
  have hsq := Real.sq_sqrt (mul_nonneg hv.le hs)
  have hprod : 0 ≤ R * s * Real.sqrt (v * s) := by positivity
  have hRs : 0 ≤ (R * s) ^ 2 := sq_nonneg _
  dsimp only [bernsteinThreshold]
  nlinarith

/-- Inserting the intrinsic logarithm gives an explicit dimension-free tail
envelope `8 exp(-z)`. The original trace/norm ratio `d` remains exact. -/
theorem intrinsicBernstein_expression_le {d v R z : ℝ}
    (hd : 0 ≤ d) (hv : 0 < v) (hR : 0 ≤ R) (hz : 0 ≤ z) :
    8 * d * Real.exp (-(bernsteinThreshold v R (dimensionLog d + z) ^ 2) /
      (2 * (v + R * bernsteinThreshold v R (dimensionLog d + z) / 3))) ≤
      8 * Real.exp (-z) := by
  have hs : 0 ≤ dimensionLog d + z := by linarith [one_le_dimensionLog hd]
  have he := bernsteinThreshold_exponent_ge hv hR hs
  have he' : -(bernsteinThreshold v R (dimensionLog d + z) ^ 2) /
      (2 * (v + R * bernsteinThreshold v R (dimensionLog d + z) / 3)) ≤
      -(dimensionLog d + z) := by simpa only [neg_div] using neg_le_neg he
  have hlog : Real.exp (dimensionLog d) = Real.exp 1 + d :=
    Real.exp_log (by positivity)
  have hid : Real.exp (-(dimensionLog d + z)) =
      (Real.exp (dimensionLog d))⁻¹ * Real.exp (-z) := by
    rw [neg_add, Real.exp_add, Real.exp_neg]
  calc
    _ ≤ 8 * d * Real.exp (-(dimensionLog d + z)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he') (by positivity)
    _ = (8 * (d / (Real.exp 1 + d))) * Real.exp (-z) := by
      rw [hid, hlog]
      ring
    _ ≤ 8 * Real.exp (-z) := by
      have hratio : d / (Real.exp 1 + d) ≤ 1 :=
        (div_le_one (by positivity : 0 < Real.exp 1 + d)).mpr (by linarith [Real.exp_pos 1])
      exact mul_le_mul_of_nonneg_right (by linarith : 8 * (d / (Real.exp 1 + d)) ≤ 8)
        (Real.exp_pos _).le

/-- Vanishing deterministic thresholds at every fixed exponential confidence
level yield convergence in measure. No measurability hypothesis is added to
the outer tail comparison. -/
theorem tendstoInMeasure_zero_of_exponential_thresholds
    {J Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    {l : Filter J} (P : Measure Ω) (f : J → Ω → E) (T : ℝ → J → ℝ)
    (hT : ∀ z : ℝ, 0 ≤ z → Tendsto (T z) l (𝓝 0))
    (htail : ∀ z : ℝ, 0 ≤ z → ∀ᶠ i in l,
      P {ω | T z i < ‖f i ω‖} ≤ ENNReal.ofReal (8 * Real.exp (-z))) :
    TendstoInMeasure P f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_zero]
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ζ hζ
  obtain ⟨r, hr, hrζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hζ
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hexp : Tendsto (fun z : ℝ => 8 * Real.exp (-z)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  obtain ⟨z, hz, hzr⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (hexp.eventually (eventually_lt_nhds hrpos))).exists
  filter_upwards [htail z hz, (hT z hz).eventually (eventually_lt_nhds hε)] with i hi hTi
  have hb : P {ω | ε ≤ ‖f i ω‖} ≤ ENNReal.ofReal (8 * Real.exp (-z)) :=
    (measure_mono (fun ω hω => hTi.trans_le hω)).trans hi
  exact hb.trans (by
    apply le_trans (ENNReal.ofReal_le_ofReal hzr.le)
    simpa only [ENNReal.ofReal_coe_nnreal] using hrζ.le)

end KernelSeq
