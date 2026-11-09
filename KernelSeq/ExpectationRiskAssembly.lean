import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual L1 assembly of good- and bad-event risk estimates

The good-event normalized absolute error, the bad-event normalized risk and
the bad-event probability control the full normalized L1 error. Genuine
Bochner integration then gives the normalized expectation-risk limit. The
denominator is only eventually positive and may tend to zero.
-/

open MeasureTheory Filter Topology

namespace KernelSeq
noncomputable section

theorem normalized_abs_risk_le_risk_add_one (R D : ℝ) (hR : 0 ≤ R) (hD : 0 < D) :
    |R - D| / D ≤ R / D + 1 := by
  have h := abs_sub R D
  rw [abs_of_nonneg hR, abs_of_pos hD] at h
  calc
    _ ≤ (R + D) / D := div_le_div_of_nonneg_right h hD.le
    _ = _ := by rw [add_div, div_self hD.ne']

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A genuine integral split bounds the normalized full L1 error, with
nonnegativity required only almost everywhere. -/
theorem integral_normalized_abs_risk_le_good_bad (R : Ω → ℝ) (D : ℝ)
    (G : Set Ω) (hG : MeasurableSet G) (hR : Integrable R P)
    (hR0 : ∀ᵐ ω ∂P, 0 ≤ R ω) (hD : 0 < D) :
    (∫ ω, |R ω - D| / D ∂P) ≤
      (∫ ω in G, |R ω - D| / D ∂P) +
        (∫ ω in Gᶜ, R ω / D ∂P) + (P Gᶜ).toReal := by
  have hAbs : Integrable (fun ω => |R ω - D| / D) P := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hR.sub (integrable_const D)).norm.div_const D
  have hDiv : Integrable (fun ω => R ω / D) P := hR.div_const D
  rw [← integral_add_compl hG hAbs]
  have hb : (∫ ω in Gᶜ, |R ω - D| / D ∂P) ≤
      (∫ ω in Gᶜ, R ω / D + 1 ∂P) := by
    apply integral_mono_ae hAbs.restrict (hDiv.add (integrable_const 1)).restrict
    exact ae_restrict_of_ae (hR0.mono fun ω hω => normalized_abs_risk_le_risk_add_one (R ω) D hω hD)
  have hc : (∫ ω in Gᶜ, R ω / D + 1 ∂P) =
      (∫ ω in Gᶜ, R ω / D ∂P) + (P Gᶜ).toReal := by
    rw [integral_add hDiv.restrict (integrable_const 1)]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one]
  linarith

/-- The absolute error of the genuinely integrated risk ratio is bounded
by the normalized L1 error. This is not a risk identity premise. -/
theorem integral_risk_ratio_error_le (R : Ω → ℝ) (D : ℝ)
    (hR : Integrable R P) (hD : 0 < D) :
    |(∫ ω, R ω ∂P) / D - 1| ≤ ∫ ω, |R ω - D| / D ∂P := by
  have heq : (∫ ω, R ω / D - 1 ∂P) = (∫ ω, R ω ∂P) / D - 1 := by
    rw [integral_sub (hR.div_const D) (integrable_const 1), integral_div]
    simp
  rw [← heq]
  calc
    _ ≤ ∫ ω, |R ω / D - 1| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => R ω / D - 1)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change |R ω / D - 1| = |R ω - D| / D
        have hi : R ω / D - 1 = (R ω - D) / D := by field_simp
        rw [hi, abs_div, abs_of_pos hD]

variable {J : Type*} {l : Filter J}

/-- True expectation-risk assembly on an arbitrary index filter. The
three inputs are precisely the proved good-event L1 error, bad-event risk
and bad-event probability estimates, rather than the desired full limit. -/
theorem risk_expectation_from_good_bad
    (R : J → Ω → ℝ) (D : J → ℝ) (G : J → Set Ω)
    (hG : ∀ i, MeasurableSet (G i)) (hR : ∀ i, Integrable (R i) P)
    (hR0 : ∀ i, ∀ᵐ ω ∂P, 0 ≤ R i ω) (hD : ∀ᶠ i in l, 0 < D i)
    (hgood : Tendsto (fun i => ∫ ω in G i, |R i ω - D i| / D i ∂P) l (𝓝 0))
    (hbad : Tendsto (fun i => ∫ ω in (G i)ᶜ, R i ω / D i ∂P) l (𝓝 0))
    (hprob : Tendsto (fun i => (P (G i)ᶜ).toReal) l (𝓝 0)) :
    Tendsto (fun i => (∫ ω, R i ω ∂P) / D i) l (𝓝 1) ∧
      Tendsto (fun i => ∫ ω, |R i ω - D i| / D i ∂P) l (𝓝 0) := by
  have hL1 : Tendsto (fun i => ∫ ω, |R i ω - D i| / D i ∂P) l (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa only [zero_add] using (hgood.add hbad).add hprob)
    · filter_upwards [hD] with i hiD
      exact integral_nonneg fun ω => div_nonneg (abs_nonneg _) hiD.le
    · filter_upwards [hD] with i hiD
      exact integral_normalized_abs_risk_le_good_bad (R i) (D i) (G i) (hG i) (hR i) (hR0 i) hiD
  refine ⟨?_, hL1⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) _ hL1
  filter_upwards [hD] with i hiD
  simpa only [Real.norm_eq_abs] using integral_risk_ratio_error_le (R i) (D i) (hR i) hiD

/-- Equivalent outside-the-integral normalization, convenient for the
actual bad-risk envelope and good-event comparison integrals. -/
theorem risk_expectation_from_good_bad_integrals
    (R : J → Ω → ℝ) (D : J → ℝ) (G : J → Set Ω)
    (hG : ∀ i, MeasurableSet (G i)) (hR : ∀ i, Integrable (R i) P)
    (hR0 : ∀ i, ∀ᵐ ω ∂P, 0 ≤ R i ω) (hD : ∀ᶠ i in l, 0 < D i)
    (hgood : Tendsto (fun i => (∫ ω in G i, |R i ω - D i| ∂P) / D i) l (𝓝 0))
    (hbad : Tendsto (fun i => (∫ ω in (G i)ᶜ, R i ω ∂P) / D i) l (𝓝 0))
    (hprob : Tendsto (fun i => (P (G i)ᶜ).toReal) l (𝓝 0)) :
    Tendsto (fun i => (∫ ω, R i ω ∂P) / D i) l (𝓝 1) ∧
      Tendsto (fun i => (∫ ω, |R i ω - D i| ∂P) / D i) l (𝓝 0) := by
  have h := risk_expectation_from_good_bad R D G hG hR hR0 hD
    (by simpa only [integral_div] using hgood)
    (by simpa only [integral_div] using hbad) hprob
  simpa only [integral_div] using h

end
end KernelSeq
