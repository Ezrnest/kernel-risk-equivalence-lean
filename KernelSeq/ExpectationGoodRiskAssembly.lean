import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# True good-event bias/variance risk assembly

Integral bounds for risk on the good-design event. The conditional-risk identity
`R = B + a V` identifies the genuine conditional variance energy. Its
integrability follows from those of risk and bias, rather than being a
further certificate. The bias and variance comparison limits are explicit
intermediate inputs here; the model-specific good-event theorems supply them.
The total deterministic risk may approach zero and the population bias may
vanish. No independence between the bias and variance errors is required.
-/

open MeasureTheory Filter Topology

namespace KernelSeq
noncomputable section

/-- The total-risk normalization needs no positive population bias. The
noise factor cancels in the relative variance term, and the larger total
denominator only improves its bound. -/
theorem good_risk_relative_error_le_bias_variance (B V b a q : ℝ)
    (hb : 0 ≤ b) (ha : 0 < a) (hq : 0 < q) :
    |(B + a * V) - (b + a * q)| / (b + a * q) ≤
      |B - b| / (b + a * q) + |V - q| / q := by
  have hD : 0 < b + a * q := add_pos_of_nonneg_of_pos hb (mul_pos ha hq)
  have htri : |(B + a * V) - (b + a * q)| ≤ |B - b| + a * |V - q| := by
    calc
      _ = |(B - b) + a * (V - q)| := by congr 1; ring
      _ ≤ |B - b| + |a * (V - q)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_pos ha]
  have hv : a * |V - q| / (b + a * q) ≤ |V - q| / q := by
    apply (div_le_div_iff₀ hD hq).mpr
    nlinarith [mul_nonneg hb (abs_nonneg (V - q))]
  exact (div_le_div_of_nonneg_right htri hD.le).trans
    (by rw [add_div]; exact add_le_add le_rfl hv)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The actual scalar variance is integrable whenever its conditional-risk
identity holds almost everywhere and risk and bias are integrable. -/
theorem integrable_variance_of_risk_bias_identity (R B V : Ω → ℝ) {a : ℝ}
    (ha : a ≠ 0) (hR : Integrable R P) (hB : Integrable B P)
    (hident : ∀ᵐ ω ∂P, R ω = B ω + a * V ω) : Integrable V P := by
  apply ((hR.sub hB).div_const a).congr
  filter_upwards [hident] with ω hω
  dsimp only [Pi.sub_apply]
  rw [hω]
  field_simp
  ring

/-- A true restricted integral comparison for conditional risk. No separate
integrability of `V` or of any relative absolute error is assumed: all are
derived from the genuine risk identity and the displayed risk/bias integrals. -/
theorem setIntegral_good_risk_relative_le_bias_variance [IsFiniteMeasure P]
    (R B V : Ω → ℝ) (b a q : ℝ) (G : Set Ω)
    (hb : 0 ≤ b) (ha : 0 < a) (hq : 0 < q)
    (hR : Integrable R P) (hB : Integrable B P)
    (hident : ∀ᵐ ω ∂P, R ω = B ω + a * V ω) :
    (∫ ω in G, |R ω - (b + a * q)| / (b + a * q) ∂P) ≤
      (∫ ω in G, |B ω - b| / (b + a * q) ∂P) + (∫ ω in G, |V ω - q| / q ∂P) := by
  have hV := integrable_variance_of_risk_bias_identity R B V ha.ne' hR hB hident
  have hRe : Integrable (fun ω => |R ω - (b + a * q)| / (b + a * q)) P := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hR.sub (integrable_const (b + a * q))).norm.div_const (b + a * q)
  have hBe : Integrable (fun ω => |B ω - b| / (b + a * q)) P := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hB.sub (integrable_const b)).norm.div_const (b + a * q)
  have hVe : Integrable (fun ω => |V ω - q| / q) P := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hV.sub (integrable_const q)).norm.div_const q
  have hbnd : ∀ᵐ ω ∂P.restrict G,
      |R ω - (b + a * q)| / (b + a * q) ≤
        |B ω - b| / (b + a * q) + |V ω - q| / q := by
    apply ae_restrict_of_ae
    filter_upwards [hident] with ω hω
    rw [hω]
    exact good_risk_relative_error_le_bias_variance (B ω) (V ω) b a q hb ha hq
  have hm := integral_mono_ae hRe.restrict (hBe.add hVe).restrict hbnd
  have he := integral_add (μ := P.restrict G) hBe.restrict hVe.restrict
  dsimp only [Pi.add_apply] at he hm
  exact hm.trans_eq he

/-- Bias and variance good-event comparisons imply the true conditional-risk
good-event L¹ comparison along any filter. Only `q` is eventually positive;
the noise factor is positive and the population bias nonnegative. All actual
energy integrability comes from risk, bias and their genuine a.e. identity. -/
theorem good_risk_relative_L1_of_bias_variance [IsFiniteMeasure P]
    {I : Type*} {l : Filter I}
    (R B V : I → Ω → ℝ) (b a q : I → ℝ) (G : I → Set Ω)
    (hb : ∀ i, 0 ≤ b i) (ha : ∀ i, 0 < a i) (hq : ∀ᶠ i in l, 0 < q i)
    (hR : ∀ i, Integrable (R i) P) (hB : ∀ i, Integrable (B i) P)
    (hident : ∀ i, ∀ᵐ ω ∂P, R i ω = B i ω + a i * V i ω)
    (hbias : Tendsto (fun i => ∫ ω in G i, |B i ω - b i| / (b i + a i * q i) ∂P) l (𝓝 0))
    (hvariance : Tendsto (fun i => ∫ ω in G i, |V i ω - q i| / q i ∂P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω in G i,
      |R i ω - (b i + a i * q i)| / (b i + a i * q i) ∂P) l (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa only [zero_add] using hbias.add hvariance)
  · filter_upwards [hq] with i hqi
    exact integral_nonneg fun _ => div_nonneg (abs_nonneg _)
      (add_nonneg (hb i) (mul_nonneg (ha i).le hqi.le))
  · filter_upwards [hq] with i hqi
    exact setIntegral_good_risk_relative_le_bias_variance (R i) (B i) (V i)
      (b i) (a i) (q i) (G i) (hb i) (ha i) hqi (hR i) (hB i) (hident i)

end
end KernelSeq
