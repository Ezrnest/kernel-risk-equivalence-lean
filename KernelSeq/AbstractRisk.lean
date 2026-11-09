import KernelSeq.BiasAsymptotics
import KernelSeq.GoodEvents
import KernelSeq.RiskAssembly
import KernelSeq.ProbabilisticBias

/-!
# Complete abstract risk-transfer chains

These corollaries connect the checked norm perturbation, asymptotic/good-event
reduction, and risk assembly modules. They are not the RKHS risk-equivalence
theorem: the actual estimator's operator estimates and conditional risk
decomposition must still be supplied by later modules.
-/

open Filter MeasureTheory Topology

namespace KernelSeq

/-- Deterministic risk equivalence from vector perturbation and variance control. -/
theorem abstract_risk_equivalence {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} (r e : ι → E) (u c V Vh : ι → ℝ)
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i)
    (hc_nonneg : ∀ᶠ i in l, 0 ≤ c i)
    (hV : ∀ᶠ i in l, 0 < V i)
    (he : ∀ᶠ i in l, ‖e i‖ ≤ u i * ‖r i‖ + c i)
    (hu : Tendsto u l (𝓝 0))
    (hsmall : Tendsto (fun i => c i ^ 2 / V i) l (𝓝 0))
    (hvariance : Tendsto (fun i => |Vh i - V i| / V i) l (𝓝 0)) :
    Tendsto (fun i => (‖r i - e i‖ ^ 2 + Vh i) / (‖r i‖ ^ 2 + V i)) l (𝓝 1) := by
  exact risk_ratio_tendsto_one _ _ _ _
    (Eventually.of_forall fun i => sq_nonneg ‖r i‖) hV
    (deterministic_bias_transfer r e u c V hu_nonneg hc_nonneg hV he hu hsmall)
    hvariance

/-- Bias comparison on good design events. The scalar error envelope must
converge in measure; deriving that from the random coefficient rates remains
an explicit upstream task. -/
theorem bias_tendstoInMeasure_of_good_events
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {l : Filter ι} (P : Measure Ω) (r : ι → E) (e : ι → Ω → E)
    (u c : ι → Ω → ℝ) (V : ι → ℝ) (G : ι → Set Ω)
    (hV : ∀ᶠ i in l, 0 < V i)
    (hbad : Tendsto (fun i => P (G i)ᶜ) l (𝓝 0))
    (hcoeff : ∀ᶠ i in l, ∀ ω ∈ G i,
      0 ≤ u i ω ∧ 0 ≤ c i ω ∧ ‖e i ω‖ ≤ u i ω * ‖r i‖ + c i ω)
    (henvelope : TendstoInMeasure P
      (fun i ω => relativeRiskBound (u i ω) (c i ω) (V i)) l (fun _ => 0)) :
    TendstoInMeasure P
      (fun i ω => |‖r i - e i ω‖ ^ 2 - ‖r i‖ ^ 2| / (‖r i‖ ^ 2 + V i))
      l (fun _ => 0) := by
  apply tendstoInMeasure_zero_of_good_events P _ _ G hbad henvelope
  filter_upwards [hV, hcoeff] with i hVi hi ω hω
  obtain ⟨hui, hci, hei⟩ := hi ω hω
  have hnonneg : 0 ≤ |‖r i - e i ω‖ ^ 2 - ‖r i‖ ^ 2| / (‖r i‖ ^ 2 + V i) :=
    div_nonneg (abs_nonneg _) (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
    bias_relative_risk_bound (r i) (e i ω) (u i ω) (c i ω) (V i) hui hci hVi hei

/-- Probabilistic risk equivalence from a good-event vector bound and a
vanishing scalar envelope. This retains the actual upstream hypotheses. -/
theorem abstract_risk_equivalence_inMeasure
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {l : Filter ι} (P : Measure Ω) (r : ι → E) (e : ι → Ω → E)
    (u c : ι → Ω → ℝ) (V : ι → ℝ) (Vh : ι → Ω → ℝ) (G : ι → Set Ω)
    (hV : ∀ᶠ i in l, 0 < V i)
    (hbad : Tendsto (fun i => P (G i)ᶜ) l (𝓝 0))
    (hcoeff : ∀ᶠ i in l, ∀ ω ∈ G i,
      0 ≤ u i ω ∧ 0 ≤ c i ω ∧ ‖e i ω‖ ≤ u i ω * ‖r i‖ + c i ω)
    (henvelope : TendstoInMeasure P
      (fun i ω => relativeRiskBound (u i ω) (c i ω) (V i)) l (fun _ => 0))
    (hvariance : TendstoInMeasure P
      (fun i ω => |Vh i ω - V i| / V i) l (fun _ => 0)) :
    TendstoInMeasure P
      (fun i ω => (‖r i - e i ω‖ ^ 2 + Vh i ω) / (‖r i‖ ^ 2 + V i))
      l (fun _ => 1) := by
  exact risk_ratio_tendstoInMeasure_one P _ _ _ _
    (Eventually.of_forall fun i => sq_nonneg ‖r i‖) hV
    (bias_tendstoInMeasure_of_good_events P r e u c V G hV hbad hcoeff henvelope)
    hvariance

/-- The abstract probabilistic chain from the original scalar coefficient rates,
rather than assuming convergence of the complete error envelope. -/
theorem abstract_risk_equivalence_of_rates
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {l : Filter ι} (P : Measure Ω) (r : ι → E) (e : ι → Ω → E)
    (u c : ι → Ω → ℝ) (V : ι → ℝ) (Vh : ι → Ω → ℝ) (G : ι → Set Ω)
    (hV : ∀ᶠ i in l, 0 < V i)
    (hbad : Tendsto (fun i => P (G i)ᶜ) l (𝓝 0))
    (hc_ae : ∀ᶠ i in l, ∀ᵐ ω ∂P, 0 ≤ c i ω)
    (hcoeff : ∀ᶠ i in l, ∀ ω ∈ G i, 0 ≤ u i ω ∧ 0 ≤ c i ω)
    (he : ∀ᶠ i in l, ∀ ω ∈ G i, ‖e i ω‖ ≤ u i ω * ‖r i‖ + c i ω)
    (hu : TendstoInMeasure P u l (fun _ => 0))
    (hsmall : TendstoInMeasure P (fun i ω => c i ω ^ 2 / V i) l (fun _ => 0))
    (hvariance : TendstoInMeasure P
      (fun i ω => |Vh i ω - V i| / V i) l (fun _ => 0)) :
    TendstoInMeasure P
      (fun i ω => (‖r i - e i ω‖ ^ 2 + Vh i ω) / (‖r i‖ ^ 2 + V i))
      l (fun _ => 1) := by
  exact risk_ratio_tendstoInMeasure_one P _ _ _ _
    (Eventually.of_forall fun i => sq_nonneg ‖r i‖) hV
    (probabilistic_bias_transfer_on_good_events P (fun i _ => r i) e u c V G
      hbad hc_ae hcoeff hV he hu hsmall) hvariance

end KernelSeq
