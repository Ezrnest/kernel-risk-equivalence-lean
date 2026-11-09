import KernelSeq.BiasTransfer
import KernelSeq.ProbabilityCalculus

/-!
# Bias transfer in probability

Probabilistic scalar and vector-error reductions for bias transfer. The upstream
operator-error decomposition and estimates are explicit premises; no RKHS
risk theorem is asserted here. Bias norms can vanish and need not be bounded.
-/

open Filter MeasureTheory Topology

namespace KernelSeq

/-- A variance-normalized squared error converging to zero in measure implies
that the corresponding nonnegative square-root ratio does too. -/
theorem normalized_error_tendstoInMeasure_zero
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {μ : Measure Ω}
    (c : ι → Ω → ℝ) (V : ι → ℝ)
    (hc : ∀ᶠ i in l, ∀ᵐ ω ∂μ, 0 ≤ c i ω)
    (hsmall : TendstoInMeasure μ (fun i ω => c i ω ^ 2 / V i) l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => c i ω / Real.sqrt (V i)) l (fun _ => 0) := by
  have hs := tendstoInMeasure_sqrt_zero hsmall
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hs
  filter_upwards [hc] with i hci
  filter_upwards [hci] with ω hω
  rw [Real.sqrt_div (sq_nonneg (c i ω)), Real.sqrt_sq hω]

/-- The complete relative-risk error envelope converges to zero in measure.
The variance scale is deterministic but may converge to zero arbitrarily fast. -/
theorem relativeRiskBound_tendstoInMeasure_zero
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {μ : Measure Ω}
    (u c : ι → Ω → ℝ) (V : ι → ℝ)
    (hc : ∀ᶠ i in l, ∀ᵐ ω ∂μ, 0 ≤ c i ω)
    (hu : TendstoInMeasure μ u l (fun _ => 0))
    (hsmall : TendstoInMeasure μ (fun i ω => c i ω ^ 2 / V i) l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => relativeRiskBound (u i ω) (c i ω) (V i))
      l (fun _ => 0) := by
  have hr := normalized_error_tendstoInMeasure_zero c V hc hsmall
  have hpoly := tendstoInMeasure_add_zero
    (tendstoInMeasure_add_zero
      (tendstoInMeasure_add_zero (tendstoInMeasure_const_mul_zero hu 2)
        (tendstoInMeasure_sq_zero hu))
      (tendstoInMeasure_add_zero hr (tendstoInMeasure_mul_zero hu hr))) hsmall
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hpoly
  exact Eventually.of_forall fun i => Eventually.of_forall fun ω => by
    dsimp
    unfold relativeRiskBound
    ring

/-- Bias transfer in measure on asymptotically full-measure design events.
The operator argument that supplies `he`, `hu`, and `hsmall` remains upstream. -/
theorem probabilistic_bias_transfer_on_good_events
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {l : Filter ι} (μ : Measure Ω) (r e : ι → Ω → E)
    (u c : ι → Ω → ℝ) (V : ι → ℝ) (G : ι → Set Ω)
    (hbad : Tendsto (fun i => μ (G i)ᶜ) l (𝓝 0))
    (hc_ae : ∀ᶠ i in l, ∀ᵐ ω ∂μ, 0 ≤ c i ω)
    (hcoeff : ∀ᶠ i in l, ∀ ω ∈ G i, 0 ≤ u i ω ∧ 0 ≤ c i ω)
    (hV : ∀ᶠ i in l, 0 < V i)
    (he : ∀ᶠ i in l, ∀ ω ∈ G i, ‖e i ω‖ ≤ u i ω * ‖r i ω‖ + c i ω)
    (hu : TendstoInMeasure μ u l (fun _ => 0))
    (hsmall : TendstoInMeasure μ (fun i ω => c i ω ^ 2 / V i) l (fun _ => 0)) :
    TendstoInMeasure μ
      (fun i ω => |‖r i ω - e i ω‖ ^ 2 - ‖r i ω‖ ^ 2| /
        (‖r i ω‖ ^ 2 + V i)) l (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_good_events μ _
    (fun i ω => relativeRiskBound (u i ω) (c i ω) (V i)) G hbad
    (relativeRiskBound_tendstoInMeasure_zero u c V hc_ae hu hsmall) ?_
  filter_upwards [hcoeff, hV, he] with i hci hVi hei ω hω
  have hnonneg : 0 ≤ |‖r i ω - e i ω‖ ^ 2 - ‖r i ω‖ ^ 2| /
      (‖r i ω‖ ^ 2 + V i) := div_nonneg (abs_nonneg _) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact bias_relative_risk_bound (r i ω) (e i ω) (u i ω) (c i ω) (V i)
    (hci ω hω).1 (hci ω hω).2 hVi (hei ω hω)

end KernelSeq
