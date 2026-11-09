import KernelSeq.ProbabilityCalculus
import KernelSeq.VarianceTransfer
import Mathlib.Tactic.FieldSimp

/-!
# The probabilistic consequence of quantitative variance comparison

Variance transfer in probability follows from the trace and square-root
comparison bounds. The upstream operator
identities and concentration estimates are not asserted here. All probability
reductions use arbitrary index filters and outer measures.
-/

open Filter MeasureTheory Topology

namespace KernelSeq

/-- Polynomial envelope for the variance comparison after normalization by Q.
Here z = d / sqrt Q and t = δ N / Q. -/
noncomputable def varianceRelativeBound (δ z t E : ℝ) : ℝ :=
  2 * z + z ^ 2 + (2 * (1 + E ^ 2)) * (δ + 2 * (δ * z) + δ * z ^ 2 + t)

/-- Normalize the quantitative trace comparison by the positive population
variance scale; no positivity assumption on the empirical scalar a is needed. -/
theorem normalized_quantitative_variance_comparison {a W Q N E δ d : ℝ}
    (hW : 0 ≤ W) (hQ : 0 < Q) (hN : 0 ≤ N) (hd : 0 ≤ d)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4)
    (htrace : |a - W| ≤ δ * (a + E ^ 2 * N))
    (hsqrt : |Real.sqrt W - Real.sqrt Q| ≤ d) :
    |a - Q| / Q ≤ varianceRelativeBound δ (d / Real.sqrt Q) (δ * N / Q) E := by
  have hbound := quantitative_variance_comparison hW hQ.le hN hd hδ hδsmall
    htrace hsqrt
  calc
    |a - Q| / Q ≤ (d * (2 * Real.sqrt Q + d) +
        (2 * (1 + E ^ 2)) * δ * ((Real.sqrt Q + d) ^ 2 + N)) / Q :=
      div_le_div_of_nonneg_right hbound hQ.le
    _ = varianceRelativeBound δ (d / Real.sqrt Q) (δ * N / Q) E := by
      set s := Real.sqrt Q
      have hs : 0 < s := Real.sqrt_pos.mpr hQ
      have hsq : s ^ 2 = Q := Real.sq_sqrt hQ.le
      change (d * (2 * s + d) + (2 * (1 + E ^ 2)) * δ * ((s + d) ^ 2 + N)) / Q =
        2 * (d / s) + (d / s) ^ 2 +
          (2 * (1 + E ^ 2)) * (δ + 2 * (δ * (d / s)) + δ * (d / s) ^ 2 + δ * N / Q)
      rw [← hsq]
      field_simp
      ring

/-- All terms in the normalized polynomial envelope vanish in measure. -/
theorem varianceRelativeBound_tendstoInMeasure_zero
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {μ : Measure Ω}
    (δ z t : ι → Ω → ℝ) (E : ℝ)
    (hδ : TendstoInMeasure μ δ l (fun _ => 0))
    (hz : TendstoInMeasure μ z l (fun _ => 0))
    (ht : TendstoInMeasure μ t l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => varianceRelativeBound (δ i ω) (z i ω) (t i ω) E)
      l (fun _ => 0) := by
  have hzsq := tendstoInMeasure_sq_zero hz
  have hδz := tendstoInMeasure_mul_zero hδ hz
  have hδzsq := tendstoInMeasure_mul_zero hδ hzsq
  exact tendstoInMeasure_add_zero
    (tendstoInMeasure_add_zero (tendstoInMeasure_const_mul_zero hz 2) hzsq)
    (tendstoInMeasure_const_mul_zero
      (tendstoInMeasure_add_zero
        (tendstoInMeasure_add_zero
          (tendstoInMeasure_add_zero hδ (tendstoInMeasure_const_mul_zero hδz 2)) hδzsq)
        ht) (2 * (1 + E ^ 2)))

/-- Almost-everywhere domination on good events suffices. This variant is
needed because operator identities are generally statements almost surely. -/
theorem tendstoInMeasure_zero_of_good_events_ae
    {ι Ω F : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup F]
    {l : Filter ι} (μ : Measure Ω) (f : ι → Ω → F) (g : ι → Ω → ℝ)
    (G : ι → Set Ω)
    (hbad : Tendsto (fun i => μ (G i)ᶜ) l (𝓝 0))
    (hg : TendstoInMeasure μ g l (fun _ => 0))
    (hdom : ∀ᶠ i in l, ∀ᵐ ω ∂μ, ω ∈ G i → ‖f i ω‖ ≤ g i ω) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_zero]
  have hgε : Tendsto (fun i => μ {ω | ε ≤ |g i ω|}) l (𝓝 0) := by
    simpa only [sub_zero, Real.norm_eq_abs] using
      (tendstoInMeasure_iff_norm.mp hg) ε hε
  have hsum : Tendsto (fun i => μ (G i)ᶜ + μ {ω | ε ≤ |g i ω|}) l (𝓝 0) := by
    simpa only [zero_add] using hbad.add hgε
  have hbound : ∀ᶠ i in l,
      μ {ω | ε ≤ ‖f i ω‖} ≤ μ (G i)ᶜ + μ {ω | ε ≤ |g i ω|} := by
    filter_upwards [hdom] with i hi
    calc
      μ {ω | ε ≤ ‖f i ω‖} ≤ μ ((G i)ᶜ ∪ {ω | ε ≤ |g i ω|}) := by
        apply measure_mono_ae
        filter_upwards [hi] with ω hω
        intro htail
        by_cases hmem : ω ∈ G i
        · exact Or.inr ((htail.trans (hω hmem)).trans (le_abs_self _))
        · exact Or.inl hmem
      _ ≤ μ (G i)ᶜ + μ {ω | ε ≤ |g i ω|} := measure_union_le _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum (Eventually.of_forall (fun _ => zero_le)) hbound

/-- The asymptotic consequence of the manuscript's quantitative variance
comparison, with all scalar hypotheses explicit. Finite-moment or measurable
sample hypotheses enter only when proving the upstream estimates. -/
theorem probabilistic_variance_transfer_on_good_events
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι}
    (μ : Measure Ω) (a W N δ d : ι → Ω → ℝ) (Q : ι → ℝ) (E : ℝ)
    (G : ι → Set Ω)
    (hQ : ∀ᶠ i in l, 0 < Q i)
    (hbad : Tendsto (fun i => μ (G i)ᶜ) l (𝓝 0))
    (hcoeff : ∀ᶠ i in l, ∀ᵐ ω ∂μ, ω ∈ G i →
      0 ≤ W i ω ∧ 0 ≤ N i ω ∧ 0 ≤ d i ω ∧ 0 ≤ δ i ω ∧ δ i ω ≤ 1 / 4)
    (htrace : ∀ᶠ i in l, ∀ᵐ ω ∂μ, ω ∈ G i →
      |a i ω - W i ω| ≤ δ i ω * (a i ω + E ^ 2 * N i ω))
    (hsqrt : ∀ᶠ i in l, ∀ᵐ ω ∂μ, ω ∈ G i →
      |Real.sqrt (W i ω) - Real.sqrt (Q i)| ≤ d i ω)
    (hδ : TendstoInMeasure μ δ l (fun _ => 0))
    (hd : TendstoInMeasure μ (fun i ω => d i ω ^ 2 / Q i) l (fun _ => 0))
    (hN : TendstoInMeasure μ (fun i ω => δ i ω * N i ω / Q i) l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => |a i ω - Q i| / Q i) l (fun _ => 0) := by
  let z : ι → Ω → ℝ := fun i ω => Real.sqrt (d i ω ^ 2 / Q i)
  have hz : TendstoInMeasure μ z l (fun _ => 0) := tendstoInMeasure_sqrt_zero hd
  refine tendstoInMeasure_zero_of_good_events_ae μ _
    (fun i ω => varianceRelativeBound (δ i ω) (z i ω) (δ i ω * N i ω / Q i) E)
    G hbad (varianceRelativeBound_tendstoInMeasure_zero δ z _ E hδ hz hN) ?_
  filter_upwards [hQ, hcoeff, htrace, hsqrt] with i hQi hci hti hsi
  filter_upwards [hci, hti, hsi] with ω hc ht hs
  intro hω
  obtain ⟨hW, hN', hd', hδ', hδsmall⟩ := hc hω
  have hzval : z i ω = d i ω / Real.sqrt (Q i) := by
    dsimp [z]
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hd']
  have hnonneg : 0 ≤ |a i ω - Q i| / Q i := div_nonneg (abs_nonneg _) hQi.le
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hzval]
  exact normalized_quantitative_variance_comparison hW hQi hN' hd' hδ' hδsmall
    (ht hω) (hs hω)

end KernelSeq
