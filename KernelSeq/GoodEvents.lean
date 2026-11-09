import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Transfer from good events

This reduction applies to bias transfer and other conditional risk
comparisons when a deterministic inequality holds only on a design event
whose probability tends to one. All measures below are extended-valued outer
measures of sets, so no measurability assumptions on the events or functions
are required for this reduction. Establishing the upstream domination is a
separate task.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace KernelSeq

/-- Domination by an error tending to zero in measure on asymptotically full
measure events implies convergence to zero in measure. The index filter and
measure are arbitrary; in applications the measure is the design probability. -/
theorem tendstoInMeasure_zero_of_good_events
    {ι Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    {l : Filter ι} (μ : Measure Ω) (f : ι → Ω → E) (g : ι → Ω → ℝ)
    (G : ι → Set Ω)
    (hbad : Tendsto (fun i => μ (G i)ᶜ) l (𝓝 0))
    (hg : TendstoInMeasure μ g l (fun _ => 0))
    (hdom : ∀ᶠ i in l, ∀ ω ∈ G i, ‖f i ω‖ ≤ g i ω) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_zero]
  have hgε : Tendsto (fun i => μ {ω | ε ≤ |g i ω|}) l (𝓝 0) := by
    simpa only [sub_zero, Real.norm_eq_abs] using
      (tendstoInMeasure_iff_norm.mp hg) ε hε
  have hsum : Tendsto
      (fun i => μ (G i)ᶜ + μ {ω | ε ≤ |g i ω|}) l (𝓝 0) := by
    simpa only [zero_add] using hbad.add hgε
  have hbound : ∀ᶠ i in l,
      μ {ω | ε ≤ ‖f i ω‖} ≤ μ (G i)ᶜ + μ {ω | ε ≤ |g i ω|} := by
    filter_upwards [hdom] with i hi
    calc
      μ {ω | ε ≤ ‖f i ω‖} ≤ μ ((G i)ᶜ ∪ {ω | ε ≤ |g i ω|}) := by
        apply measure_mono
        intro ω hω
        by_cases hmem : ω ∈ G i
        · exact Or.inr ((hω.trans (hi ω hmem)).trans (le_abs_self _))
        · exact Or.inl hmem
      _ ≤ μ (G i)ᶜ + μ {ω | ε ≤ |g i ω|} := measure_union_le _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum (Eventually.of_forall (fun _ => zero_le)) hbound

/-- Global eventual domination is the special case with the full good event. -/
theorem tendstoInMeasure_zero_of_eventually_norm_le
    {ι Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    {l : Filter ι} (μ : Measure Ω) (f : ι → Ω → E) (g : ι → Ω → ℝ)
    (hg : TendstoInMeasure μ g l (fun _ => 0))
    (hdom : ∀ᶠ i in l, ∀ ω, ‖f i ω‖ ≤ g i ω) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_good_events μ f g (fun _ => Set.univ) ?_ hg ?_
  · simpa only [Set.compl_univ, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ≥0∞)) l (𝓝 0))
  · filter_upwards [hdom] with i hi ω _
    exact hi ω

end KernelSeq
