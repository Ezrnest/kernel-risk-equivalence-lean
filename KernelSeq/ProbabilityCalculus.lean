import KernelSeq.GoodEvents
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Probability limit calculus at deterministic constants

The elementary continuous mapping and arithmetic reductions used to propagate
risk-error bounds. All index filters and measures are arbitrary. The proofs
use outer-measure tail inclusions, so no measurability or countable-generation
hypotheses are added.
-/

open Filter MeasureTheory Topology

namespace KernelSeq

/-- A map continuous at a constant preserves convergence in measure to that
constant. Uniform continuity away from the limit is not needed. -/
theorem tendstoInMeasure_continuousAt_const
    {ι Ω E F : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] [PseudoMetricSpace F]
    {l : Filter ι} {μ : Measure Ω} {f : ι → Ω → E} {a : E}
    (hf : TendstoInMeasure μ f l (fun _ => a))
    (φ : E → F) (hφ : ContinuousAt φ a) :
    TendstoInMeasure μ (fun i ω => φ (f i ω)) l (fun _ => φ a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.continuousAt_iff.mp hφ ε hε
  have htail := (tendstoInMeasure_iff_dist.mp hf) δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds htail (fun _ => zero_le)
  intro i
  apply measure_mono
  intro ω hω
  by_contra hnot
  exact (not_lt_of_ge hω) (hcontrol (lt_of_not_ge hnot))

/-- Pairing functions that converge in measure to constants. -/
theorem tendstoInMeasure_pair_const
    {ι Ω E F : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] [PseudoMetricSpace F]
    {l : Filter ι} {μ : Measure Ω} {f : ι → Ω → E} {g : ι → Ω → F}
    {a : E} {b : F}
    (hf : TendstoInMeasure μ f l (fun _ => a))
    (hg : TendstoInMeasure μ g l (fun _ => b)) :
    TendstoInMeasure μ (fun i ω => (f i ω, g i ω)) l (fun _ => (a, b)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hsum : Tendsto
      (fun i => μ {ω | ε ≤ dist (f i ω) a} + μ {ω | ε ≤ dist (g i ω) b})
      l (𝓝 0) := by
    simpa only [zero_add] using
      ((tendstoInMeasure_iff_dist.mp hf) ε hε).add
        ((tendstoInMeasure_iff_dist.mp hg) ε hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => zero_le)
  intro i
  calc
    μ {ω | ε ≤ dist (f i ω, g i ω) (a, b)} ≤
        μ ({ω | ε ≤ dist (f i ω) a} ∪ {ω | ε ≤ dist (g i ω) b}) := by
      apply measure_mono
      intro ω hω
      change ε ≤ dist (f i ω, g i ω) (a, b) at hω
      change ε ≤ dist (f i ω) a ∨ ε ≤ dist (g i ω) b
      exact le_max_iff.mp (by simpa only [Prod.dist_eq] using hω)
    _ ≤ μ {ω | ε ≤ dist (f i ω) a} + μ {ω | ε ≤ dist (g i ω) b} :=
      measure_union_le _ _

/-- Addition at zero in measure, with no measurability assumptions. -/
theorem tendstoInMeasure_add_zero
    {ι Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} {f g : ι → Ω → E}
    (hf : TendstoInMeasure μ f l (fun _ => 0))
    (hg : TendstoInMeasure μ g l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => f i ω + g i ω) l (fun _ => 0) := by
  have hcont : Continuous (fun p : E × E => p.1 + p.2) :=
    continuous_fst.add continuous_snd
  have hp : TendstoInMeasure μ (fun i ω => (f i ω, g i ω)) l
      (fun _ => ((0 : E), (0 : E))) :=
    tendstoInMeasure_pair_const (a := (0 : E)) (b := (0 : E)) hf hg
  simpa only [zero_add] using
    tendstoInMeasure_continuousAt_const hp
      (fun p : E × E => p.1 + p.2) hcont.continuousAt

/-- Multiplication of two real errors converging to zero in measure. -/
theorem tendstoInMeasure_mul_zero
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {μ : Measure Ω}
    {f g : ι → Ω → ℝ}
    (hf : TendstoInMeasure μ f l (fun _ => 0))
    (hg : TendstoInMeasure μ g l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => f i ω * g i ω) l (fun _ => 0) := by
  have hcont : Continuous (fun p : ℝ × ℝ => p.1 * p.2) :=
    continuous_fst.mul continuous_snd
  have hp : TendstoInMeasure μ (fun i ω => (f i ω, g i ω)) l
      (fun _ => ((0 : ℝ), (0 : ℝ))) :=
    tendstoInMeasure_pair_const (a := (0 : ℝ)) (b := (0 : ℝ)) hf hg
  simpa only [zero_mul] using
    tendstoInMeasure_continuousAt_const hp
      (fun p : ℝ × ℝ => p.1 * p.2) hcont.continuousAt

/-- Multiplication by a fixed real constant. -/
theorem tendstoInMeasure_const_mul_zero
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {μ : Measure Ω}
    {f : ι → Ω → ℝ} (hf : TendstoInMeasure μ f l (fun _ => 0)) (c : ℝ) :
    TendstoInMeasure μ (fun i ω => c * f i ω) l (fun _ => 0) := by
  simpa only [mul_zero] using
    tendstoInMeasure_continuousAt_const hf (fun x : ℝ => c * x)
      (continuous_const.mul continuous_id).continuousAt

/-- Squaring a real error converging to zero in measure. -/
theorem tendstoInMeasure_sq_zero
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {μ : Measure Ω}
    {f : ι → Ω → ℝ} (hf : TendstoInMeasure μ f l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => f i ω ^ 2) l (fun _ => 0) := by
  simpa only [sq] using tendstoInMeasure_mul_zero hf hf

/-- The real square root is continuous at zero, including from negative inputs. -/
theorem tendstoInMeasure_sqrt_zero
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {μ : Measure Ω}
    {f : ι → Ω → ℝ} (hf : TendstoInMeasure μ f l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => Real.sqrt (f i ω)) l (fun _ => 0) := by
  simpa only [Real.sqrt_zero] using
    tendstoInMeasure_continuousAt_const hf Real.sqrt Real.continuous_sqrt.continuousAt

end KernelSeq
