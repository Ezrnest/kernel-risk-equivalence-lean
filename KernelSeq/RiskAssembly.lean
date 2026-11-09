import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Assembly of bias and variance comparisons

Conditional risk equivalence from relative bias and variance comparisons.
The hypotheses below are comparison estimates, not a formalization of the
RKHS model or proofs that its bias and variance satisfy those estimates.
-/

open Filter MeasureTheory
open scoped Topology

namespace KernelSeq

/-- Relative bias and relative variance errors control the total risk ratio.
No positive lower bound on the population bias is needed. -/
theorem risk_ratio_error_le (Bh Vh B V : ℝ) (hB : 0 ≤ B) (hV : 0 < V) :
    |(Bh + Vh) / (B + V) - 1| ≤ |Bh - B| / (B + V) + |Vh - V| / V := by
  have hden : 0 < B + V := add_pos_of_nonneg_of_pos hB hV
  have heq : (Bh + Vh) / (B + V) - 1 = ((Bh - B) + (Vh - V)) / (B + V) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hden]
  calc
    |(Bh - B) + (Vh - V)| / (B + V) ≤ (|Bh - B| + |Vh - V|) / (B + V) :=
      div_le_div_of_nonneg_right (abs_add_le _ _) hden.le
    _ = |Bh - B| / (B + V) + |Vh - V| / (B + V) := add_div _ _ _
    _ ≤ |Bh - B| / (B + V) + |Vh - V| / V :=
      add_le_add le_rfl
        (div_le_div_of_nonneg_left (abs_nonneg _) hV (le_add_of_nonneg_left hB))

/-- Deterministic filter-limit form of the final risk assembly step.
Both denominators may tend to zero. -/
theorem risk_ratio_tendsto_one {ι : Type*} {l : Filter ι}
    (Bh Vh B V : ι → ℝ)
    (hB : ∀ᶠ i in l, 0 ≤ B i) (hV : ∀ᶠ i in l, 0 < V i)
    (hbias : Tendsto (fun i => |Bh i - B i| / (B i + V i)) l (𝓝 0))
    (hvariance : Tendsto (fun i => |Vh i - V i| / V i) l (𝓝 0)) :
    Tendsto (fun i => (Bh i + Vh i) / (B i + V i)) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [hB, hV] with i hiB hiV
    simpa only [Real.norm_eq_abs] using risk_ratio_error_le (Bh i) (Vh i) (B i) (V i) hiB hiV
  · simpa only [zero_add] using hbias.add hvariance

/-- Probabilistic form of risk assembly, for an arbitrary measure and index filter.
For a probability measure, `TendstoInMeasure` is convergence in probability.
The comparison assumptions are normalized absolute errors. -/
theorem risk_ratio_tendstoInMeasure_one {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {l : Filter ι} (Bh Vh : ι → Ω → ℝ) (B V : ι → ℝ)
    (hB : ∀ᶠ i in l, 0 ≤ B i) (hV : ∀ᶠ i in l, 0 < V i)
    (hbias : TendstoInMeasure P (fun i ω => |Bh i ω - B i| / (B i + V i)) l (fun _ => 0))
    (hvariance : TendstoInMeasure P (fun i ω => |Vh i ω - V i| / V i) l (fun _ => 0)) :
    TendstoInMeasure P (fun i ω => (Bh i ω + Vh i ω) / (B i + V i)) l (fun _ => 1) := by
  rw [tendstoInMeasure_iff_norm] at hbias hvariance ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hlim := (hbias (ε / 2) hhalf).add (hvariance (ε / 2) hhalf)
  simp only [add_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [hB, hV] with i hiB hiV
    calc
      P {ω | ε ≤ ‖(Bh i ω + Vh i ω) / (B i + V i) - 1‖} ≤
          P ({ω | ε / 2 ≤ ‖|Bh i ω - B i| / (B i + V i) - 0‖} ∪
            {ω | ε / 2 ≤ ‖|Vh i ω - V i| / V i - 0‖}) := by
        apply measure_mono
        intro ω hω
        by_contra hnot
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
        have hbnonneg : 0 ≤ |Bh i ω - B i| / (B i + V i) :=
          div_nonneg (abs_nonneg _) (add_pos_of_nonneg_of_pos hiB hiV).le
        have hvnonneg : 0 ≤ |Vh i ω - V i| / V i := div_nonneg (abs_nonneg _) hiV.le
        simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbnonneg,
          abs_of_nonneg hvnonneg] at hnot
        have hbound := risk_ratio_error_le (Bh i ω) (Vh i ω) (B i) (V i) hiB hiV
        simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hω
        linarith
      _ ≤ P {ω | ε / 2 ≤ ‖|Bh i ω - B i| / (B i + V i) - 0‖} +
          P {ω | ε / 2 ≤ ‖|Vh i ω - V i| / V i - 0‖} := measure_union_le _ _

end KernelSeq
