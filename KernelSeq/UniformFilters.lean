import Mathlib.Order.Filter.Prod
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Uniform families and arbitrary diagonals

The product `l ×ˢ ⊤` means that every parameter is controlled after one
common index threshold. It does not permit a parameter-dependent threshold.
Real supremum statements explicitly retain eventual boundedness, so an
early unbounded family and Lean's real `sSup` convention cause no ambiguity.
The complete-lattice ENNReal supremum requires no such convention.
-/

open Filter Topology
open scoped ENNReal

namespace KernelSeq

variable {I Θ : Type*} {l : Filter I}

/-- The uniform parameter filter: eventually in the row, for every parameter. -/
def uniformFamilyFilter (l : Filter I) (Θ : Type*) : Filter (I × Θ) := l ×ˢ ⊤

theorem eventually_uniformFamilyFilter_iff {p : I → Θ → Prop} :
    (∀ᶠ z in uniformFamilyFilter l Θ, p z.1 z.2) ↔ ∀ᶠ i in l, ∀ θ, p i θ := by
  exact Filter.mem_prod_top

/-- Exact epsilon-uniform convergence, for an arbitrary parameter type. -/
theorem tendsto_uniformFamilyFilter_iff {E : Type*} [PseudoMetricSpace E]
    (f : I → Θ → E) (z : E) :
    Tendsto (fun p => f p.1 p.2) (uniformFamilyFilter l Θ) (𝓝 z) ↔
      ∀ ε > 0, ∀ᶠ i in l, ∀ θ, dist (f i θ) z < ε := by
  constructor
  · intro h ε hε
    exact (eventually_uniformFamilyFilter_iff
      (p := fun i θ => dist (f i θ) z < ε)).mp (Metric.tendsto_nhds.mp h ε hε)
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    exact (eventually_uniformFamilyFilter_iff
      (p := fun i θ => dist (f i θ) z < ε)).mpr (h ε hε)

theorem tendsto_uniformFamilyFilter_real_zero_iff (a : I → Θ → ℝ) :
    Tendsto (fun p => a p.1 p.2) (uniformFamilyFilter l Θ) (𝓝 0) ↔
      ∀ ε > 0, ∀ᶠ i in l, ∀ θ, |a i θ| < ε := by
  simpa only [Real.dist_eq, sub_zero] using tendsto_uniformFamilyFilter_iff a 0

/-- For natural-number rows this is exactly one threshold for all parameters. -/
theorem tendsto_uniformFamilyFilter_nat_iff {E : Type*} [PseudoMetricSpace E]
    (f : ℕ → Θ → E) (z : E) :
    Tendsto (fun p => f p.1 p.2) (uniformFamilyFilter atTop Θ) (𝓝 z) ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ θ, dist (f n θ) z < ε := by
  simp only [tendsto_uniformFamilyFilter_iff, eventually_atTop]

/-- A common eventual statement is equivalent to its validity on every
parameter selection. Choice selects a violating parameter at each bad
row; no countability or compactness of the family is needed. -/
theorem eventually_forall_iff_diagonal [Nonempty Θ] (p : I → Θ → Prop) :
    (∀ᶠ i in l, ∀ θ, p i θ) ↔ ∀ θ : I → Θ, ∀ᶠ i in l, p i (θ i) := by
  constructor
  · intro h θ
    exact h.mono fun i hi => hi (θ i)
  · intro h
    classical
    let θ : I → Θ := fun i => if hi : ∃ θ, ¬ p i θ then Classical.choose hi
      else Classical.arbitrary Θ
    filter_upwards [h θ] with i hi θ'
    by_contra hnot
    have hex : ∃ θ, ¬ p i θ := ⟨θ', hnot⟩
    have hbad : ¬ p i (θ i) := by
      dsimp only [θ]
      rw [dif_pos hex]
      exact Classical.choose_spec hex
    exact hbad hi

/-- Any parameter sequence is an admissible diagonal of a uniform family. -/
theorem tendsto_diagonal_uniformFamilyFilter (θ : I → Θ) :
    Tendsto (fun i => (i, θ i)) l (uniformFamilyFilter l Θ) :=
  tendsto_id.prodMk tendsto_top

theorem uniformFamilyFilter_tendsto_diagonal {E : Type*} [TopologicalSpace E]
    {f : I → Θ → E} {z : E}
    (hf : Tendsto (fun p => f p.1 p.2) (uniformFamilyFilter l Θ) (𝓝 z)) (θ : I → Θ) :
    Tendsto (fun i => f i (θ i)) l (𝓝 z) :=
  hf.comp (tendsto_diagonal_uniformFamilyFilter θ)

/-- True uniform convergence is equivalent to convergence along every
parameter diagonal, even when the parameter set is infinite. -/
theorem uniformFamilyFilter_tendsto_iff_diagonal [Nonempty Θ]
    {E : Type*} [PseudoMetricSpace E] (f : I → Θ → E) (z : E) :
    Tendsto (fun p => f p.1 p.2) (uniformFamilyFilter l Θ) (𝓝 z) ↔
      ∀ θ : I → Θ, Tendsto (fun i => f i (θ i)) l (𝓝 z) := by
  constructor
  · intro h θ
    exact uniformFamilyFilter_tendsto_diagonal h θ
  · intro h
    apply (tendsto_uniformFamilyFilter_iff f z).mpr
    intro ε hε
    apply (eventually_forall_iff_diagonal (fun i θ => dist (f i θ) z < ε)).mpr
    intro θ
    exact Metric.tendsto_nhds.mp (h θ) ε hε

/-- A common finite scalar bound tending to zero supplies true uniform
convergence, rather than taking uniform convergence as a premise. -/
theorem uniform_tendsto_zero_of_bound (a : I → Θ → ℝ) (h : I → ℝ)
    (ha : ∀ᶠ i in l, ∀ θ, 0 ≤ a i θ)
    (hbound : ∀ᶠ i in l, ∀ θ, a i θ ≤ h i) (hh : Tendsto h l (𝓝 0)) :
    Tendsto (fun p => a p.1 p.2) (uniformFamilyFilter l Θ) (𝓝 0) := by
  apply (tendsto_uniformFamilyFilter_real_zero_iff a).mpr
  intro ε hε
  filter_upwards [ha, hbound, hh.eventually (gt_mem_nhds hε)] with i hia hib hih θ
  rw [abs_of_nonneg (hia θ)]
  exact (hib θ).trans_lt hih

/-- The real supremum and epsilon-uniform formulations agree when the
family is eventually bounded above and nonnegative. No early-row bound
and no finite parameter set are required. -/
theorem uniform_tendsto_zero_iff_sSup [Nonempty Θ] (a : I → Θ → ℝ)
    (ha : ∀ᶠ i in l, ∀ θ, 0 ≤ a i θ)
    (hbdd : ∀ᶠ i in l, BddAbove (Set.range (a i))) :
    Tendsto (fun p => a p.1 p.2) (uniformFamilyFilter l Θ) (𝓝 0) ↔
      Tendsto (fun i => sSup (Set.range (a i))) l (𝓝 0) := by
  constructor
  · intro hf
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he := (tendsto_uniformFamilyFilter_real_zero_iff a).mp hf (ε / 2) (by linarith)
    filter_upwards [ha, hbdd, he] with i hia hib hie
    have h0 : 0 ≤ sSup (Set.range (a i)) := (hia (Classical.arbitrary Θ)).trans
      (le_csSup hib (Set.mem_range_self _))
    have hle : sSup (Set.range (a i)) ≤ ε / 2 := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨θ, rfl⟩
      exact (le_abs_self _).trans (hie θ).le
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg h0] using hle.trans_lt (by linarith)
  · intro hs
    apply uniform_tendsto_zero_of_bound a _ ha _ hs
    filter_upwards [hbdd] with i hi θ
    exact le_csSup hi (Set.mem_range_self θ)

/-- A genuine common scalar bound itself proves the boundedness needed for
the real supremum and gives its vanishing limit. -/
theorem sSup_tendsto_zero_of_uniform_bound [Nonempty Θ] (a : I → Θ → ℝ) (h : I → ℝ)
    (ha : ∀ᶠ i in l, ∀ θ, 0 ≤ a i θ)
    (hbound : ∀ᶠ i in l, ∀ θ, a i θ ≤ h i) (hh : Tendsto h l (𝓝 0)) :
    Tendsto (fun i => sSup (Set.range (a i))) l (𝓝 0) := by
  have hbdd : ∀ᶠ i in l, BddAbove (Set.range (a i)) := by
    filter_upwards [hbound] with i hi
    exact ⟨h i, by rintro _ ⟨θ, rfl⟩; exact hi θ⟩
  exact (uniform_tendsto_zero_iff_sSup a ha hbdd).mp
    (uniform_tendsto_zero_of_bound a h ha hbound hh)

/-- Probability suprema are complete-lattice suprema. Their equivalence
with epsilon-uniform control needs neither boundedness nor nonemptiness. -/
theorem uniform_ennreal_tendsto_zero_iff_iSup (q : I → Θ → ℝ≥0∞) :
    Tendsto (fun p => q p.1 p.2) (uniformFamilyFilter l Θ) (𝓝 0) ↔
      Tendsto (fun i => ⨆ θ, q i θ) l (𝓝 0) := by
  constructor
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    have he := (eventually_uniformFamilyFilter_iff (p := fun i θ => q i θ ≤ ε)).mp
      (ENNReal.tendsto_nhds_zero.mp h ε hε)
    exact he.mono fun _ hi => iSup_le hi
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    apply (eventually_uniformFamilyFilter_iff (p := fun i θ => q i θ ≤ ε)).mpr
    exact (ENNReal.tendsto_nhds_zero.mp h ε hε).mono fun _ hi θ => (le_iSup _ θ).trans hi

theorem iSup_ennreal_tendsto_zero_of_uniform_bound (q : I → Θ → ℝ≥0∞) (h : I → ℝ≥0∞)
    (hbound : ∀ᶠ i in l, ∀ θ, q i θ ≤ h i) (hh : Tendsto h l (𝓝 0)) :
    Tendsto (fun i => ⨆ θ, q i θ) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [hbound, ENNReal.tendsto_nhds_zero.mp hh ε hε] with i hi hih
  exact iSup_le fun θ => (hi θ).trans hih

end KernelSeq
