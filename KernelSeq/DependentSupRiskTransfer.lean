import KernelSeq.UniformSupRiskTransfer

/-! Uniform relative error over a changing family of actual source balls. -/

namespace KernelSeq
open Filter Topology Set

abbrev dependentFamilyFilter {I : Type*} (l : Filter I) (Θ : I → Type*) :
    Filter (Σ i, Θ i) := l.comap Sigma.fst

theorem eventually_dependentFamilyFilter_iff {I : Type*} {l : Filter I}
    {Θ : I → Type*} {p : (Σ i, Θ i) → Prop} :
    (∀ᶠ z in dependentFamilyFilter l Θ, p z) ↔ ∀ᶠ i in l, ∀ θ : Θ i, p ⟨i,θ⟩ := by
  rw [Filter.eventually_comap]
  apply Filter.eventually_congr
  apply Filter.Eventually.of_forall
  intro i
  constructor
  · intro h θ
    exact h ⟨i,θ⟩ rfl
  · rintro h ⟨j,θ⟩ rfl
    exact h θ

theorem dependentFamilyFilter_neBot {I : Type*} {l : Filter I} [NeBot l]
    {Θ : I → Type*} (hΘ : ∀ i, Nonempty (Θ i)) : NeBot (dependentFamilyFilter l Θ) := by
  apply Filter.comap_neBot
  intro t ht
  obtain ⟨i,hi⟩ := Filter.nonempty_of_mem ht
  obtain ⟨θ⟩ := hΘ i
  exact ⟨⟨i,θ⟩,hi⟩

theorem dependent_sup_risk_ratio_tendsto {I : Type*} {Θ : I → Type*} {l : Filter I}
    (R B : ∀ i, Θ i → ℝ) (S : I → ℝ)
    (hB : ∀ᶠ i in l, ∀ θ, 0 < B i θ)
    (hupper : ∀ᶠ i in l, ∀ θ, B i θ ≤ S i)
    (hattained : ∀ᶠ i in l, ∃ θ, B i θ = S i)
    (hratio : Tendsto (fun p : Σ i, Θ i => R p.1 p.2 / B p.1 p.2)
      (dependentFamilyFilter l Θ) (𝓝 1)) :
    (∀ᶠ i in l, BddAbove (Set.range (R i))) ∧
      Tendsto (fun i => sSup (Set.range (R i)) / S i) l (𝓝 1) := by
  have herr (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in l, ∀ θ, |R i θ / B i θ - 1| < ε := by
    exact eventually_dependentFamilyFilter_iff.mp
      (show ∀ᶠ p in dependentFamilyFilter l Θ, |R p.1 p.2 / B p.1 p.2 - 1| < ε from
        by simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hratio ε hε)
  have hbdd : ∀ᶠ i in l, BddAbove (Set.range (R i)) := by
    filter_upwards [hB,hupper,hattained,herr 1 (by norm_num)] with i hi hu ha he
    exact (sup_risk_relative_error_of_benchmark_attained (R i) (B i) (S i) 1
      (by norm_num) hi hu ha (fun θ => (he θ).le)).1
  refine ⟨hbdd,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  filter_upwards [hB,hupper,hattained,herr (ε/2) (by linarith)] with i hi hu ha he
  have h := (sup_risk_relative_error_of_benchmark_attained (R i) (B i) (S i) (ε/2)
    (by linarith) hi hu ha (fun θ => (he θ).le)).2
  exact (show dist (sSup (Set.range (R i)) / S i) 1 ≤ ε/2 by
    simpa only [Real.dist_eq] using h).trans_lt (by linarith)

theorem dependent_sup_risk_eventual_upper {I : Type*} {Θ : I → Type*} {l : Filter I}
    (R B : ∀ i, Θ i → ℝ) (S : I → ℝ) (hΘ : ∀ i, Nonempty (Θ i))
    (hB : ∀ᶠ i in l, ∀ θ, 0 < B i θ)
    (hupper : ∀ᶠ i in l, ∀ θ, B i θ ≤ S i)
    (hratio : Tendsto (fun p : Σ i, Θ i => R p.1 p.2 / B p.1 p.2)
      (dependentFamilyFilter l Θ) (𝓝 1)) :
    ∀ᶠ i in l, BddAbove (Set.range (R i)) ∧ sSup (Set.range (R i)) ≤ 2*S i := by
  have he : ∀ᶠ i in l, ∀ θ, |R i θ / B i θ-1| < 1 := by
    exact eventually_dependentFamilyFilter_iff.mp
      (show ∀ᶠ p in dependentFamilyFilter l Θ, |R p.1 p.2 / B p.1 p.2 - 1| < 1 from
        by simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hratio 1 zero_lt_one)
  filter_upwards [hB,hupper,he] with i hi hu he
  have hb (θ : Θ i) : R i θ ≤ 2*S i := by
    have h := (abs_lt.mp (he θ)).2
    have hr : R i θ / B i θ ≤ 2 := by linarith
    exact ((div_le_iff₀ (hi θ)).mp hr).trans
      (mul_le_mul_of_nonneg_left (hu θ) (by norm_num))
  have hbound : 2*S i ∈ upperBounds (Set.range (R i)) := by
    rintro _ ⟨θ,rfl⟩
    exact hb θ
  obtain ⟨θ⟩ := hΘ i
  exact ⟨⟨_,hbound⟩, csSup_le ⟨_,Set.mem_range_self θ⟩ hbound⟩

end KernelSeq
