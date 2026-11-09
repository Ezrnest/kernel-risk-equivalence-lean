import KernelSeq.TriangularRiskConvergence

/-!
# Original uniform risk equivalence, including changing-model arrays

The uniform filter has one common row threshold for every family member.
Each member may have its own actual kernel, design law, target and spaces.
The assumptions are the original common constants, a positive noise floor,
uniform eventual variance positivity and uniformly vanishing original scales.

Uniform probability convergence means the supremum of the separate tail
probabilities. It does not require a simultaneous supremum event or any
measurability, countability or compactness of the parameter family.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

universe uH uX uΩ
variable {I Θ : Type*} {l : Filter I} [NeBot l] [Nonempty Θ] {κ ρ A s0 : ℝ}

instance uniformFamilyFilter_neBot : NeBot (uniformFamilyFilter l Θ) := by
  unfold uniformFamilyFilter
  infer_instance

/-- Original uniform conditional-risk equivalence, with no additional
expectation/logarithmic scale. Fixed-kernel target families and varying-model
families are both specializations of the actual row family below. -/
theorem uniform_conditional_risk_equivalence
    (m : I → Θ → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, ∀ θ, s0 ≤ (m i θ).σ)
    (hQ : ∀ᶠ i in l, ∀ θ, 0 < (m i θ).Q)
    (hc : Tendsto (fun p : I × Θ => (m p.1 p.2).compatibility)
      (uniformFamilyFilter l Θ) (𝓝 0))
    (hz : Tendsto (fun p : I × Θ => (m p.1 p.2).sourceBalance)
      (uniformFamilyFilter l Θ) (𝓝 0)) :
    UniformRiskInProbability (fun i θ => (m i θ).P)
      (fun i θ ω => (m i θ).conditionalRisk ω / (m i θ).benchmark - 1) l := by
  apply (uniformRiskInProbability_iff_product (fun i θ => (m i θ).P)
    (fun i θ ω => (m i θ).conditionalRisk ω / (m i θ).benchmark - 1)).mpr
  exact triangular_conditional_risk_equivalence (fun p : I × Θ => m p.1 p.2) hs0
    (eventually_uniformFamilyFilter_iff.mpr hnoise)
    (eventually_uniformFamilyFilter_iff.mpr hQ) hc hz

/-- Original uniform expectation-risk equivalence with precisely the extra
logarithmic scale. The real supremum is justified by derived eventual bounds,
so even an infinite target family may be unbounded at early indices. -/
theorem uniform_expectation_risk_equivalence
    (m : I → Θ → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, ∀ θ, s0 ≤ (m i θ).σ)
    (hQ : ∀ᶠ i in l, ∀ θ, 0 < (m i θ).Q)
    (hc : Tendsto (fun p : I × Θ => (m p.1 p.2).compatibility)
      (uniformFamilyFilter l Θ) (𝓝 0))
    (hz : Tendsto (fun p : I × Θ => (m p.1 p.2).sourceBalance)
      (uniformFamilyFilter l Θ) (𝓝 0))
    (he : Tendsto (fun p : I × Θ => (m p.1 p.2).expectationScale)
      (uniformFamilyFilter l Θ) (𝓝 0)) :
    Tendsto (fun i => sSup (Set.range (fun θ =>
      |(m i θ).expectationRisk / (m i θ).benchmark - 1|))) l (𝓝 0) ∧
      Tendsto (fun p : I × Θ => (m p.1 p.2).expectationRisk / (m p.1 p.2).benchmark)
        (uniformFamilyFilter l Θ) (𝓝 1) ∧
      Tendsto (fun p : I × Θ => (m p.1 p.2).normalizedL1)
        (uniformFamilyFilter l Θ) (𝓝 0) := by
  have h := triangular_expectation_risk_equivalence (fun p : I × Θ => m p.1 p.2) hs0
    (eventually_uniformFamilyFilter_iff.mpr hnoise)
    (eventually_uniformFamilyFilter_iff.mpr hQ) hc hz he
  let e := fun i θ => |(m i θ).expectationRisk / (m i θ).benchmark - 1|
  have hAbs : Tendsto (fun p : I × Θ => e p.1 p.2) (uniformFamilyFilter l Θ) (𝓝 0) := by
    simpa only [e, Real.norm_eq_abs, sub_self, norm_zero] using (h.1.sub_const 1).norm
  have hOne := (tendsto_uniformFamilyFilter_real_zero_iff e).mp hAbs 1 (by norm_num)
  have hbdd : ∀ᶠ i in l, BddAbove (Set.range (e i)) := by
    filter_upwards [hOne] with i hi
    refine ⟨1, ?_⟩
    rintro _ ⟨θ, rfl⟩
    exact (le_abs_self _).trans (hi θ).le
  have hNonneg : ∀ᶠ i in l, ∀ θ, 0 ≤ e i θ :=
    Eventually.of_forall fun _ _ => abs_nonneg _
  exact ⟨(uniform_tendsto_zero_iff_sSup e hNonneg hbdd).mp hAbs, h.1, h.2⟩

/-- Every deterministic choice of a target/model from the family may vary
with the row. This includes growing-dimensional kernel/distribution arrays. -/
theorem uniform_risk_equivalence_diagonal
    (m : I → Θ → TriangularRiskModel.{uH, uX, uΩ} κ ρ A) (θ : I → Θ)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, ∀ t, s0 ≤ (m i t).σ)
    (hQ : ∀ᶠ i in l, ∀ t, 0 < (m i t).Q)
    (hc : Tendsto (fun p : I × Θ => (m p.1 p.2).compatibility)
      (uniformFamilyFilter l Θ) (𝓝 0))
    (hz : Tendsto (fun p : I × Θ => (m p.1 p.2).sourceBalance)
      (uniformFamilyFilter l Θ) (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun i => (m i (θ i)).P
      {ω | ε < |(m i (θ i)).conditionalRisk ω / (m i (θ i)).benchmark - 1|}) l (𝓝 0) :=
  (uniform_conditional_risk_equivalence m hs0 hnoise hQ hc hz).diagonal θ

/-- The expectation conclusion also survives every changing-model diagonal,
using only the original uniformly vanishing third scale. -/
theorem uniform_expectation_risk_equivalence_diagonal
    (m : I → Θ → TriangularRiskModel.{uH, uX, uΩ} κ ρ A) (θ : I → Θ)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, ∀ t, s0 ≤ (m i t).σ)
    (hQ : ∀ᶠ i in l, ∀ t, 0 < (m i t).Q)
    (hc : Tendsto (fun p : I × Θ => (m p.1 p.2).compatibility)
      (uniformFamilyFilter l Θ) (𝓝 0))
    (hz : Tendsto (fun p : I × Θ => (m p.1 p.2).sourceBalance)
      (uniformFamilyFilter l Θ) (𝓝 0))
    (he : Tendsto (fun p : I × Θ => (m p.1 p.2).expectationScale)
      (uniformFamilyFilter l Θ) (𝓝 0)) :
    Tendsto (fun i => (m i (θ i)).expectationRisk / (m i (θ i)).benchmark) l (𝓝 1) ∧
      Tendsto (fun i => (m i (θ i)).normalizedL1) l (𝓝 0) := by
  have h := uniform_expectation_risk_equivalence m hs0 hnoise hQ hc hz he
  exact ⟨uniformFamilyFilter_tendsto_diagonal
      (f := fun i t => (m i t).expectationRisk / (m i t).benchmark) h.2.1 θ,
    uniformFamilyFilter_tendsto_diagonal (f := fun i t => (m i t).normalizedL1) h.2.2 θ⟩

end
end KernelSeq
