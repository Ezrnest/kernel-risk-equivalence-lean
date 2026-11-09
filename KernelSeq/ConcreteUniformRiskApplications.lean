import KernelSeq.ConcreteRiskApplications

/-!
# Uniform risk conclusions in the concrete spectrum examples

The parameter-family filter requires one common threshold for all targets.
The row model may change its kernel, spaces and laws at every index. Real
supremum boundedness is derived from the actual uniform limit internally.
-/

open MeasureTheory Filter Topology Asymptotics

namespace KernelSeq
noncomputable section

universe uH uX uΩ
variable {I Θ : Type*} {l : Filter I} [NeBot l] [Nonempty Θ] {κ ρ A s0 : ℝ}

def ConcreteUniformRiskEquivalence
    (m : I × Θ → TriangularRiskModel.{uH, uX, uΩ} κ ρ A) (l : Filter I) : Prop :=
  UniformRiskInProbability (fun i θ => (m (i, θ)).P)
    (fun i θ ω => (m (i, θ)).conditionalRisk ω / (m (i, θ)).benchmark - 1) l ∧
    Tendsto (fun i => sSup (Set.range (fun θ =>
      |(m (i, θ)).expectationRisk / (m (i, θ)).benchmark - 1|))) l (𝓝 0) ∧
    Tendsto (fun p => (m p).expectationRisk / (m p).benchmark) (uniformFamilyFilter l Θ) (𝓝 1) ∧
    Tendsto (fun p => (m p).normalizedL1) (uniformFamilyFilter l Θ) (𝓝 0)

omit [NeBot l] in
theorem concreteUniformRiskEquivalence_of_product_rows
    (m : I × Θ → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (h : ConcreteRowRiskEquivalence m (uniformFamilyFilter l Θ)) :
    ConcreteUniformRiskEquivalence m l := by
  have hprob : UniformRiskInProbability (fun i θ => (m (i, θ)).P)
      (fun i θ ω => (m (i, θ)).conditionalRisk ω / (m (i, θ)).benchmark - 1) l := by
    apply (uniformRiskInProbability_iff_product _ _).mpr
    exact h.1
  let e := fun i θ => |(m (i, θ)).expectationRisk / (m (i, θ)).benchmark - 1|
  have hAbs : Tendsto (fun p : I × Θ => e p.1 p.2) (uniformFamilyFilter l Θ) (𝓝 0) := by
    simpa only [e, Real.norm_eq_abs, sub_self, norm_zero] using (h.2.1.sub_const 1).norm
  have hOne := (tendsto_uniformFamilyFilter_real_zero_iff e).mp hAbs 1 (by norm_num)
  have hbdd : ∀ᶠ i in l, BddAbove (Set.range (e i)) := by
    filter_upwards [hOne] with i hi
    refine ⟨1, ?_⟩
    rintro _ ⟨θ, rfl⟩
    exact (le_abs_self _).trans (hi θ).le
  have hnonneg : ∀ᶠ i in l, ∀ θ, 0 ≤ e i θ :=
    Eventually.of_forall fun _ _ => abs_nonneg _
  exact ⟨hprob, (uniform_tendsto_zero_iff_sSup e hnonneg hbdd).mp hAbs, h.2.1, h.2.2⟩

theorem uniform_polynomial_sourceBall_risk_equivalence
    (m : I × Θ → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (e : ∀ i, (m i).scaleModel.SpectrumEnumeration) (J0 : ℕ)
    {β θ s R c C K : ℝ} (hβ : 1 < β) (hθ : 0 < θ) (hθβ : θ < β)
    (hs : 0 < s) (hR : 0 < R) (hc : 0 < c) (hC : 0 < C)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in uniformFamilyFilter l Θ, s0 ≤ (m i).σ)
    (hn : Tendsto (fun i => ((m i).n : ℝ)) (uniformFamilyFilter l Θ) atTop)
    (hreg : (fun i => (m i).lam) =Θ[uniformFamilyFilter l Θ] (fun i => ((m i).n : ℝ) ^ (-θ)))
    (hspectrum : ∀ᶠ i in uniformFamilyFilter l Θ, ∀ j : ℕ, J0 ≤ j →
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).scaleModel.eigenvalue (e i) j ∧
      (m i).scaleModel.eigenvalue (e i) j ≤ C * ((j : ℝ) + 1) ^ (-β))
    (hsource : ∀ᶠ i in uniformFamilyFilter l Θ, (m i).f ∈ (m i).scaleModel.SourceBall s hs.le R)
    (hleverage : ∀ᶠ i in uniformFamilyFilter l Θ, (m i).L ≤ K * (m i).N) :
    ConcreteUniformRiskEquivalence m l :=
  concreteUniformRiskEquivalence_of_product_rows m
    (polynomial_sourceBall_risk_equivalence (l := uniformFamilyFilter l Θ) m e J0 hβ hθ hθβ hs hR hc hC hs0 hnoise hn hreg hspectrum hsource hleverage)

theorem uniform_polynomial_universal_sourceBall_risk_equivalence
    (m : I × Θ → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (e : ∀ i, (m i).scaleModel.SpectrumEnumeration) (J0 : ℕ)
    {β θ s R c C : ℝ} (hβ : 1 < β) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs : 0 < s) (hR : 0 < R) (hc : 0 < c) (hC : 0 < C)
    (hsmooth : 1 - 1 / β < min s (residualComparisonOrder ρ))
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in uniformFamilyFilter l Θ, s0 ≤ (m i).σ)
    (hn : Tendsto (fun i => ((m i).n : ℝ)) (uniformFamilyFilter l Θ) atTop)
    (hreg : (fun i => (m i).lam) =Θ[uniformFamilyFilter l Θ] (fun i => ((m i).n : ℝ) ^ (-θ)))
    (hspectrum : ∀ᶠ i in uniformFamilyFilter l Θ, ∀ j : ℕ, J0 ≤ j →
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).scaleModel.eigenvalue (e i) j ∧
      (m i).scaleModel.eigenvalue (e i) j ≤ C * ((j : ℝ) + 1) ^ (-β))
    (hsource : ∀ᶠ i in uniformFamilyFilter l Θ, (m i).f ∈ (m i).scaleModel.SourceBall s hs.le R) :
    ConcreteUniformRiskEquivalence m l :=
  concreteUniformRiskEquivalence_of_product_rows m
    (polynomial_universal_sourceBall_risk_equivalence (l := uniformFamilyFilter l Θ) m e J0 hβ hθ hθ1 hs hR hc hC hsmooth hs0 hnoise hn hreg hspectrum hsource)

theorem uniform_exponential_sourceBall_risk_equivalence
    (m : I × Θ → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (e : ∀ i, (m i).scaleModel.SpectrumEnumeration) (J0 : ℕ)
    {θ s R c C c0 ν K : ℝ} (hθ : 0 < θ) (hs : 0 < s) (hR : 0 < R)
    (hc : 0 < c) (hC : 0 < C) (hc0 : 0 < c0) (hν : 0 < ν)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in uniformFamilyFilter l Θ, s0 ≤ (m i).σ)
    (hn : Tendsto (fun i => ((m i).n : ℝ)) (uniformFamilyFilter l Θ) atTop)
    (hreg : (fun i => (m i).lam) =Θ[uniformFamilyFilter l Θ] (fun i => ((m i).n : ℝ) ^ (-θ)))
    (hspectrum : ∀ᶠ i in uniformFamilyFilter l Θ, ∀ j : ℕ, J0 ≤ j →
      c * Real.exp (-c0 * ((j : ℝ) + 1) ^ ν) ≤ (m i).scaleModel.eigenvalue (e i) j ∧
      (m i).scaleModel.eigenvalue (e i) j ≤ C * Real.exp (-c0 * ((j : ℝ) + 1) ^ ν))
    (hsource : ∀ᶠ i in uniformFamilyFilter l Θ, (m i).f ∈ (m i).scaleModel.SourceBall s hs.le R)
    (hleverage : ∀ᶠ i in uniformFamilyFilter l Θ, (m i).L ≤ K * (m i).N) :
    ConcreteUniformRiskEquivalence m l :=
  concreteUniformRiskEquivalence_of_product_rows m
    (exponential_sourceBall_risk_equivalence (l := uniformFamilyFilter l Θ) m e J0 hθ hs hR hc hC hc0 hν hs0 hnoise hn hreg hspectrum hsource hleverage)


end
end KernelSeq
