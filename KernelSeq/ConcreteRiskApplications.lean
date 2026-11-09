import KernelSeq.PolynomialAsymptoticScaleVerification
import KernelSeq.ExponentialScaleVerification
import KernelSeq.UniformRiskEquivalence

/-!
# Actual risk equivalence in the concrete spectral-decay examples

The three original scale limits are proved from the primitive spectral,
source, leverage and regularization conditions before invoking the complete
risk theorem. No scale, moment or risk estimate is an application premise.
-/

open MeasureTheory Filter Topology Asymptotics

namespace KernelSeq
noncomputable section

universe uH uX uΩ
variable {J : Type*} {l : Filter J} [NeBot l] {κ ρ A s0 : ℝ}

def ConcreteRowRiskEquivalence (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (l : Filter J) : Prop :=
  (∀ ε > 0, Tendsto (fun i => (m i).P
    {ω | ε < |(m i).conditionalRisk ω / (m i).benchmark - 1|}) l (𝓝 0)) ∧
    Tendsto (fun i => (m i).expectationRisk / (m i).benchmark) l (𝓝 1) ∧
    Tendsto (fun i => (m i).normalizedL1) l (𝓝 0)

theorem concreteRowRiskEquivalence_of_verified_scales
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, s0 ≤ (m i).σ)
    (hscales : (∀ᶠ i in l, 0 < (m i).scaleModel.Q) ∧
      Tendsto (fun i => (m i).scaleModel.compatibility) l (𝓝 0) ∧
      Tendsto (fun i => (m i).scaleModel.sourceBalance) l (𝓝 0) ∧
      Tendsto (fun i => (m i).scaleModel.expectationScale) l (𝓝 0)) :
    ConcreteRowRiskEquivalence m l := by
  have hQ : ∀ᶠ i in l, 0 < (m i).Q := hscales.1
  have hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0) := by simpa only [TriangularRiskModel.scaleModel_compatibility] using hscales.2.1
  have hz : Tendsto (fun i => (m i).sourceBalance) l (𝓝 0) := by simpa only [TriangularRiskModel.scaleModel_sourceBalance] using hscales.2.2.1
  have he : Tendsto (fun i => (m i).expectationScale) l (𝓝 0) := by simpa only [TriangularRiskModel.scaleModel_expectationScale] using hscales.2.2.2
  exact ⟨triangular_conditional_risk_equivalence m hs0 hnoise hQ hc hz,
    triangular_expectation_risk_equivalence m hs0 hnoise hQ hc hz he⟩

theorem polynomial_sourceBall_risk_equivalence
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (e : ∀ i, (m i).scaleModel.SpectrumEnumeration) (J0 : ℕ)
    {β θ s R c C K : ℝ} (hβ : 1 < β) (hθ : 0 < θ) (hθβ : θ < β)
    (hs : 0 < s) (hR : 0 < R) (hc : 0 < c) (hC : 0 < C)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, s0 ≤ (m i).σ)
    (hn : Tendsto (fun i => ((m i).n : ℝ)) l atTop)
    (hreg : (fun i => (m i).lam) =Θ[l] (fun i => ((m i).n : ℝ) ^ (-θ)))
    (hspectrum : ∀ᶠ i in l, ∀ j : ℕ, J0 ≤ j →
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).scaleModel.eigenvalue (e i) j ∧
      (m i).scaleModel.eigenvalue (e i) j ≤ C * ((j : ℝ) + 1) ^ (-β))
    (hsource : ∀ᶠ i in l, (m i).f ∈ (m i).scaleModel.SourceBall s hs.le R)
    (hleverage : ∀ᶠ i in l, (m i).L ≤ K * (m i).N) :
    ConcreteRowRiskEquivalence m l :=
  concreteRowRiskEquivalence_of_verified_scales m hs0 hnoise
    (polynomial_sourceBall_original_scales_of_spectral_threshold
      (fun i => (m i).scaleModel) e J0 hβ hθ hθβ hs hR hc hC hn hreg hspectrum hsource hleverage)

theorem polynomial_universal_sourceBall_risk_equivalence
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (e : ∀ i, (m i).scaleModel.SpectrumEnumeration) (J0 : ℕ)
    {β θ s R c C : ℝ} (hβ : 1 < β) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs : 0 < s) (hR : 0 < R) (hc : 0 < c) (hC : 0 < C)
    (hsmooth : 1 - 1 / β < min s (residualComparisonOrder ρ))
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, s0 ≤ (m i).σ)
    (hn : Tendsto (fun i => ((m i).n : ℝ)) l atTop)
    (hreg : (fun i => (m i).lam) =Θ[l] (fun i => ((m i).n : ℝ) ^ (-θ)))
    (hspectrum : ∀ᶠ i in l, ∀ j : ℕ, J0 ≤ j →
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).scaleModel.eigenvalue (e i) j ∧
      (m i).scaleModel.eigenvalue (e i) j ≤ C * ((j : ℝ) + 1) ^ (-β))
    (hsource : ∀ᶠ i in l, (m i).f ∈ (m i).scaleModel.SourceBall s hs.le R) :
    ConcreteRowRiskEquivalence m l :=
  concreteRowRiskEquivalence_of_verified_scales m hs0 hnoise
    (polynomial_universal_sourceBall_original_scales_of_spectral_threshold
      (fun i => (m i).scaleModel) e J0 hβ hθ hθ1 hs hR hc hC hsmooth hn hreg hspectrum hsource)

theorem exponential_sourceBall_risk_equivalence
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A)
    (e : ∀ i, (m i).scaleModel.SpectrumEnumeration) (J0 : ℕ)
    {θ s R c C c0 ν K : ℝ} (hθ : 0 < θ) (hs : 0 < s) (hR : 0 < R)
    (hc : 0 < c) (hC : 0 < C) (hc0 : 0 < c0) (hν : 0 < ν)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, s0 ≤ (m i).σ)
    (hn : Tendsto (fun i => ((m i).n : ℝ)) l atTop)
    (hreg : (fun i => (m i).lam) =Θ[l] (fun i => ((m i).n : ℝ) ^ (-θ)))
    (hspectrum : ∀ᶠ i in l, ∀ j : ℕ, J0 ≤ j →
      c * Real.exp (-c0 * ((j : ℝ) + 1) ^ ν) ≤ (m i).scaleModel.eigenvalue (e i) j ∧
      (m i).scaleModel.eigenvalue (e i) j ≤ C * Real.exp (-c0 * ((j : ℝ) + 1) ^ ν))
    (hsource : ∀ᶠ i in l, (m i).f ∈ (m i).scaleModel.SourceBall s hs.le R)
    (hleverage : ∀ᶠ i in l, (m i).L ≤ K * (m i).N) :
    ConcreteRowRiskEquivalence m l :=
  concreteRowRiskEquivalence_of_verified_scales m hs0 hnoise
    (exponential_sourceBall_original_scales (fun i => (m i).scaleModel) e J0
      hθ hs hR hc hC hc0 hν hn hreg hspectrum hsource hleverage)

end
end KernelSeq
