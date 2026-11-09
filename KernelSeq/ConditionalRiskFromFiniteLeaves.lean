import KernelSeq.ActualRiskAsymptotics
import KernelSeq.OriginalScaleParameters
import KernelSeq.LocalizedCoreScale
import KernelSeq.FiniteLipschitzFromHMS

/-!
# Conditional risk equivalence from the named general finite leaves

This is the original fixed-kernel, fixed-target conditional-risk theorem, with
αψ = min(2ρ,1) and the actual essential supremum of normalized leverage.
The localized interaction inequality, the Hilbert basis, canonical-feature
measurability, and all stochastic comparison rates are derived internally.

The first interface displays general finite Bernstein, Lipschitz Schur, and HMS
propositions. The second interface derives the Lipschitz leaf from HMS.
The Bernstein parameter is now constructible in `ProvedBernstein`, and
`ConditionalRiskEquivalence` supplies it internally, leaving only HMS external.
These interfaces do not assert uniformity over changing kernels or
expectation-risk convergence. No separability of the prediction L² space is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace KernelSeq

noncomputable section

universe uH uX uΩ uJ

variable {H : Type uH} {X : Type uX} {Ω : Type uΩ} {J : Type uJ}
  [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {l : Filter J} [NeBot l]

/-- The manuscript's conditional-risk equivalence, with its two exact original scales.
Three general finite interfaces are displayed as explicit proof parameters.
The covariance Bernstein parameter is supplied by a local theorem in the newer wrapper.
In particular no project-specific localization, probability rate, or risk identity is assumed. -/
theorem rkhs_conditional_risk_equivalence_from_finite_leaves {CL CH : ℝ}
    (hLip : FiniteLipschitzSchur.{uH, uH, uH, uH} CL)
    (hHMS : FiniteHMS.{uH, uH, uH, uH} CH)
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (Z : (i : J) → Fin (n i) → Ω → X × ℝ)
    (hZ : ∀ i j, Measurable (Z i j))
    (hlaw : ∀ i j, MeasurePreserving (fun ω => (Z i j ω).1) P μ)
    (hind : ∀ i, iIndepFun (Z i) P) (f : Lp ℝ 2 μ) (σ : ℝ) (hσ : 0 < σ)
    (hmean : ∀ i j, P[observationNoise (Z i j) (lpRepresentative f) |
      observationDesignSigma (Z i j)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i j, P[(fun ω => observationNoise (Z i j) (lpRepresentative f) ω ^ 2) |
      observationDesignSigma (Z i j)] =ᵐ[P] (fun _ => σ ^ 2))
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i) {ρ A : ℝ} (φ : J → ℝ → ℝ)
    (hf : ∀ i, ResidualFilter.SpectralFilter (κ ^ 2) (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) (κ ^ 2) ρ A (φ i)) :
    let k := rkhsFeature (X := X) (H := H)
    let hk := rkhsFeature_memLp μ hK κ hκ hdiag
    let α := residualComparisonOrder ρ
    let L := fun i => featureLeverageEssentialSup k hk (lam i)
    let Q := fun i => featureFilterDimension k hk (φ i)
    f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure →
    (∀ᶠ i in l, 0 < Q i) →
    Tendsto (fun i => featureEffectiveDimension k hk (lam i) / Q i * Real.sqrt
      (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0) →
    Tendsto (fun i => (n i : ℝ) * featureSequenceSourceEnergy k hk (lam i) α f *
      originalBiasGamma (L i) (n i : ℝ) (featureEffectiveDimension k hk (lam i)) ^ 2 / Q i) l (𝓝 0) →
    (∀ i, FiniteSpectralBernstein (featureCovarianceBasis (bernsteinFeature k hk (lam i))
      (bernsteinFeature_memLp k hk (lam i))) P) →
    TendstoInMeasure P (fun i ω =>
      rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f (φ i) (hlam i) (h i) ω /
        sequenceBenchmark k hk (φ i) f σ (n i)) l (fun _ => 1) ∧
    TendstoInMeasure P (fun i ω =>
      |rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f (φ i) (hlam i) (h i) ω -
        sequenceBenchmark k hk (φ i) f σ (n i)| /
          sequenceBenchmark k hk (φ i) f σ (n i)) l (fun _ => 0) := by
  dsimp only
  intro hsupport hQ hcompat hsource hTropp
  let k := rkhsFeature (X := X) (H := H)
  let hk := rkhsFeature_memLp μ hK κ hκ hdiag
  let L := fun i => featureLeverageEssentialSup k hk (lam i)
  let hM := rkhs_population_covariance_bound (μ := μ) hK κ hκ hdiag
  let x := fun i j ω => (Z i j ω).1
  let hMX := fun i ω => rkhs_empirical_covariance_bound κ hκ hdiag (hn i) (fun j => x i j ω)
  let b : HilbertBasis (exists_hilbertBasis ℝ H).choose ℝ H :=
    (exists_hilbertBasis ℝ H).choose_spec.choose
  obtain ⟨i₀, _⟩ := hQ.exists
  have hα0 := residualComparisonOrder_pos (h i₀).rho_pos
  have hα1 := residualComparisonOrder_le_one ρ
  have hαρ := residualComparisonOrder_half_le ρ
  have hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i := by
    intro i
    exact normalizedLeverage_ae_le_essentialSup k hk (hlam i)
      (Eventually.of_forall fun y => by simpa only [k, rkhsFeature_norm_sq] using hdiag y)
  apply rkhs_conditional_risk_from_original_scales b hK κ hκ hdiag n hn Z hZ hlaw hind
    (fun _ => f) σ hσ hmean hsecond lam hlam hα0.le hαρ φ hf h L
    (localizedCoreConstant CL CH (residualComparisonOrder ρ) ρ A)
    (fun _ => hsupport) hL hQ hcompat hsource hTropp
  filter_upwards with i ω τ hτ hδ
  exact actual_localized_interaction_from_finite_analytic hLip hHMS b k hk (φ i) (hlam i)
    hM (fun j => x i j ω) (hMX i ω) (hf i) (h i) hα0 hα1 hαρ τ hτ hδ f hsupport


/-- The conditional-risk theorem with only the general finite HMS and Bernstein leaves.
The separate finite Lipschitz Schur premise is discharged by the proved Steklov/HMS
reduction. The newer wrapper also supplies the locally proved covariance Bernstein input. -/
theorem rkhs_conditional_risk_equivalence_from_hms_bernstein {CH : ℝ}
    (hHMS : FiniteHMS.{uH, uH, uH, uH} CH)
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (Z : (i : J) → Fin (n i) → Ω → X × ℝ)
    (hZ : ∀ i j, Measurable (Z i j))
    (hlaw : ∀ i j, MeasurePreserving (fun ω => (Z i j ω).1) P μ)
    (hind : ∀ i, iIndepFun (Z i) P) (f : Lp ℝ 2 μ) (σ : ℝ) (hσ : 0 < σ)
    (hmean : ∀ i j, P[observationNoise (Z i j) (lpRepresentative f) |
      observationDesignSigma (Z i j)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i j, P[(fun ω => observationNoise (Z i j) (lpRepresentative f) ω ^ 2) |
      observationDesignSigma (Z i j)] =ᵐ[P] (fun _ => σ ^ 2))
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i) {ρ A : ℝ} (φ : J → ℝ → ℝ)
    (hf : ∀ i, ResidualFilter.SpectralFilter (κ ^ 2) (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) (κ ^ 2) ρ A (φ i)) :
    let k := rkhsFeature (X := X) (H := H)
    let hk := rkhsFeature_memLp μ hK κ hκ hdiag
    let α := residualComparisonOrder ρ
    let L := fun i => featureLeverageEssentialSup k hk (lam i)
    let Q := fun i => featureFilterDimension k hk (φ i)
    f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure →
    (∀ᶠ i in l, 0 < Q i) →
    Tendsto (fun i => featureEffectiveDimension k hk (lam i) / Q i * Real.sqrt
      (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0) →
    Tendsto (fun i => (n i : ℝ) * featureSequenceSourceEnergy k hk (lam i) α f *
      originalBiasGamma (L i) (n i : ℝ) (featureEffectiveDimension k hk (lam i)) ^ 2 / Q i) l (𝓝 0) →
    (∀ i, FiniteSpectralBernstein (featureCovarianceBasis (bernsteinFeature k hk (lam i))
      (bernsteinFeature_memLp k hk (lam i))) P) →
    TendstoInMeasure P (fun i ω =>
      rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f (φ i) (hlam i) (h i) ω /
        sequenceBenchmark k hk (φ i) f σ (n i)) l (fun _ => 1) ∧
    TendstoInMeasure P (fun i ω =>
      |rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f (φ i) (hlam i) (h i) ω -
        sequenceBenchmark k hk (φ i) f σ (n i)| /
          sequenceBenchmark k hk (φ i) f σ (n i)) l (fun _ => 0) := by
  exact rkhs_conditional_risk_equivalence_from_finite_leaves
    (finiteLipschitzSchur_of_finiteHMS hHMS) hHMS hK κ hκ hdiag n hn Z hZ hlaw hind
    f σ hσ hmean hsecond lam hlam φ hf h

end
end KernelSeq
