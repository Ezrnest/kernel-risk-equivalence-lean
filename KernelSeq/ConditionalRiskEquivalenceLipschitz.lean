import KernelSeq.LocalizedLipschitz
import KernelSeq.ActualRiskAsymptotics
import KernelSeq.OriginalScaleParameters
import KernelSeq.ProvedBernstein

/-!
# Conditional risk equivalence with an explicit finite Lipschitz input

All project-specific localized estimates, actual chi multipliers and covariance
Bernstein concentration used here are proved locally. The finite dyadic
Lipschitz Schur estimate remains an explicit input for modular reuse;
`finiteDyadicLipschitzSchur_proved` in `FixedSymbolFourierLpBound` supplies
its actual constructor. The older all-exponent interface is retained separately.

The fixed canonical RKHS, fixed target, actual conditional prediction risk and
sequence benchmark use the original two scale conditions and the actual
essential supremum of normalized leverage. No separability of the prediction
L² space, positive population bias or retention lower bound is imposed.
The final wrapper preserves the older all-exponent interface through the
proved restriction to dyadic exponents, without a constant loss.
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

/-- The original-scale fixed-kernel conditional-risk conclusion with an
explicit finite dyadic Lipschitz input. Its actual constructor is
`finiteDyadicLipschitzSchur_proved` in `FixedSymbolFourierLpBound`. No covariance
concentration, chi Schur, localized interaction or risk identity is an input. -/
theorem rkhs_conditional_risk_equivalence_from_dyadic_lipschitz {CL : ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uH, uH, uH, uH} CL)
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
    TendstoInMeasure P (fun i ω =>
      rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f (φ i) (hlam i) (h i) ω /
        sequenceBenchmark k hk (φ i) f σ (n i)) l (fun _ => 1) ∧
    TendstoInMeasure P (fun i ω =>
      |rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f (φ i) (hlam i) (h i) ω -
        sequenceBenchmark k hk (φ i) f σ (n i)| /
          sequenceBenchmark k hk (φ i) f σ (n i)) l (fun _ => 0) := by
  dsimp only
  intro hsupport hQ hcompat hsource
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
    (localizedLipschitzConstant CL (residualComparisonOrder ρ) ρ A)
    (fun _ => hsupport) hL hQ hcompat hsource
    (fun _ => finiteSpectralBernstein_proved _ P)
  filter_upwards with i ω τ hτ hδ
  exact actual_localized_interaction_from_lipschitz hLip b k hk (φ i) (hlam i)
    hM (fun j => x i j ω) (hMX i ω) (hf i) (h i) hα0 hα1 hαρ τ hτ hδ f hsupport

/-- The existing all-exponent interface is retained by the proved restriction
to dyadic exponents, without any interpolation premise or constant loss. -/
theorem rkhs_conditional_risk_equivalence_from_lipschitz {CL : ℝ}
    (hLip : FiniteLipschitzSchur.{uH, uH, uH, uH} CL)
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
    TendstoInMeasure P (fun i ω =>
      rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f (φ i) (hlam i) (h i) ω /
        sequenceBenchmark k hk (φ i) f σ (n i)) l (fun _ => 1) ∧
    TendstoInMeasure P (fun i ω =>
      |rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f (φ i) (hlam i) (h i) ω -
        sequenceBenchmark k hk (φ i) f σ (n i)| /
          sequenceBenchmark k hk (φ i) f σ (n i)) l (fun _ => 0) := by
  exact rkhs_conditional_risk_equivalence_from_dyadic_lipschitz hLip.toDyadic hK κ hκ hdiag n hn Z hZ
    hlaw hind f σ hσ hmean hsecond lam hlam φ hf h

end
end KernelSeq
