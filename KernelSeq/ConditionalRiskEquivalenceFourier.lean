import KernelSeq.ConditionalRiskEquivalenceLipschitz
import KernelSeq.FiniteLipschitzFromFourier

/-!
# Conditional risk equivalence from one fixed Fourier multiplier estimate

The proved integer-grid transference and lattice approximation supply the
actual dyadic divided-difference input from `FixedEvenFourierL2Bound`.
That sufficient external Fourier estimate remains unproved: it concerns the
fixed smooth even planar symbol on actual finite matrix-valued trigonometric
polynomials, with the outer torus L2 norm and dyadic Schatten exponents.

The original model and two scale conditions, actual conditional prediction
risk and exact sequence benchmark are unchanged. This file is a conditional
interface and does not assert an unconditional proof of the main theorem.
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

/-- The original fixed-kernel, fixed-target conditional-risk conclusion from
one explicitly unproved fixed-symbol Fourier estimate common to every model
and filter. -/
theorem rkhs_conditional_risk_equivalence_from_fixed_even_fourier {C : ℝ}
    (hF : FixedEvenFourierL2Bound.{uH, uH, uH} C)
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
  exact rkhs_conditional_risk_equivalence_from_dyadic_lipschitz
    (finiteDyadicLipschitzSchur_of_fixedEvenFourier hF) hK κ hκ hdiag n hn Z hZ
    hlaw hind f σ hσ hmean hsecond lam hlam φ hf h

end
end KernelSeq
