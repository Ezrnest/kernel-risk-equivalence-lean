import KernelSeq.ConditionalRiskEquivalenceFourierLp
import KernelSeq.FixedSymbolFourierLpBound

/-!
# Original conditional risk equivalence without external analytic inputs

The actual covariance Bernstein and fixed-symbol Fourier estimates are proved
locally and supplied internally. This entry point has only the original model,
filter and scale assumptions; it has no analytic proof parameter.

The conclusion concerns a fixed kernel, design measure and target, the true
all-design conditional prediction risk, and the exact sequence benchmark.
Expectation-risk convergence and changing-kernel arrays are separate claims.
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

/-- The original fixed-kernel, fixed-target conditional-risk conclusion.
All general analytic estimates required by this proof are supplied by actual
local theorems, without a Fourier, HMS, Lipschitz or concentration premise. -/
theorem rkhs_conditional_risk_equivalence
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
  exact rkhs_conditional_risk_equivalence_from_fixed_even_fourier_lp
    fixedEvenFourierLpBound_proved hK κ hκ hdiag n hn Z hZ
    hlaw hind f σ hσ hmean hsecond lam hlam φ hf h

end
end KernelSeq
