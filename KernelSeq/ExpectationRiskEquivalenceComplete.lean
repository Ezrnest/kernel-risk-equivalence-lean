import KernelSeq.ExpectationBiasAsymptotics
import KernelSeq.ExpectationVarianceAsymptotics
import KernelSeq.ExpectationGoodRiskAssembly
import KernelSeq.ExpectationBadAsymptotics
import KernelSeq.ExpectationBadProbability
import KernelSeq.ExpectationRiskAssembly

/-!
# Original expectation-risk equivalence without external analytic inputs

The actual good-event L1 bias and variance estimates and actual bad-design
risk estimates are supplied internally. The additional assumption is exactly
the manuscript's logarithmic expectation scale. The original observation
loss is genuinely integrable and its tower identity identifies expectation
risk, rather than using a default conditional-expectation value.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace KernelSeq
noncomputable section

variable {H X Ω J : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {l : Filter J} [NeBot l]

/-- The original fixed-kernel, fixed-target expectation-risk theorem, with
the true estimator loss and exact sequence benchmark. No good/bad-event,
moment, multiplier, concentration or integrability certificate is a premise. -/
theorem rkhs_expectation_risk_equivalence
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
    Tendsto (fun i => L i / (n i : ℝ) *
      Real.log (Real.exp 1 + (n i : ℝ) / (lam i * Q i))) l (𝓝 0) →
    Tendsto (fun i => rkhsExpectationPredictionRisk (P := P) hK κ hκ hdiag
      (hn i) (Z i) f (φ i) (hlam i) (h i) / sequenceBenchmark k hk (φ i) f σ (n i)) l (𝓝 1) ∧
    Tendsto (fun i =>
      (∫ ω, |rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f
        (φ i) (hlam i) (h i) ω - sequenceBenchmark k hk (φ i) f σ (n i)| ∂P) /
          sequenceBenchmark k hk (φ i) f σ (n i)) l (𝓝 0) := by
  dsimp only
  intro hsupport hQ hcompat hsource hexpect
  let k := rkhsFeature (X := X) (H := H)
  let hk := rkhsFeature_memLp μ hK κ hκ hdiag
  let hks := rkhsFeature_stronglyMeasurable hK
  let hkb := rkhsFeature_norm_le κ hκ hdiag
  let hM := rkhs_population_covariance_bound (μ := μ) hK κ hκ hdiag
  let x := fun i j ω => (Z i j ω).1
  let hMX := fun i ω => rkhs_empirical_covariance_bound κ hκ hdiag (hn i) (fun j => x i j ω)
  let L := fun i => featureLeverageEssentialSup k hk (lam i)
  let Q := fun i => featureFilterDimension k hk (φ i)
  let a := fun i => σ ^ 2 / (n i : ℝ)
  let b₀ := fun i => ‖populationSpectralResidual k hk (φ i) hM (hf i) f‖ ^ 2
  let B := fun i ω => actualEmpiricalBiasEnergy k hk (φ i) (hlam i)
    (fun j => x i j ω) (hMX i ω) (h i) f
  let V := fun i ω => actualVarianceEnergy k hk (φ i) (hlam i)
    (fun j => x i j ω) (hMX i ω) (h i)
  let R := fun i ω => rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag
    (hn i) (Z i) f (φ i) (hlam i) (h i) ω
  let D := fun i => sequenceBenchmark k hk (φ i) f σ (n i)
  let G := fun i => {ω | actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) ≤ 1 / 4}
  let basis := featureCovarianceBasis k hk
  have hxind (i : J) : iIndepFun (x i) P :=
    (hind i).comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  have hL (i : J) : ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i :=
    normalizedLeverage_ae_le_essentialSup k hk (hlam i) (Eventually.of_forall fun y =>
      pow_le_pow_left₀ (norm_nonneg _) (hkb y) 2)
  obtain ⟨i₀, _⟩ := hQ.exists
  have hα0 := residualComparisonOrder_pos (h i₀).rho_pos
  have hα1 := residualComparisonOrder_le_one ρ
  have hαρ := residualComparisonOrder_half_le ρ
  have hbias := actual_good_bias_relative_L1_of_original_scales basis n hn x hlaw hxind
    k hk hks κ hκ hkb lam hlam φ hM hMX hf h hα0 hα1 hαρ (fun _ => f)
    (fun _ => hsupport) σ hσ L hL hQ hcompat hsource
  have hvariance := actual_good_variance_relative_L1_of_compatibility
    n hn x hlaw hxind k hk hks lam hlam φ hM hMX hf h L hL hQ hcompat
  have hce (i : J) := rkhs_conditional_prediction_risk_energy hK κ hκ hdiag (hn i)
    (Z i) (hZ i) (hlaw i) f σ hσ (hind i) (hmean i) (hsecond i) (φ i) (hlam i) (hf i) (h i)
  have hRint (i : J) : Integrable (R i) P :=
    integrable_rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f
      (φ i) (hlam i) (h i)
  have hBint (i : J) : Integrable (B i) P :=
    integrable_actualEmpiricalBiasEnergy (hn i) (x i) (hlaw i) k hk hks κ hκ hkb
      (hMX i) (φ i) (hlam i) (hf i) (h i) f
  have ha (i : J) : 0 < a i := div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr (hn i))
  have hident (i : J) : R i =ᵐ[P] (fun ω => B i ω + a i * V i ω) := by
    simpa only [R, B, a, V, rkhsVarianceEnergy, rkhsConditionalPredictionRisk, k, hk, x] using (hce i).2
  have hgood := good_risk_relative_L1_of_bias_variance R B V b₀ a Q G
    (fun _ => sq_nonneg _) ha hQ hRint hBint hident hbias hvariance
  have hDeq (i : J) : D i = b₀ i + a i * Q i :=
    sequenceBenchmark_eq_population k hk (φ i) hM (hf i) hsupport σ (n i)
  have hgood' : Tendsto (fun i => (∫ ω in G i, |R i ω - D i| ∂P) / D i) l (𝓝 0) := by
    simp only [← integral_div]
    apply hgood.congr'
    exact Eventually.of_forall fun i => by
      change (∫ ω in G i, |R i ω - (b₀ i + a i * Q i)| / (b₀ i + a i * Q i) ∂P) =
        (∫ ω in G i, |R i ω - D i| / D i ∂P)
      rw [hDeq i]
  have hbad := rkhs_bad_risk_from_original_expectation_scale hK κ hκ hdiag n hn Z hZ hlaw
    hind f σ hσ hmean hsecond lam hlam φ hf h hsupport hQ hcompat hexpect
  have hprob := feature_bad_design_probability_of_original_compatibility n hn x hlaw hxind
    k hk lam hlam hM φ hf h L hL hQ hcompat
  have hG (i : J) : MeasurableSet (G i) :=
    measurableSet_le (stronglyMeasurable_actualCovarianceDeviation k hk (lam i) (x i)
      (fun j => hks.comp_measurable (hlaw i j).measurable)).measurable measurable_const
  have hGc (i : J) : (G i)ᶜ = {ω | 1 / 4 < actualCovarianceDeviation k hk (lam i)
      (fun j => x i j ω)} := by
    ext ω
    simp only [G, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have hDpos : ∀ᶠ i in l, 0 < D i := hQ.mono fun i hi => by
    rw [hDeq i]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (ha i) hi)
  have hfinal := risk_expectation_from_good_bad_integrals R D G hG hRint
    (fun i => rkhsConditionalPredictionRisk_nonneg_ae (P := P) hK κ hκ hdiag
      (hn i) (Z i) f (φ i) (hlam i) (h i)) hDpos hgood'
    (by simpa only [hGc] using hbad)
    (by simpa only [hGc, Measure.real] using hprob)
  refine ⟨?_, hfinal.2⟩
  apply hfinal.1.congr'
  filter_upwards with i
  rw [rkhsExpectationPredictionRisk_eq_integral_conditional_of_integrable hK κ hκ hdiag
    (hn i) (Z i) (hZ i) f (φ i) (hlam i) (h i) (hce i).1]

end
end KernelSeq
