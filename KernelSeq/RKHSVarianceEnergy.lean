import KernelSeq.RKHSConditionalRisk
import KernelSeq.VarianceCompatibility
import KernelSeq.ActualBiasTransfer

/-!
# The actual conditional-risk variance energy

Connects the actual canonical RKHS conditional risk to the same prediction
variance energy controlled by the variance-compatible concentration chain.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace KernelSeq

variable {X H Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  {μ : Measure X} [IsProbabilityMeasure μ] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The actual unscaled conditional-variance energy, using the canonical
feature. Its spectral interval bound is derived from the original kernel. -/
noncomputable def rkhsVarianceEnergy
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) : ℝ :=
  actualVarianceEnergy (rkhsFeature (X := X) (H := H)) (rkhsFeature_memLp μ hK κ hκ hdiag)
    φ hlam x (norm_empiricalCovariance_le_bound hn _ κ
      (fun j => pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ hκ hdiag (x j)) 2)) h

/-- The noise coefficients in the conditional risk yield exactly `σ²/n`
times the actual energy controlled by the variance comparison. -/
theorem rkhsEmpiricalCoefficient_variance_eq_energy
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (σ : ℝ) :
    σ ^ 2 * ∑ i, ‖rkhsEmpiricalCoefficient (μ := μ) hK κ hκ hdiag hn x φ hlam h i‖ ^ 2 =
      σ ^ 2 / (n : ℝ) * rkhsVarianceEnergy (μ := μ) hK κ hκ hdiag hn x φ hlam h := by
  have heq : rkhsVarianceEnergy (μ := μ) hK κ hκ hdiag hn x φ hlam h =
      ‖empiricalVarianceColumns (fun j => rkhsFeature (X := X) (H := H) (x j))
        (rkhsEmpiricalPredictionMap (μ := μ) hK κ hκ hdiag hn x φ hlam h)
        (empiricalCovarianceBasis (fun j => rkhsFeature (X := X) (H := H) (x j)))‖ ^ 2 := by
    rfl
  rw [heq]
  exact rkhsEmpiricalCoefficient_variance_eq_hs hK κ hκ hdiag hn x φ hlam h _ σ

omit [IsProbabilityMeasure P] in
/-- The source conditional mean uses the globally measurable target
representative, while the actual bias comparison uses the same `Lp` target.
Their empirical bias energies agree almost surely under the real sample law. -/
theorem rkhs_conditional_mean_bias_eq_actual_ae
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (f : Lp ℝ 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    ∀ᵐ ω ∂P,
      ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => x j ω)
        (fun j => lpRepresentative f (x j ω)) φ hlam h - f‖ ^ 2 =
      actualEmpiricalBiasEnergy (rkhsFeature (X := X) (H := H)) (rkhsFeature_memLp μ hK κ hκ hdiag)
        φ hlam (fun j => x j ω) (norm_empiricalCovariance_le_bound hn _ κ
          (fun j => pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ hκ hdiag (x j ω)) 2)) h f := by
  have hae : ∀ᵐ ω ∂P, ∀ j, lpRepresentative f (x j ω) = f (x j ω) := by
    apply ae_all_iff.mpr
    intro j
    exact (hlaw j).quasiMeasurePreserving.ae (lpRepresentative_ae_eq f)
  filter_upwards [hae] with ω hω
  have hfun : (fun j => lpRepresentative f (x j ω)) = (fun j => f (x j ω)) := funext hω
  simp only [rkhsEmpiricalPrediction, empiricalSpectralEstimator, empiricalFilterOperator,
    actualEmpiricalBiasEnergy, actualMeanPrediction, rkhsEmbedding]
  rw [hfun]

/-- The actual canonical conditional prediction risk, with its variance
written in exactly the energy used by the compatible-scale theorem. -/
theorem rkhs_conditional_prediction_risk_energy
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, MeasurePreserving (fun ω => (Z i ω).1) P μ) (f : Lp ℝ 2 μ)
    (σ : ℝ) (hσ : 0 < σ) (hind : iIndepFun Z P)
    (hmean : ∀ i, P[observationNoise (Z i) (lpRepresentative f) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => observationNoise (Z i) (lpRepresentative f) ω ^ 2) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => σ ^ 2))
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ) (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    Integrable (fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
      (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) P ∧
    P[(fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
      (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) | ⨆ j, observationDesignSigma (Z j)] =ᵐ[P]
      (fun ω => actualEmpiricalBiasEnergy (rkhsFeature (X := X) (H := H))
        (rkhsFeature_memLp μ hK κ hκ hdiag) φ hlam (fun j => (Z j ω).1)
        (norm_empiricalCovariance_le_bound hn _ κ
          (fun j => pow_le_pow_left₀ (norm_nonneg _)
            (rkhsFeature_norm_le κ hκ hdiag ((Z j ω).1)) 2)) h f +
        σ ^ 2 / (n : ℝ) * rkhsVarianceEnergy (μ := μ) hK κ hκ hdiag hn
          (fun j => (Z j ω).1) φ hlam h) := by
  have hr := rkhs_conditional_prediction_risk hK κ hκ hdiag hn Z hZ hlaw f σ hσ hind hmean hsecond φ hlam hf h
  refine ⟨hr.1, ?_⟩
  have hB := rkhs_conditional_mean_bias_eq_actual_ae hK κ hκ hdiag hn
    (fun j ω => (Z j ω).1) hlaw f φ hlam h
  filter_upwards [hr.2, hB] with ω hω hBω
  rw [hω, hBω, rkhsEmpiricalCoefficient_variance_eq_energy hK κ hκ hdiag hn
    (fun j => (Z j ω).1) φ hlam h σ]

/-- The relative variance comparison for the canonical RKHS, with both
covariance spectral bounds derived from the kernel. The original compatible
scale and the visible external finite Bernstein leaf are the only rate inputs.
The common positive noise scale is the actual `σ²/n` of conditional risk. -/
theorem rkhs_variance_relative_of_compatibility {ι : Type*} {l : Filter ι}
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (φ : ι → ℝ → ℝ) {ρ A : ℝ}
    (hf : ∀ i, ResidualFilter.SpectralFilter (κ ^ 2) (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) (κ ^ 2) ρ A (φ i))
    (L : ι → ℝ) (σ : ℝ) (hσ : 0 < σ) :
    let k := rkhsFeature (X := X) (H := H)
    let hk := rkhsFeature_memLp μ hK κ hκ hdiag
    let Q := fun i => featureFilterDimension k hk (φ i)
    (∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i) →
    (∀ᶠ i in l, 0 < Q i) →
    Tendsto (fun i => featureEffectiveDimension k hk (lam i) / Q i *
      Real.sqrt (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0) →
    (∀ i, FiniteSpectralBernstein
      (featureCovarianceBasis (bernsteinFeature k hk (lam i)) (bernsteinFeature_memLp k hk (lam i))) P) →
    TendstoInMeasure P (fun i ω =>
      |σ ^ 2 / (n i : ℝ) * rkhsVarianceEnergy (μ := μ) hK κ hκ hdiag (hn i)
          (fun j => x i j ω) (φ i) (hlam i) (h i) - σ ^ 2 / (n i : ℝ) * Q i| /
        (σ ^ 2 / (n i : ℝ) * Q i)) l (fun _ => 0) := by
  dsimp only
  intro hL hQ hcompat hTropp
  let k := rkhsFeature (X := X) (H := H)
  let hk := rkhsFeature_memLp μ hK κ hκ hdiag
  have hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ κ ^ 2 := by
    apply populationCovariance_norm_le_feature_bound k hk
    exact Eventually.of_forall (fun y => by simpa only [k, rkhsFeature_norm_sq] using hdiag y)
  have hMX (i : ι) (ω : Ω) : ‖empiricalCovariance (fun j => k (x i j ω))‖ ≤ κ ^ 2 :=
    norm_empiricalCovariance_le_bound (hn i) _ κ
      (fun j => by simpa only [k, rkhsFeature_norm_sq] using hdiag (x i j ω))
  have hr := actual_variance_relative_of_compatibility n hn x hlaw hind k hk lam hlam
    hM hMX φ hf h L hL hQ hcompat hTropp
  apply TendstoInMeasure.congr_left (fun i => Eventually.of_forall (fun ω => ?_)) hr
  exact (positive_scaled_variance_relative_error _ _ (σ ^ 2 / (n i : ℝ))
    (div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr (hn i)))).symm

end KernelSeq
