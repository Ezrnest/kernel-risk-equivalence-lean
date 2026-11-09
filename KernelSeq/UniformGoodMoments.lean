import KernelSeq.ExpectationMixedEndpoint
import KernelSeq.ExpectationVarianceAsymptotics

/-!
# Uniform finite-row covariance and mixed-endpoint moments

These are genuine finite-model estimates, with a visible scalar smallness
condition on the intrinsic linear term. Every operator moment is proved from
the actual iid feature sample; no moment bound is a hypothesis. Constants do
not depend on the underlying Hilbert space, sample space, law or target.
-/

open MeasureTheory ProbabilityTheory

namespace KernelSeq
noncomputable section

/-- One numerical constant for every finite row. -/
def uniformCovarianceMomentConstant : ℝ := 768 * Real.exp 1

theorem uniformCovarianceMomentConstant_nonneg : 0 ≤ uniformCovarianceMomentConstant := by
  unfold uniformCovarianceMomentConstant
  positivity

variable {ι H X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The actual sharp operator second moment on a single row. The sole
smallness hypothesis is the displayed deterministic intrinsic-log ratio,
which is forced eventually by the original compatibility condition. -/
theorem integral_actualCovarianceDeviation_sq_le_uniform_row (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (hind : iIndepFun x P)
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A L : ℝ}
    (hlam : 0 < lam) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hQ : 0 < featureFilterDimension k hk φ)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hsmall : Real.sqrt (L * dimensionLog (featureEffectiveDimension k hk lam) / (n : ℝ)) *
      intrinsicDimensionLog (featureEffectiveDimension k hk lam) (featureCovarianceRetention k hk lam) /
        dimensionLog (featureEffectiveDimension k hk lam) ≤ 1) :
    (∫ ω, actualCovarianceDeviation k hk lam (fun j => x j ω) ^ 2 ∂P) ≤
      uniformCovarianceMomentConstant * (L * dimensionLog (featureEffectiveDimension k hk lam) / (n : ℝ)) := by
  let N := featureEffectiveDimension k hk lam
  let r := featureCovarianceRetention k hk lam
  let v := L * dimensionLog N / (n : ℝ)
  have hLn : 0 ≤ L := feature_sq_bound_nonneg (bernsteinFeature k hk lam) hL
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hN : 0 ≤ N := featureEffectiveDimension_nonneg k hk lam hlam
  have hr : 0 < r := featureCovarianceRetention_pos_of_filterDimension_pos k hk φ hlam hM hf h hQ
  have hr1 : r ≤ 1 := featureCovarianceRetention_le_one k hk lam hlam
  have hfirst : L * r * intrinsicDimensionLog N r / (n : ℝ) ≤ 2 * v := by
    have hh := mul_le_mul_of_nonneg_left (retention_mul_intrinsicDimensionLog_le hN hr hr1) hLn
    calc
      _ ≤ L * (2 * dimensionLog N) / (n : ℝ) := by
        simpa only [mul_assoc] using div_le_div_of_nonneg_right hh hnR.le
      _ = _ := by dsimp only [v]; ring
  have hsecond : (L * intrinsicDimensionLog N r / (n : ℝ)) ^ 2 ≤ v :=
    intrinsic_linear_sq_le_variance hnR hLn hN hr hsmall
  have hm := integral_actualCovarianceDeviation_sq_le_intrinsic b k hk hlam hn x hlaw hind hL hr
  calc
    _ ≤ (16 * Real.exp 1) * (8 * (L * r * intrinsicDimensionLog N r / (n : ℝ)) +
        32 * (L * intrinsicDimensionLog N r / (n : ℝ)) ^ 2) := hm
    _ ≤ (16 * Real.exp 1) * (8 * (2 * v) + 32 * v) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
        (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = _ := by dsimp only [uniformCovarianceMomentConstant, v]; ring

/-- The true measurable mixed-endpoint envelope has a finite-row γ²
moment with a numerical constant common to all models. Neither an operator
moment nor an optimized-endpoint measurability certificate is an input. -/
theorem integral_actualMixedEndpointEnvelope_sq_le_uniform_row (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (hind : iIndepFun x P)
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A L : ℝ}
    (hlam : 0 < lam) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hQ : 0 < featureFilterDimension k hk φ)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hsmall : Real.sqrt (L * dimensionLog (featureEffectiveDimension k hk lam) / (n : ℝ)) *
      intrinsicDimensionLog (featureEffectiveDimension k hk lam) (featureCovarianceRetention k hk lam) /
        dimensionLog (featureEffectiveDimension k hk lam) ≤ 1) :
    (∫ ω, actualMixedEndpointEnvelope b k hk lam (fun j => x j ω) ^ 2 ∂P) ≤
      mixedEndpointMomentConstant * originalBiasGamma L (n : ℝ) (featureEffectiveDimension k hk lam) ^ 2 := by
  let δ := fun ω => actualCovarianceDeviation k hk lam (fun j => x j ω)
  let η := fun ω => ‖normalizedHSCovarianceFluctuation b k hk lam (fun j => x j ω)‖
  let p := mixedMomentExponent (featureEffectiveDimension k hk lam / dimensionLog (featureEffectiveDimension k hk lam))
  have hδm := integral_actualCovarianceDeviation_sq_le_uniform_row b hn x hlaw hind k hk φ hlam hM hf h hQ hL hsmall
  have hLn : 0 ≤ L := feature_sq_bound_nonneg (bernsteinFeature k hk lam) hL
  have hN := featureEffectiveDimension_pos_of_filterDimension_pos k hk φ hlam hM hf h hQ
  have hC : 1 ≤ 768 * Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hηm : (∫ ω, η ω ^ 2 ∂P) ≤
      (768 * Real.exp 1) * (L * featureEffectiveDimension k hk lam / (n : ℝ)) := by
    calc
      _ ≤ L / (n : ℝ) * featureEffectiveDimension k hk lam :=
        integral_normalizedHSCovarianceFluctuation_sq_le b hn x hlaw
          (fun _ _ hij => hind.indepFun hij) k hk lam hlam hL
      _ = L * featureEffectiveDimension k hk lam / (n : ℝ) := by ring
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hC
  have hm := integral_mixedMomentAmplitude_sq_le_originalBiasGamma
    (memLp_actualCovarianceDeviation b hn x hlaw k hk lam hL)
    (memLp_normalizedHSCovarianceFluctuation b hn x hlaw k hk lam hL).norm
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (zero_le_one.trans hC) hLn (Nat.cast_pos.mpr hn) hN hδm hηm
  have he : (∫ ω, actualMixedEndpointEnvelope b k hk lam (fun j => x j ω) ^ 2 ∂P) =
      4 * ∫ ω, mixedMomentAmplitude p δ η ω ^ 2 ∂P := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      dsimp only [actualMixedEndpointEnvelope, mixedMomentAmplitude, p, δ, η]
      ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by
    dsimp only [mixedEndpointMomentConstant]
    ring)

end
end KernelSeq
