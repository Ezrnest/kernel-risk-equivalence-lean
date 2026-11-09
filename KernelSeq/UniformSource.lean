import KernelSeq.SequenceBenchmark
import KernelSeq.OriginalBiasAsymptotics
import KernelSeq.ExpectationScale

/-!
# Uniform control of actual supported targets by the original source scale

Parseval in the actual positive singular system controls the target norm.
No target-norm bound is assumed. The original filter and leverage estimates
then control the source energy by its normalized balance parameter.
-/

open MeasureTheory Filter
open scoped BigOperators

namespace KernelSeq
noncomputable section

theorem regularized_source_weight_inverse_bound {lam M t α : ℝ}
    (hlam : 0<lam) (hM : 0≤M) (ht : t∈Set.Icc (0:ℝ) M) (hα : 0≤α) :
    1 ≤ (1+M/lam)^α * (lam/(t+lam))^α := by
  have hMt : 0<M+lam := by linarith
  have htt : 0<t+lam := by linarith [ht.1]
  have hb : 0≤1+M/lam := by positivity
  have hw : lam/(M+lam) ≤ lam/(t+lam) :=
    div_le_div_of_nonneg_left hlam.le htt (by linarith [ht.2])
  have hp : (1+M/lam)^α * (lam/(M+lam))^α = 1 := by
    rw [← Real.mul_rpow hb (div_nonneg hlam.le hMt.le)]
    have he : (1+M/lam)*(lam/(M+lam))=1 := by field_simp; ring
    rw [he, Real.one_rpow]
  calc
    1 = (1+M/lam)^α * (lam/(M+lam))^α := hp.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg hlam.le hMt.le) hw hα)
      (Real.rpow_nonneg hb _)

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual supported target norm is bounded by its actual source series,
in exactly the same positive singular coordinates as the sequence benchmark. -/
theorem norm_sq_le_source_energy (k : X → H) (hk : MemLp k 2 μ)
    {lam M α : ℝ} (hlam : 0<lam) (hα : 0≤α)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (f : Lp ℝ 2 μ)
    (hsupport : f∈(predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure) :
    ‖f‖^2 ≤ (1+M/lam)^α * featureSequenceSourceEnergy k hk lam α f := by
  have hs : f∈PredictionRange (featureEmbedding μ k hk) := by
    simpa only [predictionCovariance, closure_range_self_comp_adjoint] using hsupport
  have hparseval := predictionSingularBasis_parseval (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) hs
  have hcoeff := featureSequenceCoefficient_sq_summable k hk hs
  have hsource := summable_featureSequenceSourceEnergy k hk hlam hα hs
  have hpoint (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
      featureSequenceCoefficient k hk f i^2 ≤
        (1+M/lam)^α * ((lam/(i.1.1+lam))^α * featureSequenceCoefficient k hk f i^2) := by
    have hh := regularized_source_weight_inverse_bound hlam ((norm_nonneg _).trans hM)
      (featureCovarianceEigenvalue_mem k hk hM i.1) hα
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hh (sq_nonneg (featureSequenceCoefficient k hk f i))
  have hsum := Summable.tsum_le_tsum hpoint hcoeff (hsource.mul_left ((1+M/lam)^α))
  rw [tsum_mul_left] at hsum
  exact hparseval.trans_le hsum

/-- For the original order α≤1 the norm envelope is linear in `lambda^-1`. -/
theorem norm_sq_le_linear_source_energy (k : X → H) (hk : MemLp k 2 μ)
    {lam M α : ℝ} (hlam : 0<lam) (hα : 0≤α) (hα1 : α≤1)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (f : Lp ℝ 2 μ)
    (hsupport : f∈(predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure) :
    ‖f‖^2 ≤ (1+M/lam)*featureSequenceSourceEnergy k hk lam α f := by
  have hMn : 0≤M := (norm_nonneg _).trans hM
  have hb : 1≤1+M/lam := le_add_of_nonneg_right (div_nonneg hMn hlam.le)
  have hp := Real.rpow_le_rpow_of_exponent_le hb hα1
  rw [Real.rpow_one] at hp
  exact (norm_sq_le_source_energy k hk hlam hα hM f hsupport).trans
    (mul_le_mul_of_nonneg_right hp (featureSequenceSourceEnergy_nonneg k hk hlam f))

theorem originalBiasGamma_sq_mul_sample_ge_leverage {L n N : ℝ}
    (hL : 0≤L) (hn : 0<n) (hN : 0≤N) :
    L ≤ n*originalBiasGamma L n N^2 := by
  have hell := one_le_dimensionLog hN
  have hlog : 1≤Real.log (Real.exp 1+Real.sqrt (N/dimensionLog N)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hs := Real.sq_sqrt (show 0≤L*dimensionLog N/n by positivity)
  have he : n*originalBiasGamma L n N^2 =
      L*dimensionLog N * Real.log (Real.exp 1+Real.sqrt (N/dimensionLog N))^2 := by
    rw [originalBiasGamma, mul_pow, hs]
    field_simp
  rw [he]
  exact (le_mul_of_one_le_right hL hell).trans (le_mul_of_one_le_right
    (mul_nonneg hL (zero_le_one.trans hell)) (by nlinarith : 1≤Real.log
      (Real.exp 1+Real.sqrt (N/dimensionLog N))^2))

theorem source_energy_le_normalized_balance {S L n Q γ A : ℝ}
    (hS : 0≤S) (hQ : 0<Q) (hQL : Q≤A^2*L) (hgamma : L≤n*γ^2) :
    S ≤ A^2*(n*S*γ^2/Q) := by
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hQ).mpr
  have h1 := mul_le_mul_of_nonneg_left hQL hS
  have h2 := mul_le_mul_of_nonneg_left hgamma (mul_nonneg (sq_nonneg A) hS)
  nlinarith

variable [TopologicalSpace.SeparableSpace H]

/-- The actual average leverage is bounded by any genuine a.e. leverage bound. -/
theorem featureEffectiveDimension_le_leverageBound (k : X → H) (hk : MemLp k 2 μ)
    {lam L : ℝ} (hlam : 0<lam)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y≤L) :
    featureEffectiveDimension k hk lam≤L := by
  rw [← integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam]
  exact (integral_mono_ae (integrable_normalizedLeverage k hk lam) (integrable_const L) hL).trans_eq
    (by simp)

/-- Actual filter dimension versus the common maximal leverage, derived
without a separate dimension or retention certificate. -/
theorem featureFilterDimension_le_leverageBound (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A L : ℝ} (hlam : 0<lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y≤L) :
    featureFilterDimension k hk φ≤A^2*L :=
  (featureFilterDimension_le_effectiveDimension k hk φ hlam hM hf h).trans
    (mul_le_mul_of_nonneg_left (featureEffectiveDimension_le_leverageBound k hk hlam hL) (sq_nonneg A))

/-- The original normalized source balance controls the actual source energy,
with a constant depending only on the original filter constant. -/
theorem featureSequenceSourceEnergy_le_original_balance (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A L n α : ℝ} (hlam : 0<lam) (hn : 0<n)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y≤L)
    (hQ : 0<featureFilterDimension k hk φ) (f : Lp ℝ 2 μ) :
    featureSequenceSourceEnergy k hk lam α f ≤ A^2*(n*featureSequenceSourceEnergy k hk lam α f*
      originalBiasGamma L n (featureEffectiveDimension k hk lam)^2/featureFilterDimension k hk φ) := by
  exact source_energy_le_normalized_balance (featureSequenceSourceEnergy_nonneg k hk hlam f) hQ
    (featureFilterDimension_le_leverageBound k hk φ hlam hM hf h hL)
    (originalBiasGamma_sq_mul_sample_ge_leverage
      (feature_sq_bound_nonneg (bernsteinFeature k hk lam) hL) hn
      (featureEffectiveDimension_nonneg k hk lam hlam))

/-- The target norm in the actual bad-risk envelope is controlled by the
original normalized source balance and H. No uniform target-norm premise
or noise upper bound is introduced. -/
theorem feature_target_norm_sq_le_balance_polynomial (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) (κ : ℝ) {lam ρ A L n α : ℝ} (hlam : 0<lam) (hn : 0<n)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤κ^2)
    (hf : ResidualFilter.SpectralFilter (κ^2) φ) (h : ResidualFilter.Contract lam (κ^2) ρ A φ)
    (hα : 0≤α) (hα1 : α≤1)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y≤L)
    (hQ : 0<featureFilterDimension k hk φ) (hQn : featureFilterDimension k hk φ≤n)
    (f : Lp ℝ 2 μ)
    (hsupport : f∈(predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure) :
    ‖f‖^2 ≤ A^2*(1+κ^2)*(1+n/(lam*featureFilterDimension k hk φ))*
      (n*featureSequenceSourceEnergy k hk lam α f*
        originalBiasGamma L n (featureEffectiveDimension k hk lam)^2/featureFilterDimension k hk φ) := by
  let Q := featureFilterDimension k hk φ
  let S := featureSequenceSourceEnergy k hk lam α f
  let ζ := n*S*originalBiasGamma L n (featureEffectiveDimension k hk lam)^2/Q
  let H := n/(lam*Q)
  have hSn : 0≤S := featureSequenceSourceEnergy_nonneg k hk hlam f
  have hζ : 0≤ζ := by dsimp only [ζ]; positivity
  have hH : 0≤H := by dsimp only [H]; positivity
  have hS : S≤A^2*ζ := featureSequenceSourceEnergy_le_original_balance k hk φ hlam hn hM hf h hL hQ f
  have hinv : lam⁻¹≤H := regularization_inv_le_expectation_H hn hlam hQ hQn
  have hbase : 1+κ^2/lam≤1+κ^2*H := by
    have hh : κ^2/lam≤κ^2*H := by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (sq_nonneg κ)
    linarith
  calc
    _ ≤ (1+κ^2/lam)*S := norm_sq_le_linear_source_energy k hk hlam hα hα1 hM f hsupport
    _ ≤ (1+κ^2*H)*(A^2*ζ) := mul_le_mul hbase hS hSn (by positivity)
    _ ≤ A^2*(1+κ^2)*(1+H)*ζ := by
      have hb : 1+κ^2*H≤(1+κ^2)*(1+H) := by nlinarith [sq_nonneg κ]
      calc
        _ ≤ ((1+κ^2)*(1+H))*(A^2*ζ) :=
          mul_le_mul_of_nonneg_right hb (mul_nonneg (sq_nonneg A) hζ)
        _ = _ := by ring

end
end KernelSeq
