import KernelSeq.OriginalBiasAsymptotics
import KernelSeq.ExpectationCovarianceScales

/-!
# The original deterministic cutoff scales for expectation bias transfer

The two manuscript scales give all square-moment normalization limits at the
actual fourth-root cutoff. No stochastic convergence, interaction estimate,
or extra source condition is an input to this deterministic step.
-/

open MeasureTheory Filter Topology

namespace KernelSeq
noncomputable section

variable {H X J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]
  {l : Filter J} [NeBot l]

theorem original_expectation_bias_cutoff_limits
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (k : X → H) (hk : MemLp k 2 μ)
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i) {M ρ A α : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : J → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i)) (f : J → Lp ℝ 2 μ)
    (L : J → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0))
    (hsource : Tendsto (fun i => (n i : ℝ) * featureSequenceSourceEnergy k hk (lam i) α (f i) *
      originalBiasGamma (L i) (n i : ℝ) (featureEffectiveDimension k hk (lam i)) ^ 2 /
        featureFilterDimension k hk (φ i)) l (𝓝 0)) :
    let v := fun i => L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ)
    let ζ := fun i => (n i : ℝ) * featureSequenceSourceEnergy k hk (lam i) α (f i) *
      originalBiasGamma (L i) (n i : ℝ) (featureEffectiveDimension k hk (lam i)) ^ 2 /
        featureFilterDimension k hk (φ i)
    let τ := fun i => actualOriginalBiasCutoff k hk (lam i) (φ i) α (f i) (L i) (n i) A
    (∀ᶠ i in l, τ i ∈ Set.Ioc (0 : ℝ) (originalBiasCutoffCap A)) ∧
      Tendsto τ l (𝓝 0) ∧ Tendsto (fun i => L i / (n i : ℝ)) l (𝓝 0) ∧
      Tendsto (fun i => v i / τ i ^ 2) l (𝓝 0) ∧
      Tendsto (fun i => ζ i / τ i ^ 2) l (𝓝 0) := by
  dsimp only
  let v := fun i => L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ)
  let ζ := fun i => (n i : ℝ) * featureSequenceSourceEnergy k hk (lam i) α (f i) *
    originalBiasGamma (L i) (n i : ℝ) (featureEffectiveDimension k hk (lam i)) ^ 2 /
      featureFilterDimension k hk (φ i)
  have hvn : ∀ᶠ i in l, 0 ≤ v i := Eventually.of_forall fun i => by
    have hi := feature_sq_bound_nonneg (bernsteinFeature k hk (lam i)) (hL i)
    exact div_nonneg (mul_nonneg hi (zero_le_one.trans
      (one_le_dimensionLog (featureEffectiveDimension_nonneg k hk (lam i) (hlam i)))))
      (Nat.cast_nonneg _)
  have hζn : ∀ᶠ i in l, 0 ≤ ζ i := by
    filter_upwards [hQ] with i hi
    exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (featureSequenceSourceEnergy_nonneg k hk (hlam i) (f i))) (sq_nonneg _)) hi.le
  have hv0 : Tendsto v l (𝓝 0) :=
    (feature_variance_compatibility_scale_limits k hk lam hlam φ hM hf h v hvn hQ hcompat).1
  have hspos : ∀ᶠ i in l, 0 < v i + ζ i := by
    filter_upwards [hQ, hζn] with i hi hζi
    have hLp := actual_leverage_bound_pos_of_filterDimension_pos k hk (lam i) (hlam i)
      (φ i) hM (hf i) (h i) (hL i) hi
    have hlog : 0 < dimensionLog (featureEffectiveDimension k hk (lam i)) :=
      zero_lt_one.trans_le (one_le_dimensionLog (featureEffectiveDimension_nonneg k hk (lam i) (hlam i)))
    have hvp : 0 < v i := div_pos (mul_pos hLp hlog)
      (Nat.cast_pos.mpr (hn i))
    exact add_pos_of_pos_of_nonneg hvp hζi
  obtain ⟨i₀, _⟩ := hQ.exists
  have hA : 0 ≤ A := (h i₀).constant_nonneg (hlam i₀) ((norm_nonneg _).trans hM)
  obtain ⟨hτp, hτ0, hvτ, hζτ⟩ := localizationCutoff_limits
    (originalBiasCutoffCap_pos hA) hv0 hsource hvn hζn hspos
  have hLn := (feature_variance_compatibility_expectation_covariance_limits
    n hn k hk lam hlam φ hM hf h L hL hQ hcompat).1
  refine ⟨?_, hτ0, hLn, hvτ, hζτ⟩
  filter_upwards [hτp] with i hi
  exact ⟨hi, min_le_left _ _⟩

end
end KernelSeq
