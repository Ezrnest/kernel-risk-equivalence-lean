import KernelSeq.ExpectationGoodBias
import KernelSeq.ExpectationBiasScales

/-!
# Actual good-event bias expectation under the two original scales

All stochastic moments and localized estimates are supplied internally by
the actual covariance, RHS and mixed-endpoint theorems. The population bias
may vanish, and the prediction L2 space need not be separable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

variable {ι H X Ω J : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P] {l : Filter J} [NeBot l]

/-- The manuscript's actual good-design bias L1 conclusion, from the
original variance compatibility and target source balance. No analytic,
interaction, moment, or desired-error-limit certificate is an input. -/
theorem actual_good_bias_relative_L1_of_original_scales (b : HilbertBasis ι ℝ H)
    (n : J → ℕ) (hn : ∀ i, 0<n i) (x : (i:J) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0≤κ) (hkb : ∀ y, ‖k y‖≤κ)
    (lam : J → ℝ) (hlam : ∀ i, 0<lam i) (φ : J → ℝ → ℝ)
    {ρ A α : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤κ^2)
    (hMX : ∀ i ω, ‖empiricalCovariance (fun j => k (x i j ω))‖≤κ^2)
    (hf : ∀ i, ResidualFilter.SpectralFilter (κ^2) (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) (κ^2) ρ A (φ i))
    (hα0 : 0<α) (hα1 : α≤1) (hαρ : α/2≤ρ) (f : J → Lp ℝ 2 μ)
    (hsupport : ∀ i, f i ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure)
    (σ : ℝ) (hσ : 0<σ) (L : J → ℝ)
    (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y≤L i)
    (hQ : ∀ᶠ i in l, 0<featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i*dimensionLog (featureEffectiveDimension k hk (lam i))/(n i:ℝ))) l (𝓝 0))
    (hsource : Tendsto (fun i => (n i:ℝ)*featureSequenceSourceEnergy k hk (lam i) α (f i)*
      originalBiasGamma (L i) (n i:ℝ) (featureEffectiveDimension k hk (lam i))^2 /
        featureFilterDimension k hk (φ i)) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω in {ω | actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)≤1/4},
      |actualEmpiricalBiasEnergy k hk (φ i) (hlam i) (fun j => x i j ω) (hMX i ω) (h i) (f i)-
          ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖^2| /
        (‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖^2+
          σ^2/(n i:ℝ)*featureFilterDimension k hk (φ i)) ∂P) l (𝓝 0) := by
  let C := expectationBiasInteractionConstant α ρ A
  let Cd := 768*Real.exp 1
  let Ce := mixedEndpointMomentConstant
  let Q := fun i => featureFilterDimension k hk (φ i)
  let N := fun i => featureEffectiveDimension k hk (lam i)
  let S := fun i => featureSequenceSourceEnergy k hk (lam i) α (f i)
  let γ := fun i => originalBiasGamma (L i) (n i:ℝ) (N i)
  let v := fun i => L i*dimensionLog (N i)/(n i:ℝ)
  let ζ := fun i => (n i:ℝ)*S i*γ i^2/Q i
  let τ := fun i => actualOriginalBiasCutoff k hk (lam i) (φ i) α (f i) (L i) (n i) A
  let V := fun i => σ^2/(n i:ℝ)*Q i
  let U := fun i ω => actualBiasRHSAmplitude k hk (φ i) (hlam i) hM (hf i) (h i) (f i) (fun j => x i j ω)
  let δ := fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)
  let E := fun i ω => actualMixedEndpointEnvelope b k hk (lam i) (fun j => x i j ω)
  let W := fun i => ‖actualBiasWeight k hk (φ i) (hlam i) hα0.le hM (hf i) (f i)‖
  let u := fun i ω => U i ω+C*(τ i+δ i ω/τ i)
  let c := fun i ω => C*E i ω/τ i*W i
  let U₂ := fun i => ∫ ω, u i ω^2 ∂P
  let C₂ := fun i => ∫ ω, (c i ω/Real.sqrt (V i))^2 ∂P
  obtain ⟨hτ, hτ0, hLn, hvτ, hζτ⟩ := original_expectation_bias_cutoff_limits
    n hn k hk lam hlam hM φ hf h f L hL hQ hcompat hsource
  have hδmoment := integral_actualCovarianceDeviation_sq_le_original_scale_eventually
    b n hn x hlaw hind k hk lam hlam φ hM hf h L hL hQ hcompat
  have hEmoment := integral_actualMixedEndpointEnvelope_sq_le_original_scale_eventually
    b n hn x hlaw hind k hk lam hlam φ hM hf h L hL hQ hcompat
  have hL0 (i : J) : 0≤L i := feature_sq_bound_nonneg (bernsteinFeature k hk (lam i)) (hL i)
  have hUbound : ∀ᶠ i in l, U₂ i ≤ 3*((2*A)^2*(L i/(n i:ℝ))+C^2*(τ i)^2+
      (C^2*Cd)*(v i/(τ i)^2)) := by
    filter_upwards [hδmoment] with i hi
    have hUm := memLp_actualBiasRHSAmplitude (hn i) (x i) (hlaw i) k hk (φ i) (hlam i) hM (hf i) (h i) (f i) (hL i)
    have hδm := memLp_actualCovarianceDeviation b (hn i) (x i) (hlaw i) k hk (lam i) (hL i)
    have ha := integral_bias_affine_coefficient_sq_le (P:=P) (by simp) hUm hδm C (τ i)
    have hR := integral_actualBiasRHSAmplitude_sq_le (hn i) (x i) (hlaw i)
      (fun _ _ hij => (hind i).indepFun hij) k hk (φ i) (hlam i) hM (hf i) (h i) (f i) (hL0 i) (hL i)
    refine ha.trans ?_
    have hd := mul_le_mul_of_nonneg_left hi (div_nonneg (sq_nonneg C) (sq_nonneg (τ i)))
    have hd' : C^2/(τ i)^2*(∫ ω, δ i ω^2 ∂P)≤C^2/(τ i)^2*(Cd*v i) := by
      simpa only [δ, Cd, v, N] using hd
    calc
      _ ≤ 3*((2*A)^2*(L i/(n i:ℝ))+C^2*(τ i)^2+C^2/(τ i)^2*(Cd*v i)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤3)
        exact add_le_add (add_le_add hR le_rfl) hd'
      _ = _ := by ring
  have hUlim : Tendsto U₂ l (𝓝 0) := by
    have hu := (((hLn.const_mul ((2*A)^2)).add ((hτ0.pow 2).const_mul (C^2))).add
      (hvτ.const_mul (C^2*Cd))).const_mul 3
    simp only [mul_zero, zero_pow (by norm_num : 2≠0), add_zero] at hu
    exact squeeze_zero' (Eventually.of_forall fun i => integral_nonneg fun _ => sq_nonneg _)
      hUbound hu
  let K := C^2*(A+1)^2*Ce/σ^2
  have hCbound : ∀ᶠ i in l, C₂ i ≤ K*(ζ i/(τ i)^2) := by
    filter_upwards [hQ, hτ, hEmoment] with i hQi hτi hEi
    have hVi : 0<V i := mul_pos (div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr (hn i))) hQi
    have hW : W i^2 ≤ (A+1)^2*S i := populationResidualWeight_norm_sq_le_sequenceSource
      k hk (φ i) (hlam i) hα0.le hαρ hM (hf i) (h i) (hsupport i)
    have hSn : 0≤S i := featureSequenceSourceEnergy_nonneg k hk (hlam i) (f i)
    have hCe : 0≤Ce := mixedEndpointMomentConstant_nonneg
    have hcoef : 0≤C^2*W i^2/((τ i)^2*V i) := by positivity
    have hmain : C₂ i ≤ (C^2*W i^2/((τ i)^2*V i))*(Ce*γ i^2) := by
      rw [show C₂ i = (C^2*W i^2/((τ i)^2*V i))*(∫ ω, E i ω^2 ∂P) from
        integral_bias_source_coefficient_sq C (τ i) (W i) hVi]
      exact mul_le_mul_of_nonneg_left hEi hcoef
    refine hmain.trans ?_
    calc
      _ ≤ (C^2*((A+1)^2*S i)/((τ i)^2*V i))*(Ce*γ i^2) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hCe (sq_nonneg _))
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (sq_nonneg C))
          (mul_nonneg (sq_nonneg _) hVi.le)
      _ = K*(ζ i/(τ i)^2) := by
        dsimp only [K, ζ, V]
        field_simp [hσ.ne', (Nat.cast_pos.mpr (hn i)).ne', hQi.ne', hτi.1.ne']
  have hClim : Tendsto C₂ l (𝓝 0) := by
    have hc := hζτ.const_mul K
    simp only [mul_zero] at hc
    exact squeeze_zero' (Eventually.of_forall fun i => integral_nonneg fun _ => sq_nonneg _)
      hCbound hc
  have hEnv := ((((hUlim.sqrt.const_mul 2).add (hUlim.const_mul 2)).add hClim.sqrt).add
    (hClim.const_mul 2))
  simp only [Real.sqrt_zero, mul_zero, add_zero] at hEnv
  apply squeeze_zero' _ _ hEnv
  · filter_upwards [hQ] with i hi
    exact integral_nonneg fun _ => div_nonneg (abs_nonneg _)
      (add_nonneg (sq_nonneg _) (mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hi.le))
  · filter_upwards [hQ, hτ] with i hi hτi
    exact setIntegral_actual_good_bias_relative_le b (hn i) (x i) (hlaw i) k hk hks κ hκ hkb
      hM (hMX i) (φ i) (hlam i) (hf i) (h i) hα0 hα1 hαρ (f i) (hsupport i)
      σ hσ hi (hL i) (τ i) hτi

end
end KernelSeq
