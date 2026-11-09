import KernelSeq.UniformGoodMoments
import KernelSeq.ExpectationGoodBias

/-!
# Common-constant finite-row good-event bias bounds

The target norm is unrestricted. A common positive lower bound on noise is
enough: every stochastic moment is supplied by the actual iid feature model.
All constants below depend only on the common filter parameters and noise
lower bound, and not on the ambient spaces, laws, sample size or target.
-/

open MeasureTheory ProbabilityTheory

namespace KernelSeq
noncomputable section

def uniformBiasUMomentConstant (α ρ A : ℝ) : ℝ :=
  3 * ((2 * A) ^ 2 + expectationBiasInteractionConstant α ρ A ^ 2 +
    expectationBiasInteractionConstant α ρ A ^ 2 * uniformCovarianceMomentConstant)

def uniformBiasCMomentConstant (α ρ A σ₀ : ℝ) : ℝ :=
  expectationBiasInteractionConstant α ρ A ^ 2 * (A + 1) ^ 2 * mixedEndpointMomentConstant / σ₀ ^ 2

def uniformBiasRiskConstant (α ρ A σ₀ : ℝ) : ℝ :=
  2 * Real.sqrt (uniformBiasUMomentConstant α ρ A) + 2 * uniformBiasUMomentConstant α ρ A +
    Real.sqrt (uniformBiasCMomentConstant α ρ A σ₀) + 2 * uniformBiasCMomentConstant α ρ A σ₀

def uniformBiasErrorRate (t z : ℝ) : ℝ := Real.sqrt t + t + Real.sqrt z + z

/-- The exact source exponent selected in the original manuscript. -/
def uniformBiasSourceExponent (ρ : ℝ) : ℝ := min (2 * ρ) 1

theorem uniformBiasUMomentConstant_nonneg (α ρ A : ℝ) : 0 ≤ uniformBiasUMomentConstant α ρ A := by
  unfold uniformBiasUMomentConstant
  positivity [uniformCovarianceMomentConstant_nonneg]

theorem uniformBiasCMomentConstant_nonneg (α ρ A σ₀ : ℝ) : 0 ≤ uniformBiasCMomentConstant α ρ A σ₀ := by
  unfold uniformBiasCMomentConstant
  positivity [mixedEndpointMomentConstant_nonneg]

theorem uniformBiasRiskConstant_nonneg (α ρ A σ₀ : ℝ) : 0 ≤ uniformBiasRiskConstant α ρ A σ₀ := by
  unfold uniformBiasRiskConstant
  positivity [uniformBiasUMomentConstant_nonneg α ρ A, uniformBiasCMomentConstant_nonneg α ρ A σ₀]

private theorem weighted_three_le {a b c x y z : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    a * x + b * y + c * z ≤ (a + b + c) * (x + y + z) := by
  have h₁ := mul_le_mul_of_nonneg_right (show a ≤ a + b + c by linarith) hx
  have h₂ := mul_le_mul_of_nonneg_right (show b ≤ a + b + c by linarith) hy
  have h₃ := mul_le_mul_of_nonneg_right (show c ≤ a + b + c by linarith) hz
  nlinarith

private theorem bias_moment_envelope_le {U C t z : ℝ} (hU : 0 ≤ U) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (hz : 0 ≤ z) {u c : ℝ} (hu : u ≤ U * t) (hc : c ≤ C * z) :
    2 * Real.sqrt u + 2 * u + Real.sqrt c + 2 * c ≤
      (2 * Real.sqrt U + 2 * U + Real.sqrt C + 2 * C) * uniformBiasErrorRate t z := by
  have hsU : Real.sqrt u ≤ Real.sqrt U * Real.sqrt t := by
    simpa only [Real.sqrt_mul hU] using Real.sqrt_le_sqrt hu
  have hsC : Real.sqrt c ≤ Real.sqrt C * Real.sqrt z := by
    simpa only [Real.sqrt_mul hC] using Real.sqrt_le_sqrt hc
  have hsum₁ : 2 * Real.sqrt U ≤ 2 * Real.sqrt U + 2 * U + Real.sqrt C + 2 * C := by linarith [Real.sqrt_nonneg C]
  have hsum₂ : 2 * U ≤ 2 * Real.sqrt U + 2 * U + Real.sqrt C + 2 * C := by linarith [Real.sqrt_nonneg U, Real.sqrt_nonneg C]
  have hsum₃ : Real.sqrt C ≤ 2 * Real.sqrt U + 2 * U + Real.sqrt C + 2 * C := by linarith [Real.sqrt_nonneg U]
  have hsum₄ : 2 * C ≤ 2 * Real.sqrt U + 2 * U + Real.sqrt C + 2 * C := by linarith [Real.sqrt_nonneg U, Real.sqrt_nonneg C]
  have h₁ := mul_le_mul_of_nonneg_right hsum₁ (Real.sqrt_nonneg t)
  have h₂ := mul_le_mul_of_nonneg_right hsum₂ ht
  have h₃ := mul_le_mul_of_nonneg_right hsum₃ (Real.sqrt_nonneg z)
  have h₄ := mul_le_mul_of_nonneg_right hsum₄ hz
  unfold uniformBiasErrorRate
  nlinarith

variable {ι H X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- Actual finite-row bias comparison with common constants, at any valid
deterministic cutoff. Only a noise lower bound and a visible scalar intrinsic
smallness condition are added to the actual model assumptions. -/
theorem setIntegral_actual_good_bias_uniform_cutoff (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (hind : iIndepFun x P)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0 ≤ κ) (hkb : ∀ y, ‖k y‖ ≤ κ)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ κ ^ 2)
    (hMX : ∀ ω, ‖empiricalCovariance (fun j => k (x j ω))‖ ≤ κ ^ 2)
    (φ : ℝ → ℝ) {lam ρ A α : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ) (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ)
    (f : Lp ℝ 2 μ) (hsupport : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure)
    (σ σ₀ : ℝ) (hσ₀ : 0 < σ₀) (hσσ₀ : σ₀ ≤ σ) (hQ : 0 < featureFilterDimension k hk φ)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hsmall : Real.sqrt (L * dimensionLog (featureEffectiveDimension k hk lam) / (n : ℝ)) *
      intrinsicDimensionLog (featureEffectiveDimension k hk lam) (featureCovarianceRetention k hk lam) /
        dimensionLog (featureEffectiveDimension k hk lam) ≤ 1)
    (τ : ℝ) (hτ : τ ∈ Set.Ioc (0 : ℝ) (originalBiasCutoffCap A)) :
    let Q := featureFilterDimension k hk φ
    let N := featureEffectiveDimension k hk lam
    let v := L * dimensionLog N / (n : ℝ)
    let ζ := (n : ℝ) * featureSequenceSourceEnergy k hk lam α f * originalBiasGamma L (n : ℝ) N ^ 2 / Q
    let t := L / (n : ℝ) + τ ^ 2 + v / τ ^ 2
    (∫ ω in {ω | actualCovarianceDeviation k hk lam (fun j => x j ω) ≤ 1 / 4},
      |actualEmpiricalBiasEnergy k hk φ hlam (fun j => x j ω) (hMX ω) h f -
          ‖populationSpectralResidual k hk φ hM hf f‖ ^ 2| /
        (‖populationSpectralResidual k hk φ hM hf f‖ ^ 2 + σ ^ 2 / (n : ℝ) * Q) ∂P) ≤
      uniformBiasRiskConstant α ρ A σ₀ * uniformBiasErrorRate t (ζ / τ ^ 2) := by
  dsimp only
  let C := expectationBiasInteractionConstant α ρ A
  let Q := featureFilterDimension k hk φ
  let S := featureSequenceSourceEnergy k hk lam α f
  let N := featureEffectiveDimension k hk lam
  let v := L * dimensionLog N / (n : ℝ)
  let ζ := (n : ℝ) * S * originalBiasGamma L (n : ℝ) N ^ 2 / Q
  let t := L / (n : ℝ) + τ ^ 2 + v / τ ^ 2
  let V := σ ^ 2 / (n : ℝ) * Q
  let U := fun ω => actualBiasRHSAmplitude k hk φ hlam hM hf h f (fun j => x j ω)
  let δ := fun ω => actualCovarianceDeviation k hk lam (fun j => x j ω)
  let E := fun ω => actualMixedEndpointEnvelope b k hk lam (fun j => x j ω)
  let W := ‖actualBiasWeight k hk φ hlam hα0.le hM hf f‖
  let U₂ := ∫ ω, (U ω + C * (τ + δ ω / τ)) ^ 2 ∂P
  let C₂ := ∫ ω, ((C * E ω / τ * W) / Real.sqrt V) ^ 2 ∂P
  have hσ : 0 < σ := hσ₀.trans_le hσσ₀
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hLn : 0 ≤ L := feature_sq_bound_nonneg (bernsteinFeature k hk lam) hL
  have hv : 0 ≤ v := div_nonneg (mul_nonneg hLn (zero_le_one.trans
    (one_le_dimensionLog (featureEffectiveDimension_nonneg k hk lam hlam)))) hnR.le
  have hS : 0 ≤ S := featureSequenceSourceEnergy_nonneg k hk hlam f
  have hζ : 0 ≤ ζ := div_nonneg (mul_nonneg (mul_nonneg hnR.le hS) (sq_nonneg _)) hQ.le
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hd := integral_actualCovarianceDeviation_sq_le_uniform_row b hn x hlaw hind k hk φ hlam hM hf h hQ hL hsmall
  have hE := integral_actualMixedEndpointEnvelope_sq_le_uniform_row b hn x hlaw hind k hk φ hlam hM hf h hQ hL hsmall
  have hUm := memLp_actualBiasRHSAmplitude hn x hlaw k hk φ hlam hM hf h f hL
  have hδm := memLp_actualCovarianceDeviation b hn x hlaw k hk lam hL
  have hU : U₂ ≤ uniformBiasUMomentConstant α ρ A * t := by
    have ha := integral_bias_affine_coefficient_sq_le (P := P) (by simp) hUm hδm C τ
    have hR := integral_actualBiasRHSAmplitude_sq_le hn x hlaw (fun _ _ hij => hind.indepFun hij)
      k hk φ hlam hM hf h f hLn hL
    have hδ := mul_le_mul_of_nonneg_left hd (div_nonneg (sq_nonneg C) (sq_nonneg τ))
    have hδ' : C ^ 2 / τ ^ 2 * (∫ ω, δ ω ^ 2 ∂P) ≤
        C ^ 2 / τ ^ 2 * (uniformCovarianceMomentConstant * v) := by exact hδ
    refine ha.trans ((mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hR le_rfl) hδ') (by norm_num : (0 : ℝ) ≤ 3)).trans ?_)
    have hh := weighted_three_le (sq_nonneg (2 * A)) (sq_nonneg C)
      (mul_nonneg (sq_nonneg C) uniformCovarianceMomentConstant_nonneg)
      (div_nonneg hLn hnR.le) (sq_nonneg τ) (div_nonneg hv (sq_nonneg τ))
    dsimp only [uniformBiasUMomentConstant, t, C]
    convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 3) using 1 <;>
      dsimp only [C] <;> ring
  have hC : C₂ ≤ uniformBiasCMomentConstant α ρ A σ₀ * (ζ / τ ^ 2) := by
    have hV : 0 < V := mul_pos (div_pos (sq_pos_of_pos hσ) hnR) hQ
    have hW : W ^ 2 ≤ (A + 1) ^ 2 * S := populationResidualWeight_norm_sq_le_sequenceSource
      k hk φ hlam hα0.le hαρ hM hf h hsupport
    have hp : 0 ≤ C ^ 2 * W ^ 2 / (τ ^ 2 * V) := by positivity
    have he : C₂ = (C ^ 2 * W ^ 2 / (τ ^ 2 * V)) * (∫ ω, E ω ^ 2 ∂P) :=
      integral_bias_source_coefficient_sq C τ W hV
    rw [he]
    calc
      _ ≤ (C ^ 2 * W ^ 2 / (τ ^ 2 * V)) * (mixedEndpointMomentConstant * originalBiasGamma L (n : ℝ) N ^ 2) :=
        mul_le_mul_of_nonneg_left hE hp
      _ ≤ (C ^ 2 * ((A + 1) ^ 2 * S) / (τ ^ 2 * V)) *
          (mixedEndpointMomentConstant * originalBiasGamma L (n : ℝ) N ^ 2) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (sq_nonneg C)) (by positivity))
          (mul_nonneg mixedEndpointMomentConstant_nonneg (sq_nonneg _))
      _ = (C ^ 2 * (A + 1) ^ 2 * mixedEndpointMomentConstant / σ ^ 2) * (ζ / τ ^ 2) := by
        dsimp only [ζ, V]
        field_simp [hσ.ne', hnR.ne', hQ.ne', hτ.1.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity [mixedEndpointMomentConstant_nonneg])
          (sq_pos_of_pos hσ₀) (pow_le_pow_left₀ hσ₀.le hσσ₀ 2))
        (div_nonneg hζ (sq_nonneg τ))
  have hb := setIntegral_actual_good_bias_relative_le b hn x hlaw k hk hks κ hκ hkb hM hMX
    φ hlam hf h hα0 hα1 hαρ f hsupport σ hσ hQ hL τ hτ
  exact hb.trans (bias_moment_envelope_le (uniformBiasUMomentConstant_nonneg α ρ A)
    (uniformBiasCMomentConstant_nonneg α ρ A σ₀) ht (div_nonneg hζ (sq_nonneg τ)) hU hC)

/-- The complete finite-row bias bound at the manuscript's exact source
exponent and actual fourth-root cutoff. The noise may vary from row to row;
only the displayed positive common lower bound enters the constant. -/
theorem setIntegral_actual_good_bias_uniform_row (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (hind : iIndepFun x P)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0 ≤ κ) (hkb : ∀ y, ‖k y‖ ≤ κ)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ κ ^ 2)
    (hMX : ∀ ω, ‖empiricalCovariance (fun j => k (x j ω))‖ ≤ κ ^ 2)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ) (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ)
    (f : Lp ℝ 2 μ) (hsupport : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure)
    (σ σ₀ : ℝ) (hσ₀ : 0 < σ₀) (hσσ₀ : σ₀ ≤ σ) (hQ : 0 < featureFilterDimension k hk φ)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hsmall : Real.sqrt (L * dimensionLog (featureEffectiveDimension k hk lam) / (n : ℝ)) *
      intrinsicDimensionLog (featureEffectiveDimension k hk lam) (featureCovarianceRetention k hk lam) /
        dimensionLog (featureEffectiveDimension k hk lam) ≤ 1) :
    let Q := featureFilterDimension k hk φ
    let N := featureEffectiveDimension k hk lam
    let S := featureSequenceSourceEnergy k hk lam (uniformBiasSourceExponent ρ) f
    let v := L * dimensionLog N / (n : ℝ)
    let ζ := (n : ℝ) * S * originalBiasGamma L (n : ℝ) N ^ 2 / Q
    let τ := originalBiasCutoff A L (n : ℝ) N Q S
    (∫ ω in {ω | actualCovarianceDeviation k hk lam (fun j => x j ω) ≤ 1 / 4},
      |actualEmpiricalBiasEnergy k hk φ hlam (fun j => x j ω) (hMX ω) h f -
          ‖populationSpectralResidual k hk φ hM hf f‖ ^ 2| /
        (‖populationSpectralResidual k hk φ hM hf f‖ ^ 2 + σ ^ 2 / (n : ℝ) * Q) ∂P) ≤
      uniformBiasRiskConstant (uniformBiasSourceExponent ρ) ρ A σ₀ *
        uniformBiasErrorRate (L / (n : ℝ) + τ ^ 2 + v / τ ^ 2) (ζ / τ ^ 2) := by
  dsimp only
  let α := uniformBiasSourceExponent ρ
  let N := featureEffectiveDimension k hk lam
  let Q := featureFilterDimension k hk φ
  let S := featureSequenceSourceEnergy k hk lam α f
  let v := L * dimensionLog N / (n : ℝ)
  let ζ := (n : ℝ) * S * originalBiasGamma L (n : ℝ) N ^ 2 / Q
  let τ := originalBiasCutoff A L (n : ℝ) N Q S
  have hα0 : 0 < α := lt_min (by linarith [h.rho_pos]) zero_lt_one
  have hα1 : α ≤ 1 := min_le_right _ _
  have hαρ : α / 2 ≤ ρ := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    ((min_le_left (2 * ρ) 1).trans_eq (mul_comm 2 ρ))
  have hA : 0 ≤ A := h.constant_nonneg hlam (sq_nonneg κ)
  have hLp : 0 < L := actual_leverage_bound_pos_of_filterDimension_pos k hk lam hlam φ hM hf h hL hQ
  have hv : 0 < v := div_pos (mul_pos hLp (zero_lt_one.trans_le
    (one_le_dimensionLog (featureEffectiveDimension_nonneg k hk lam hlam)))) (Nat.cast_pos.mpr hn)
  have hζ : 0 ≤ ζ := div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (featureSequenceSourceEnergy_nonneg k hk hlam f)) (sq_nonneg _)) hQ.le
  have hτ : τ ∈ Set.Ioc (0 : ℝ) (originalBiasCutoffCap A) := by
    exact ⟨localizationCutoff_pos (originalBiasCutoffCap_pos hA) (add_pos_of_pos_of_nonneg hv hζ),
      min_le_left _ _⟩
  exact setIntegral_actual_good_bias_uniform_cutoff b hn x hlaw hind k hk hks κ hκ hkb hM hMX φ hlam hf h
    hα0 hα1 hαρ f hsupport σ σ₀ hσ₀ hσσ₀ hQ hL hsmall τ hτ

end
end KernelSeq
