import KernelSeq.ActualBiasTransfer

/-!
# Actual RHS coefficient second moments for expectation transfer

The amplitude used by the common bias-transfer proof has a genuine second
moment bounded by `4 A² L/n`. The residual-normalization identity is proved
using the actual population spectral solution. In particular, a zero residual
does not require a positive lower bound or a separate integrability premise.
-/

open MeasureTheory ProbabilityTheory

namespace KernelSeq
noncomputable section

variable {X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

local instance expectationRHSMeasurableSpace : MeasurableSpace H := borel H
local instance expectationRHSBorelSpace : BorelSpace H := ⟨rfl⟩

/-- The actual RHS error coefficient is L² from the real sample laws and
bounded normalized leverage, without any assumption on the residual norm. -/
theorem memLp_actualBiasRHSAmplitude {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    MemLp (fun ω => actualBiasRHSAmplitude k hk φ hlam hM hf h f (fun i => x i ω)) 2 P := by
  have hz := memLp_rhsFluctuation hn x hlaw k hk f
    (populationSpectralSolution k hk φ hlam hM h f) (featureRegularizedInvSqrt μ k hk lam) hL
  simpa only [actualBiasRHSAmplitude, normalizedRHS, Pi.smul_apply] using
    ((hz.const_smul ‖populationSpectralResidual k hk φ hM hf f‖⁻¹).norm.const_mul (2 * A))

/-- The exact finite-sample second-moment bound for the actual normalized
RHS coefficient. It is valid when the population spectral residual is zero. -/
theorem integral_actualBiasRHSAmplitude_sq_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hind : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) {L : ℝ} (hLn : 0 ≤ L)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    (∫ ω, actualBiasRHSAmplitude k hk φ hlam hM hf h f (fun i => x i ω) ^ 2 ∂P) ≤
      (2 * A) ^ 2 * (L / (n : ℝ)) := by
  have hz := integral_scaled_rhsFluctuation_sq_le hn x hlaw hind k hk f
    (populationSpectralSolution k hk φ hlam hM h f) (featureRegularizedInvSqrt μ k hk lam) hLn hL
  rw [populationSpectralSolution_residual k hk φ hlam hM hf h f] at hz
  simp only [actualBiasRHSAmplitude, normalizedRHS, mul_pow]
  rw [integral_const_mul]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_left hz (sq_nonneg (2 * A))

end
end KernelSeq
