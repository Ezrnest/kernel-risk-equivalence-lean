import KernelSeq.ExpectationBiasMeasurability
import KernelSeq.ExpectationBiasCoefficientMoments
import KernelSeq.ExpectationGoodRHS
import KernelSeq.ExpectationMixedEndpoint
import KernelSeq.LocalizedLipschitz
import KernelSeq.FixedSymbolFourierLpBound

/-!
# Actual bias comparison integrated on the covariance good event

The localized operator estimate is supplied by the locally proved dyadic
Lipschitz theorem. Actual measurable coefficients, their L2 membership and
the zero-residual RHS identity are derived internally. No operator estimate
or moment bound is assumed in the finite-model result below.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

def expectationBiasInteractionConstant (α ρ A : ℝ) : ℝ :=
  localizedLipschitzConstant (2*fixedSymbolFourierConstant) α ρ A

theorem expectationBiasInteractionConstant_nonneg {α ρ A : ℝ} (hA : 0≤A) :
    0≤expectationBiasInteractionConstant α ρ A := localizedLipschitzConstant_nonneg hA

variable {ι H X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The actual finite-sample good-event bias error is bounded by the two
actual coefficient moments. All measurability, L2 existence, zero-residual
handling and localized interaction bounds are proved inside this theorem. -/
theorem setIntegral_actual_good_bias_relative_le (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0<n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0≤κ) (hkb : ∀ y, ‖k y‖≤κ)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤κ^2)
    (hMX : ∀ ω, ‖empiricalCovariance (fun j => k (x j ω))‖≤κ^2)
    (φ : ℝ → ℝ) {lam ρ A α : ℝ} (hlam : 0<lam)
    (hf : ResidualFilter.SpectralFilter (κ^2) φ) (h : ResidualFilter.Contract lam (κ^2) ρ A φ)
    (hα0 : 0<α) (hα1 : α≤1) (hαρ : α/2≤ρ)
    (f : Lp ℝ 2 μ) (hsupport : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure)
    (σ : ℝ) (hσ : 0<σ) (hQ : 0<featureFilterDimension k hk φ)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y≤L)
    (τ : ℝ) (hτ : τ∈Set.Ioc (0:ℝ) (originalBiasCutoffCap A)) :
    let C := expectationBiasInteractionConstant α ρ A
    let V := σ^2/(n:ℝ)*featureFilterDimension k hk φ
    let U := fun ω => actualBiasRHSAmplitude k hk φ hlam hM hf h f (fun j => x j ω)
    let δ := fun ω => actualCovarianceDeviation k hk lam (fun j => x j ω)
    let E := fun ω => actualMixedEndpointEnvelope b k hk lam (fun j => x j ω)
    let W := ‖actualBiasWeight k hk φ hlam hα0.le hM hf f‖
    let U₂ := ∫ ω, (U ω+C*(τ+δ ω/τ))^2 ∂P
    let C₂ := ∫ ω, ((C*E ω/τ*W)/Real.sqrt V)^2 ∂P
    (∫ ω in {ω | δ ω≤1/4},
      |actualEmpiricalBiasEnergy k hk φ hlam (fun j => x j ω) (hMX ω) h f -
          ‖populationSpectralResidual k hk φ hM hf f‖^2| /
        (‖populationSpectralResidual k hk φ hM hf f‖^2+V) ∂P) ≤
      2*Real.sqrt U₂+2*U₂+Real.sqrt C₂+2*C₂ := by
  dsimp only
  let C := expectationBiasInteractionConstant α ρ A
  let V := σ^2/(n:ℝ)*featureFilterDimension k hk φ
  let U := fun ω => actualBiasRHSAmplitude k hk φ hlam hM hf h f (fun j => x j ω)
  let δ := fun ω => actualCovarianceDeviation k hk lam (fun j => x j ω)
  let E := fun ω => actualMixedEndpointEnvelope b k hk lam (fun j => x j ω)
  let W := ‖actualBiasWeight k hk φ hlam hα0.le hM hf f‖
  let u := fun ω => U ω+C*(τ+δ ω/τ)
  let c := fun ω => C*E ω/τ*W
  let r := populationSpectralResidual k hk φ hM hf f
  let e := fun ω => actualBiasError k hk φ hlam hM (fun j => x j ω) (hMX ω) h f
  let G := {ω | δ ω≤1/4}
  have hA : 0≤A := h.constant_nonneg hlam (sq_nonneg κ)
  have hC : 0≤C := expectationBiasInteractionConstant_nonneg hA
  have hV : 0<V := mul_pos (div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr hn)) hQ
  have hUm : MemLp U 2 P := memLp_actualBiasRHSAmplitude hn x hlaw k hk φ hlam hM hf h f hL
  have hδm : MemLp δ 2 P := memLp_actualCovarianceDeviation b hn x hlaw k hk lam hL
  have hEm : MemLp E 2 P := actualMixedEndpointEnvelope_memLp b hn x hlaw k hk lam hlam hL
  have hum : MemLp u 2 P := memLp_bias_affine_coefficient hUm hδm C τ
  have hcm : MemLp c 2 P := by
    simpa only [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hEm.const_mul (C/τ*W)
  have hzm : MemLp (fun ω => c ω/Real.sqrt V) 2 P := by
    simpa only [div_eq_mul_inv] using hcm.mul_const (Real.sqrt V)⁻¹
  have he : AEStronglyMeasurable e P := aestronglyMeasurable_actualBiasError
    hn x hlaw k hk hks κ hκ hkb hM hMX φ hlam hf h f
  have hδs : StronglyMeasurable δ := by
    let R := featureRegularizedInvSqrt μ k hk lam
    let T := populationCovariance (featureEmbedding μ k hk)
    have ht := stronglyMeasurable_empiricalCovariance (fun j ω => k (x j ω))
      (fun j => hks.comp_measurable (hlaw j).measurable)
    change StronglyMeasurable (fun ω => ‖R*(empiricalCovariance (fun j => k (x j ω))-T)*R‖)
    exact ((stronglyMeasurable_const.mul (ht.sub stronglyMeasurable_const)).mul stronglyMeasurable_const).norm
  have hG : MeasurableSet G := measurableSet_le hδs.measurable measurable_const
  have hzero : ∀ᵐ ω ∂P, ‖r‖=0 →
      rhsFluctuation k hk f (populationSpectralSolution k hk φ hlam hM h f) (fun j => x j ω)=0 := by
    by_cases hr : ‖r‖=0
    · have hz := actual_spectral_rhs_zero_ae_of_residual_zero x hlaw k hk φ hlam hM hf h f (norm_eq_zero.mp hr)
      filter_upwards [hz] with ω hω _
      exact hω
    · exact Eventually.of_forall fun _ hh => (hr hh).elim
  have hun (ω : Ω) : 0≤u ω := by
    exact add_nonneg (actualBiasRHSAmplitude_nonneg k hk φ hlam hM hf h f _)
      (mul_nonneg hC (add_nonneg hτ.1.le (div_nonneg (norm_nonneg _) hτ.1.le)))
  have hcn (ω : Ω) : 0≤c ω :=
    mul_nonneg (div_nonneg (mul_nonneg hC (actualMixedEndpointEnvelope_nonneg b k hk lam _)) hτ.1.le) (norm_nonneg _)
  have herr : ∀ᵐ ω ∂P.restrict G, ‖e ω‖≤u ω*‖r‖+c ω := by
    rw [ae_restrict_iff' hG]
    filter_upwards [hzero] with ω hz hω
    have hδ : actualCovarianceDeviation k hk lam (fun j => x j ω)≤1/4 := hω
    have hi := actual_localized_interaction_from_lipschitz finiteDyadicLipschitzSchur_proved
      b k hk φ hlam hM (fun j => x j ω) (hMX ω) hf h hα0 hα1 hαρ τ hτ hδ f hsupport
    have hep := manuscriptMixedEndpoint_le_actualMixedEndpointEnvelope b k hk lam hlam
      (fun j => x j ω) hδ
    have hb : ‖actualInteractionPrediction k hk φ hlam hM (fun j => x j ω) (hMX ω) hf h f‖ ≤
        (C*(τ+δ ω/τ))*‖r‖+(C*E ω/τ)*W := by
      refine hi.trans ?_
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hep hC) hτ.1.le) (norm_nonneg _)
    have hε : 0≤C*(τ+δ ω/τ) := by
      exact mul_nonneg hC (add_nonneg hτ.1.le (div_nonneg (norm_nonneg _) hτ.1.le))
    have hβ : 0≤C*E ω/τ := div_nonneg
      (mul_nonneg hC (actualMixedEndpointEnvelope_nonneg b k hk lam _)) hτ.1.le
    simpa only [u, c, abs_of_nonneg hε, abs_of_nonneg hβ] using
      actualBiasError_norm_le_of_interaction k hk φ hlam hα0.le hM (fun j => x j ω)
        (hMX ω) hf h f (C*(τ+δ ω/τ)) (C*E ω/τ) hδ hz hb
  have hb := setIntegral_bias_relative_risk_le G r e (he.mono_measure Measure.restrict_le_self) hV
    (hum.restrict G) (hcm.restrict G) (Eventually.of_forall hun) (Eventually.of_forall hcn) herr
  have hUbound : (∫ ω in G, u ω^2 ∂P)≤∫ ω, u ω^2 ∂P :=
    integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ => sq_nonneg _) hum.integrable_sq
  have hCbound : (∫ ω in G, (c ω/Real.sqrt V)^2 ∂P)≤∫ ω, (c ω/Real.sqrt V)^2 ∂P :=
    integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ => sq_nonneg _) hzm.integrable_sq
  have hmono : 2*Real.sqrt (∫ ω in G, u ω^2 ∂P)+2*(∫ ω in G, u ω^2 ∂P)+
      Real.sqrt (∫ ω in G, (c ω/Real.sqrt V)^2 ∂P)+2*(∫ ω in G, (c ω/Real.sqrt V)^2 ∂P) ≤
      2*Real.sqrt (∫ ω, u ω^2 ∂P)+2*(∫ ω, u ω^2 ∂P)+
        Real.sqrt (∫ ω, (c ω/Real.sqrt V)^2 ∂P)+2*(∫ ω, (c ω/Real.sqrt V)^2 ∂P) := by
    gcongr
  apply (le_trans ?_ (hb.trans hmono))
  apply le_of_eq
  apply setIntegral_congr_fun hG
  intro ω _
  dsimp only [r, e, V]
  rw [actual_bias_energy_eq k hk φ hlam hM (fun j => x j ω) (hMX ω) hf h f]

end
end KernelSeq
