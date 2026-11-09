import KernelSeq.UniformSource
import KernelSeq.UniformBadNormalization
import KernelSeq.ExpectationBadAsymptotics

/-!
# Actual bad-design risk with common target-family constants

This is a quantitative finite-model theorem. The actual leave-one-out events,
their independent integrals and their concentration bounds are supplied
internally. The target norm is controlled by the original source balance.
Only a common positive noise lower bound appears in the final constant.
The finite smallness conditions are those already derived from original
variance compatibility, not new asymptotic model hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace KernelSeq
noncomputable section

variable {H X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- Actual common bad-risk bound, uniform in the target, design law, kernel,
noise level and ambient spaces once κ,A and the positive noise lower bound
are fixed. No target-norm, noise upper bound, concentration or leave-one-out
certificate is assumed. -/
theorem rkhs_uniform_bad_risk_quantitative
    (hK : Measurable (fun p : X×X => rkhsKernel (X:=X) (H:=H) p.1 p.2))
    (κ : ℝ) (hκ : 0≤κ) (hdiag : ∀ y, rkhsKernel (X:=X) (H:=H) y y≤κ^2)
    {n : ℕ} (hn : 0<n) (Z : Fin n → Ω → X×ℝ) (hZ : ∀ j, Measurable (Z j))
    (hlaw : ∀ j, MeasurePreserving (fun ω => (Z j ω).1) P μ) (hind : iIndepFun Z P)
    (f : Lp ℝ 2 μ) (σ s0 : ℝ) (hs0 : 0<s0) (hσ : s0≤σ)
    (hmean : ∀ j, P[observationNoise (Z j) (lpRepresentative f) |
      observationDesignSigma (Z j)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ j, P[(fun ω => observationNoise (Z j) (lpRepresentative f) ω^2) |
      observationDesignSigma (Z j)] =ᵐ[P] (fun _ => σ^2))
    (φ : ℝ → ℝ) {lam ρ A α : ℝ} (hlam : 0<lam)
    (hf : ResidualFilter.SpectralFilter (κ^2) φ) (h : ResidualFilter.Contract lam (κ^2) ρ A φ)
    (hα : 0≤α) (hα1 : α≤1) :
    let k := rkhsFeature (X:=X) (H:=H)
    let hk := rkhsFeature_memLp μ hK κ hκ hdiag
    let L := featureLeverageEssentialSup k hk lam
    let Q := featureFilterDimension k hk φ
    let Hscale := (n:ℝ)/(lam*Q)
    let ζ := (n:ℝ)*featureSequenceSourceEnergy k hk lam α f*
      originalBiasGamma L (n:ℝ) (featureEffectiveDimension k hk lam)^2/Q
    f∈(predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure →
    0<Q → Q≤(n:ℝ) → (L+1)/(n:ℝ)≤1/8 →
    L*intrinsicDimensionLog (featureEffectiveDimension k hk lam)
      (featureCovarianceRetention k hk lam)/(n:ℝ)≤1/65536 →
    (∫ ω in {ω | 1/4<actualCovarianceDeviation k hk lam (fun j => (Z j ω).1)},
      rkhsConditionalPredictionRisk (P:=P) hK κ hκ hdiag hn Z f φ hlam h ω ∂P) /
        sequenceBenchmark k hk φ f σ n ≤
      uniformBadRiskConstant A κ s0*(1+Hscale)^3*(1+ζ)*Real.exp (-(n:ℝ)/(65536*L)) := by
  dsimp only
  intro hsupport hQ hQn hsmall hsmallInt
  let k := rkhsFeature (X:=X) (H:=H)
  let hk := rkhsFeature_memLp μ hK κ hκ hdiag
  let L := featureLeverageEssentialSup k hk lam
  let Q := featureFilterDimension k hk φ
  let x := fun j ω => (Z j ω).1
  let B := {ω | 1/4<actualCovarianceDeviation k hk lam (fun j => x j ω)}
  let Bi := fun j => leaveOneOutCovarianceBad k hk lam j x
  let p := Real.exp (-(n:ℝ)/(65536*L))
  let D := sequenceBenchmark k hk φ f σ n
  let S := featureSequenceSourceEnergy k hk lam α f
  let ζ := (n:ℝ)*S*originalBiasGamma L (n:ℝ) (featureEffectiveDimension k hk lam)^2/Q
  have hnR : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hσ0 : 0<σ := hs0.trans_le hσ
  have hp : 0≤p := (Real.exp_pos _).le
  have hM := rkhs_population_covariance_bound (μ:=μ) hK κ hκ hdiag
  have hκsq : ∀ᵐ y ∂μ, ‖k y‖^2≤κ^2 := Eventually.of_forall fun y =>
    pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ hκ hdiag y) 2
  have hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y≤L :=
    normalizedLeverage_ae_le_essentialSup k hk hlam hκsq
  have hxind : iIndepFun x P := hind.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  have hr : 0<featureCovarianceRetention k hk lam :=
    featureCovarianceRetention_pos_of_filterDimension_pos k hk φ hlam hM hf h hQ
  have hSn : 0≤S := featureSequenceSourceEnergy_nonneg k hk hlam f
  have hζ : 0≤ζ := by dsimp only [ζ]; positivity
  have hPb : P.real B≤8*p := by
    have ht := actual_bad_design_exponential_tail k hk hlam hn x hlaw hxind hL hr hsmallInt
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ht).trans_eq (ENNReal.toReal_ofReal (by positivity))
  have hPbi (j : Fin n) : P.real (Bi j)≤8*p := by
    have ht := leaveOneOutCovarianceBad_exponential_tail k hk hlam hn j x hlaw hxind hL hr hsmallInt
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ht).trans_eq (ENNReal.toReal_ofReal (by positivity))
  have hbad := integral_rkhs_conditional_risk_bad_le hK κ hκ hdiag hn Z hZ hlaw f σ hσ0 hind
    hmean hsecond φ hlam hf h B Bi
    (fun j => measurableSet_otherPairs_leaveOneOutCovarianceBad k hk
      (rkhsFeature_stronglyMeasurable hK) lam j Z)
    (fun j => actual_bad_design_subset_leaveOneOut_ae k hk hlam hn j x hlaw hL hsmall) hPb hPbi
  have htarget := feature_target_norm_sq_le_balance_polynomial k hk φ κ hlam hnR hM hf h hα hα1
    hL hQ hQn f hsupport
  have hsquare : lam^2*Q≤(A*κ^2)^2 := by
    have hh := lambda_sq_mul_featureFilterDimension_le_sq_bound k hk φ κ hκsq hlam hM hf h
    convert hh using 1
    ring
  have hD : σ^2/(n:ℝ)*Q≤D := by
    dsimp only [D]
    rw [sequenceBenchmark_eq_population k hk φ hM hf hsupport σ n]
    exact le_add_of_nonneg_left (sq_nonneg _)
  exact uniform_normalize_bad_risk_envelope_le hn1 hlam hQ hQn hs0 hσ (sq_nonneg ‖f‖)
    hp hζ htarget hsquare hD hbad

end
end KernelSeq
