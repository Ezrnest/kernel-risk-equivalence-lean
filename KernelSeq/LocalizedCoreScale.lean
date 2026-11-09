import KernelSeq.AuxiliaryHMS
import KernelSeq.LocalizedScaleBridge
import KernelSeq.OriginalBiasAsymptotics

/-!
# Original-scale localized prediction from the finite analytic leaves

The actual dimensionless localized core is transported through the proved
regularization scaling and constructed supported polar isometry. The final
sampled RKHS theorem has no auxiliary-interaction, localized-core, Schur,
coefficient, basis, reconstruction, or polar certificate premise.

Only `FiniteLipschitzSchur` and `FiniteHMS`, the explicitly unproved universal
finite analytic leaves, remain external in addition to the original model and
filter hypotheses. The common constant is independent of λ, M, and τ.
-/

namespace KernelSeq

noncomputable section

universe uH uI uE uX
variable {H : Type uH} {I : Type uI}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- One common source-constant-only coefficient for all original scales,
compact spectral endpoints, and admissible localization cutoffs. -/
def localizedCoreConstant (CL CH α ρ A : ℝ) : ℝ :=
  localizedAssemblyConstant A (auxiliaryHMSConstant CL CH α ρ A)

theorem localizedCoreConstant_nonneg {CL CH α ρ A : ℝ} (hA : 0 ≤ A) :
    0 ≤ localizedCoreConstant CL CH α ρ A := localizedAssemblyConstant_nonneg hA

/-- Full actual original-scale embedded localization from the two named finite
analytic leaves. All changes of scale and the use of the same actual HS
columns at the two scales are proved identities. -/
theorem localized_original_core_from_finite_analytic {CL CH : ℝ}
    (hLip : FiniteLipschitzSchur.{uH, uH, uH, uH} CL)
    (hHMS : FiniteHMS.{uH, uH, uH, uH} CH) (b : HilbertBasis I ℝ H)
    (TX T : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hc : IsCompactOperator T)
    (hpX : TX.IsPositive) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α τ : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖T‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτA : τ ≤ 1 / (4 * (A + 1)))
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 4)
    (c : HilbertSchmidtColumns I H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation T TX hc hcX hp hpX lam) (z : H) :
    ‖(compactRegularizedSqrt T hc hp 0 * compactInteraction TX T hcX hc hpX hp φ hlam hMX hM hf h *
        compactRegularizedSqrt T hc hp 0) z‖ ≤
      localizedCoreConstant CL CH α ρ A * (τ + ‖realNormalizedPerturbation T TX hc hp lam‖ / τ) *
        ‖compactResidualOperator T hc hp φ hM hf z‖ +
      localizedCoreConstant CL CH α ρ A * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator T hc hp φ hlam hα0.le hM hf z‖ := by
  have hδd : lowBlockDeviation (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
      (dimensionlessCovariance_isCompact T hc lam) (dimensionlessCovariance_isPositive T hp hlam) ≤ 1 / 4 := by
    unfold lowBlockDeviation
    rw [realNormalizedPerturbation_dimensionless T TX hc hp hlam]
    exact hδ
  have hcKd : hilbertSchmidtOperator b c = manuscriptMixedPerturbation
      (dimensionlessCovariance T lam) (dimensionlessCovariance TX lam)
      (dimensionlessCovariance_isCompact T hc lam) (dimensionlessCovariance_isCompact TX hcX lam)
      (dimensionlessCovariance_isPositive T hp hlam) (dimensionlessCovariance_isPositive TX hpX hlam) 1 := by
    rw [manuscriptMixedPerturbation_dimensionless T TX hc hcX hp hpX hlam]
    exact hcK
  have hb := localized_interaction_of_finite_analytic hLip hHMS b
    (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
    (dimensionlessCovariance_isCompact TX hcX lam) (dimensionlessCovariance_isCompact T hc lam)
    (dimensionlessCovariance_isPositive TX hpX hlam) (dimensionlessCovariance_isPositive T hp hlam)
    (localizedDimensionlessProfile lam φ)
    (dimensionlessCovariance_norm_le TX hlam hMX) (dimensionlessCovariance_norm_le T hlam hM)
    (localizedDimensionless_spectralFilter hlam hf) (localizedDimensionless_contract hlam h)
    hα0 hα1 hαρ hτ hτ1 hτA hδd c hcKd z
  simpa only [localizedCoreConstant,
    embeddedInteraction_dimensionless TX T hcX hc hpX hp φ hlam hMX hM hf h,
    lowBlockDeviation, realNormalizedPerturbation_dimensionless T TX hc hp hlam,
    compactResidualOperator_dimensionless T hc hp φ hlam hM hf,
    compactResidualWeightOperator_dimensionless T hc hp φ hlam hα0.le hM hf] using hb

section Prediction

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The original-scale supported prediction localized core. Compactness of
`S S*`, the supported polar map, and all norm bridges are derived from the
actual compact covariance `S* S`. Neither Hilbert space needs be separable. -/
theorem localized_prediction_core_from_finite_analytic {CL CH : ℝ}
    (hLip : FiniteLipschitzSchur.{uH, uH, uH, uH} CL)
    (hHMS : FiniteHMS.{uH, uH, uH, uH} CH) (b : HilbertBasis I ℝ H)
    (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    (TX : H →L[ℝ] H) (hcX : IsCompactOperator TX) (hpX : TX.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A α τ : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M) (hM : ‖S.adjoint.comp S‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτA : τ ≤ 1 / (4 * (A + 1)))
    (hδ : ‖realNormalizedPerturbation (S.adjoint.comp S) TX hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam‖ ≤ 1 / 4)
    (c : HilbertSchmidtColumns I H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation (S.adjoint.comp S) TX hc hcX
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) hpX lam)
    (f : E) (hsupport : f ∈ (S.comp S.adjoint).range.topologicalClosure) :
    ‖S (compactInteraction TX (S.adjoint.comp S) hcX hc hpX
        (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h (S.adjoint f))‖ ≤
      localizedCoreConstant CL CH α ρ A *
        (τ + ‖realNormalizedPerturbation (S.adjoint.comp S) TX hc
          (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam‖ / τ) *
        ‖compactResidualOperator (S.comp S.adjoint)
          (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
          (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ
          ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf f‖ +
      localizedCoreConstant CL CH α ρ A * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator (S.comp S.adjoint)
          (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
          (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα0.le
          ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf f‖ := by
  have hfRange : f ∈ PredictionRange S := by
    simpa only [closure_range_self_comp_adjoint S] using hsupport
  let fs : PredictionRange S := ⟨f, hfRange⟩
  let G := compactInteraction TX (S.adjoint.comp S) hcX hc hpX
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h
  have hb := localized_original_core_from_finite_analytic hLip hHMS b TX (S.adjoint.comp S) hcX hc hpX
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h hα0 hα1 hαρ hτ hτ1 hτA
    hδ c hcK (supportedPolarIsometry S hc fs)
  simp only [mul_apply_eq_comp] at hb
  have hnorm := prediction_interaction_norm_eq S hc G fs
  have hres := prediction_residual_norm_eq S hc φ hM
    ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf fs
  have hweight := prediction_residualWeight_norm_eq S hc φ hlam hα0.le hM
    ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf fs
  rw [← hnorm, ← hres, ← hweight] at hb
  exact hb

end Prediction

section ActualFeature

open MeasureTheory

variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual RKHS localized interaction core in the exact cutoff and
coefficient format used by `actual_bias_transfer_from_original_scales` and
`actual_risk_ratio_from_original_scales`. The same constant works for all
λ, admissible τ, targets, and samples. Only the two named general finite
analytic propositions remain external; no project-specific core estimate is
an input. Actual mixed columns and reconstruction are supplied internally. -/
theorem actual_localized_interaction_from_finite_analytic {CL CH : ℝ}
    (hLip : FiniteLipschitzSchur.{uH, uH, uH, uH} CL)
    (hHMS : FiniteHMS.{uH, uH, uH, uH} CH) (b : HilbertBasis I ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A α : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    {n : ℕ} (x : Fin n → X) (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ)
    (τ : ℝ) (hτ : τ ∈ Set.Ioc (0 : ℝ) (originalBiasCutoffCap A))
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4)
    (f : Lp ℝ 2 μ) (hsupport : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure) :
    ‖actualInteractionPrediction k hk φ hlam hM x hMX hf h f‖ ≤
      localizedCoreConstant CL CH α ρ A * (τ + actualCovarianceDeviation k hk lam x / τ) *
        ‖populationSpectralResidual k hk φ hM hf f‖ +
      (localizedCoreConstant CL CH α ρ A * hsSchattenEndpoint b (manuscriptMixedColumns b k hk lam x) / τ) *
        ‖actualBiasWeight k hk φ hlam hα0.le hM hf f‖ := by
  have hτ1 : τ ≤ 1 := hτ.2.trans (min_le_left _ _)
  have hτA : τ ≤ 1 / (4 * (A + 1)) := hτ.2.trans (min_le_right _ _)
  have hb := localized_prediction_core_from_finite_analytic hLip hHMS b (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk) (empiricalCovariance (fun i => k (x i)))
    (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX hM hf h
    hα0 hα1 hαρ hτ.1 hτ1 hτA hδ (manuscriptMixedColumns b k hk lam x)
    (hilbertSchmidtOperator_manuscriptMixedColumns b k hk lam hlam x) f hsupport
  simpa only [actualInteractionPrediction, populationSpectralResidual, actualBiasWeight,
    actualCovarianceDeviation, covarianceRelativeDeviation, realNormalizedPerturbation,
    predictionCovariance, populationCovariance, mul_div_assoc] using hb

end ActualFeature

end
end KernelSeq
