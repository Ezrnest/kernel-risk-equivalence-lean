import KernelSeq.CompactInteractionLipschitz
import KernelSeq.AuxiliaryHMS
import KernelSeq.LocalizedScaleBridge
import KernelSeq.OriginalBiasAsymptotics
import KernelSeq.DyadicSchattenEndpoint

/-!
# Actual localized prediction with an explicit dyadic Lipschitz input

The genuine chi step integral and the proved dyadic triangular estimates
remove the general HMS leaf. The auxiliary interaction is optimized over
dyadic exponents, which costs only the proved fixed factor two at the original
Schatten endpoint. Actual four-block assembly, scale transport and the
supported polar isometry then give the original sampled RKHS bound.

`FiniteDyadicLipschitzSchur` is retained as an explicit modular input;
`finiteDyadicLipschitzSchur_proved` in `FixedSymbolFourierLpBound` supplies
its actual constructor. No auxiliary-interaction, localized-core,
reconstruction or polar certificate is a premise. Constants
depend only on the displayed original filter parameters and the finite
Lipschitz constant, independently of M, lambda, the sample and the cutoff.
-/

namespace KernelSeq
noncomputable section
attribute [local instance] Classical.propDecidable

universe uH uI uE uX
variable {H : Type uH} {I : Type uI}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The fixed factor two is the genuine dyadic-to-original endpoint cost. -/
def auxiliaryLipschitzConstant (CL α ρ A : ℝ) : ℝ :=
  2 * Real.sqrt 2 * |lipschitzInteractionConstant CL α ρ (ResidualFilter.auxiliaryConstant ρ A)| *
    (1 + A * (13 + 4 * ρ))

theorem auxiliaryLipschitzConstant_nonneg {CL α ρ A : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) :
    0 ≤ auxiliaryLipschitzConstant CL α ρ A := by
  unfold auxiliaryLipschitzConstant
  positivity

/-- A single original-parameter constant works at every regularization scale
and cutoff. -/
def localizedLipschitzConstant (CL α ρ A : ℝ) : ℝ :=
  localizedAssemblyConstant A (auxiliaryLipschitzConstant CL α ρ A)

theorem localizedLipschitzConstant_nonneg {CL α ρ A : ℝ} (hA : 0 ≤ A) :
    0 ≤ localizedLipschitzConstant CL α ρ A := localizedAssemblyConstant_nonneg hA

set_option maxHeartbeats 800000 in
/-- Actual high-space auxiliary interaction, using the original filter's
proved inverse-profile bound and the actual dyadic backend. -/
theorem auxiliary_embedded_endpoint_from_lipschitz {CL : ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uH, uH, uH, uH} CL) (b : HilbertBasis I ℝ H)
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4)
    (c : HilbertSchmidtColumns I H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation V U hcV hcU hpV hpU 1) (z : H) :
    ‖(compactRegularizedSqrt V hcV hpV 0 *
        compactInteraction U V hcU hcV hpU hpV (ResidualFilter.auxiliaryFilter 1 τ φ)
          (by norm_num) hMU hMV hf.auxiliary (h.auxiliary_contract (by norm_num) hτ hτ1) *
        compactRegularizedSqrt V hcV hpV 0 * (1 - lowBlockProjection V hcV hpV τ)) z‖ ≤
      auxiliaryLipschitzConstant CL α ρ A * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α) (by norm_num) hα0.le hMV hf
          ((1 - lowBlockProjection V hcV hpV τ) z)‖ := by
  let R := 1 - lowBlockProjection V hcV hpV τ
  let W := ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α) (by norm_num) hα0.le hMV hf (R z)‖
  let D := lipschitzInteractionConstant CL α ρ (ResidualFilter.auxiliaryConstant ρ A)
  let L := A * (13 + 4 * ρ)
  let C := Real.sqrt 2 * |D| * (1 + L)
  have hA : 0 ≤ A := h.constant_nonneg (by norm_num) ((norm_nonneg V).trans hMV)
  have hρ : 0 ≤ ρ := h.rho_pos.le
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hW : 0 ≤ W := norm_nonneg _
  have hratio : 1 + L / τ ≤ (1 + L) / τ := by
    apply (le_div_iff₀ hτ).mpr
    rw [add_mul, div_mul_cancel₀ L hτ.ne', one_mul]
    linarith
  have hAll : ∀ m : ℕ,
      ‖(compactRegularizedSqrt V hcV hpV 0 *
          compactInteraction U V hcU hcV hpU hpV (ResidualFilter.auxiliaryFilter 1 τ φ)
            (by norm_num) hMU hMV hf.auxiliary (h.auxiliary_contract (by norm_num) hτ hτ1) *
          compactRegularizedSqrt V hcV hpV 0) (R z)‖ ≤
        (C / τ * W) * (dyadicSchattenExponent m * hsSchattenNorm b c (dyadicSchattenExponent m)) := by
    intro m
    have hb := compact_embedded_interaction_bound_from_lipschitz
      (lam := 1) (M := M) (ρ := ρ) (A := ResidualFilter.auxiliaryConstant ρ A)
      (α := α) (BF := L / τ) (m := m) hLip b U V hcU hcV hpU hpV
      (ResidualFilter.auxiliaryFilter 1 τ φ) (by norm_num) hMU hMV hf.auxiliary
      (h.auxiliary_contract (by norm_num) hτ hτ1) hα0 hα1 hαρ
      (div_nonneg hL hτ.le) (fun s hs t ht => h.auxiliary_inverse_lipschitz (by norm_num) hτ hτ1 hs ht)
      hδ c hcK (R z)
    rw [auxiliary_residualWeight_high_eq V hcV hpV φ hMV hf hα0.le hτ z] at hb
    have hp0 : 0 ≤ dyadicSchattenExponent m := (by norm_num : (0 : ℝ) ≤ 2).trans
      (dyadicSchattenExponent_ge_two m)
    have hSp : 0 ≤ hsSchattenNorm b c (dyadicSchattenExponent m) := hsSchattenNorm_nonneg b c _
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_abs_self D) (Real.sqrt_nonneg 2))
          (by positivity : 0 ≤ 1 + L / τ)) hp0) hSp) hW
    have hrat := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ Real.sqrt 2 * |D|)) hp0) hSp) hW
    calc
      _ ≤ Real.sqrt 2 * D * (1 + L / τ) * dyadicSchattenExponent m *
          hsSchattenNorm b c (dyadicSchattenExponent m) * W := hb
      _ ≤ Real.sqrt 2 * |D| * (1 + L / τ) * dyadicSchattenExponent m *
          hsSchattenNorm b c (dyadicSchattenExponent m) * W := hmul
      _ ≤ Real.sqrt 2 * |D| * ((1 + L) / τ) * dyadicSchattenExponent m *
          hsSchattenNorm b c (dyadicSchattenExponent m) * W := hrat
      _ = _ := by dsimp only [C]; ring
  have hopt := le_mul_hsSchattenEndpoint_of_dyadic b c (C := C / τ * W)
    (mul_nonneg (div_nonneg hC hτ.le) hW) hAll
  rw [mul_apply_eq_comp]
  simpa only [W, R] using hopt.trans_eq
    (show (2 * (C / τ * W)) * hsSchattenEndpoint b c =
      auxiliaryLipschitzConstant CL α ρ A * (hsSchattenEndpoint b c / τ) * W by
      dsimp only [C, D, L, auxiliaryLipschitzConstant]; ring)

/-- Full dimensionless localization with an explicit dyadic Lipschitz input.
The auxiliary estimate and all four actual blocks are proved conclusions. -/
theorem localized_interaction_from_lipschitz {CL : ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uH, uH, uH, uH} CL) (b : HilbertBasis I ℝ H)
    (U V : H →L[ℝ] H) (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (φ : ℝ → ℝ)
    {M ρ A α τ : ℝ} (hMU : ‖U‖ ≤ M) (hMV : ‖V‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract 1 M ρ A φ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hαρ : α / 2 ≤ ρ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτA : τ ≤ 1 / (4 * (A + 1)))
    (hδ : lowBlockDeviation U V hcV hpV ≤ 1 / 4)
    (c : HilbertSchmidtColumns I H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation V U hcV hcU hpV hpU 1) (z : H) :
    ‖(compactRegularizedSqrt V hcV hpV 0 * compactInteraction U V hcU hcV hpU hpV φ
        (by norm_num) hMU hMV hf h * compactRegularizedSqrt V hcV hpV 0) z‖ ≤
      localizedLipschitzConstant CL α ρ A *
        (τ + lowBlockDeviation U V hcV hpV / τ) * ‖compactResidualOperator V hcV hpV φ hMV hf z‖ +
      localizedLipschitzConstant CL α ρ A * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator V hcV hpV φ (lam := 1) (α := α) (by norm_num) hα0.le hMV hf z‖ := by
  exact localized_interaction_of_auxiliary_bound b U V hcU hcV hpU hpV φ hMU hMV hf h
    hα0.le (by linarith) hτ hτ1 hτA hδ c hcK (auxiliaryLipschitzConstant CL α ρ A)
    (auxiliary_embedded_endpoint_from_lipschitz hLip b U V hcU hcV hpU hpV φ hMU hMV hf h
      hα0 hα1 hαρ hτ hτ1 hδ c hcK) z

/-- Actual regularization scaling preserves the original endpoint and the
same mixed columns, with a constant independent of lambda. -/
theorem localized_original_core_from_lipschitz {CL : ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uH, uH, uH, uH} CL)
    (b : HilbertBasis I ℝ H)
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
      localizedLipschitzConstant CL α ρ A * (τ + ‖realNormalizedPerturbation T TX hc hp lam‖ / τ) *
        ‖compactResidualOperator T hc hp φ hM hf z‖ +
      localizedLipschitzConstant CL α ρ A * (hsSchattenEndpoint b c / τ) *
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
  have hb := localized_interaction_from_lipschitz hLip b
    (dimensionlessCovariance TX lam) (dimensionlessCovariance T lam)
    (dimensionlessCovariance_isCompact TX hcX lam) (dimensionlessCovariance_isCompact T hc lam)
    (dimensionlessCovariance_isPositive TX hpX hlam) (dimensionlessCovariance_isPositive T hp hlam)
    (localizedDimensionlessProfile lam φ)
    (dimensionlessCovariance_norm_le TX hlam hMX) (dimensionlessCovariance_norm_le T hlam hM)
    (localizedDimensionless_spectralFilter hlam hf) (localizedDimensionless_contract hlam h)
    hα0 hα1 hαρ hτ hτ1 hτA hδd c hcKd z
  simpa only [localizedLipschitzConstant,
    embeddedInteraction_dimensionless TX T hcX hc hpX hp φ hlam hMX hM hf h,
    lowBlockDeviation, realNormalizedPerturbation_dimensionless T TX hc hp hlam,
    compactResidualOperator_dimensionless T hc hp φ hlam hM hf,
    compactResidualWeightOperator_dimensionless T hc hp φ hlam hα0.le hM hf] using hb

section Prediction

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The constructed supported polar isometry transfers the actual bound to
prediction space. Neither Hilbert space needs be separable. -/
theorem localized_prediction_core_from_lipschitz {CL : ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uH, uH, uH, uH} CL)
    (b : HilbertBasis I ℝ H)
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
      localizedLipschitzConstant CL α ρ A *
        (τ + ‖realNormalizedPerturbation (S.adjoint.comp S) TX hc
          (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam‖ / τ) *
        ‖compactResidualOperator (S.comp S.adjoint)
          (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
          (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ
          ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf f‖ +
      localizedLipschitzConstant CL α ρ A * (hsSchattenEndpoint b c / τ) *
        ‖compactResidualWeightOperator (S.comp S.adjoint)
          (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
          (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα0.le
          ((self_comp_adjoint_norm_eq_adjoint_comp_self S).trans_le hM) hf f‖ := by
  have hfRange : f ∈ PredictionRange S := by
    simpa only [closure_range_self_comp_adjoint S] using hsupport
  let fs : PredictionRange S := ⟨f, hfRange⟩
  let G := compactInteraction TX (S.adjoint.comp S) hcX hc hpX
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMX hM hf h
  have hb := localized_original_core_from_lipschitz hLip b TX (S.adjoint.comp S) hcX hc hpX
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

/-- The actual sampled feature/RKHS localized estimate in the original cutoff
format. Actual mixed columns and their reconstruction are supplied internally;
the dyadic Lipschitz input is kept explicit for modular reuse and is supplied
by `finiteDyadicLipschitzSchur_proved` in `FixedSymbolFourierLpBound`. -/
theorem actual_localized_interaction_from_lipschitz {CL : ℝ}
    (hLip : FiniteDyadicLipschitzSchur.{uH, uH, uH, uH} CL)
    (b : HilbertBasis I ℝ H)
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
      localizedLipschitzConstant CL α ρ A * (τ + actualCovarianceDeviation k hk lam x / τ) *
        ‖populationSpectralResidual k hk φ hM hf f‖ +
      (localizedLipschitzConstant CL α ρ A * hsSchattenEndpoint b (manuscriptMixedColumns b k hk lam x) / τ) *
        ‖actualBiasWeight k hk φ hlam hα0.le hM hf f‖ := by
  have hτ1 : τ ≤ 1 := hτ.2.trans (min_le_left _ _)
  have hτA : τ ≤ 1 / (4 * (A + 1)) := hτ.2.trans (min_le_right _ _)
  have hb := localized_prediction_core_from_lipschitz hLip b (featureEmbedding μ k hk)
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
