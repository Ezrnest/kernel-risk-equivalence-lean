import KernelSeq.EmpiricalConditionalRisk
import KernelSeq.EmpiricalVariance
import KernelSeq.OperatorTrace
import KernelSeq.RKHSFeature

/-!
# Conditional risk for the canonical RKHS and the exact L² target

The target's globally measurable representative is selected from its actual
`AEStronglyMeasurable` witness. Kernel measurability, feature integrability,
embedding bounds, empirical-estimator measurability, and bias integrability
are proved upstream and instantiated here. The target in the risk is exactly
the given `Lp` element. No separability of `L²(μ)` is imposed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal MeasureTheory

namespace KernelSeq

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A globally strongly measurable representative, chosen from the actual
almost-everywhere strong-measurability witness of the L² target. -/
noncomputable def lpRepresentative (f : Lp ℝ 2 μ) : X → ℝ :=
  (Lp.aestronglyMeasurable f).mk f

theorem lpRepresentative_stronglyMeasurable (f : Lp ℝ 2 μ) :
    StronglyMeasurable (lpRepresentative f) :=
  (Lp.aestronglyMeasurable f).stronglyMeasurable_mk

theorem lpRepresentative_measurable (f : Lp ℝ 2 μ) : Measurable (lpRepresentative f) :=
  (lpRepresentative_stronglyMeasurable f).measurable

theorem lpRepresentative_ae_eq (f : Lp ℝ 2 μ) : lpRepresentative f =ᵐ[μ] f :=
  (Lp.aestronglyMeasurable f).ae_eq_mk.symm

theorem lpRepresentative_memLp (f : Lp ℝ 2 μ) : MemLp (lpRepresentative f) 2 μ :=
  MemLp.ae_eq (lpRepresentative_ae_eq f).symm (Lp.memLp f)

@[simp]
theorem lpRepresentative_toLp (f : Lp ℝ 2 μ) :
    (lpRepresentative_memLp f).toLp (lpRepresentative f) = f := by
  calc
    _ = (Lp.memLp f).toLp f :=
      MemLp.toLp_congr _ _ (lpRepresentative_ae_eq f)
    _ = f := Lp.toLp_coeFn _ _

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  [IsProbabilityMeasure μ] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The bounded-feature construction is exactly the canonical RKHS embedding. -/
theorem boundedFeatureEmbedding_rkhs_eq
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2) :
    boundedFeatureEmbedding μ (rkhsFeature (X := X) (H := H))
      (rkhsFeature_stronglyMeasurable hK) κ (rkhsFeature_norm_le κ hκ hdiag) =
        rkhsEmbedding μ hK κ hκ hdiag := rfl

/-- The actual filtered prediction for a finite design and observed responses. -/
noncomputable def rkhsEmpiricalPrediction
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) (y : Fin n → ℝ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) : Lp ℝ 2 μ :=
  rkhsEmbedding μ hK κ hκ hdiag
    (empiricalSpectralEstimator hn (fun j => rkhsFeature (X := X) (H := H) (x j)) κ
      (fun j => pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ hκ hdiag (x j)) 2)
      y φ hlam h)

/-- The actual coefficient of one observation's noise in prediction space. -/
noncomputable def rkhsEmpiricalCoefficient
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) : Lp ℝ 2 μ :=
  empiricalPredictionCoefficient (rkhsEmbedding μ hK κ hκ hdiag) hn
    (fun j => rkhsFeature (X := X) (H := H) (x j)) κ
    (fun j => pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ hκ hdiag (x j)) 2) φ hlam h i

/-- The actual RKHS-to-prediction map after empirical filtering. -/
noncomputable def rkhsEmpiricalPredictionMap
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) : H →L[ℝ] Lp ℝ 2 μ :=
  (rkhsEmbedding μ hK κ hκ hdiag).comp
    (empiricalFilterOperator hn (fun j => rkhsFeature (X := X) (H := H) (x j)) κ
      (fun j => pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ hκ hdiag (x j)) 2) φ hlam h)

/-- Canonical-source conditional risk. The only target evaluations appearing
in the source noise model use the selected measurable representative. The
prediction-risk target itself is precisely the original `f : Lp ℝ 2 μ`. -/
theorem rkhs_conditional_prediction_risk
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, MeasurePreserving (fun ω => (Z i ω).1) P μ) (f : Lp ℝ 2 μ)
    (σ : ℝ) (hσ : 0 < σ) (hind : iIndepFun Z P)
    (hmean : ∀ i, P[observationNoise (Z i) (lpRepresentative f) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => observationNoise (Z i) (lpRepresentative f) ω ^ 2) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => σ ^ 2))
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ) (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    Integrable (fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
      (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) P ∧
    P[(fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
      (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) | ⨆ j, observationDesignSigma (Z j)] =ᵐ[P]
      (fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
        (fun j => lpRepresentative f ((Z j ω).1)) φ hlam h - f‖ ^ 2 +
        σ ^ 2 * ∑ i, ‖rkhsEmpiricalCoefficient (μ := μ) hK κ hκ hdiag hn (fun j => (Z j ω).1) φ hlam h i‖ ^ 2) := by
  have hr := empirical_spectral_conditional_risk
    (rkhsFeature (X := X) (H := H)) (rkhsFeature_stronglyMeasurable hK) κ hκ
    (rkhsFeature_norm_le κ hκ hdiag) hn Z hZ hlaw
    (lpRepresentative f) (lpRepresentative_measurable f) (lpRepresentative_memLp f)
    σ hσ hind hmean hsecond φ hlam hf h
  simpa only [featureSamplePredictionError, featureSamplePredictionBias,
    featureSamplePredictionCoefficient, boundedFeatureEmbedding_rkhs_eq hK κ hκ hdiag, lpRepresentative_toLp,
    rkhsEmpiricalPrediction, rkhsEmpiricalCoefficient] using hr

/-- The conditional variance is the genuine Hilbert--Schmidt norm of the actual
filtered prediction map composed with the actual empirical square root. -/
theorem rkhsEmpiricalCoefficient_variance_eq_hs {ι : Type*}
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (b : HilbertBasis ι ℝ H) (σ : ℝ) :
    σ ^ 2 * ∑ i, ‖rkhsEmpiricalCoefficient (μ := μ) hK κ hκ hdiag hn x φ hlam h i‖ ^ 2 =
      σ ^ 2 / (n : ℝ) * ‖empiricalVarianceColumns
        (fun j => rkhsFeature (X := X) (H := H) (x j))
        (rkhsEmpiricalPredictionMap (μ := μ) hK κ hκ hdiag hn x φ hlam h) b‖ ^ 2 :=
  empiricalPredictionCoefficient_variance_eq_hs (rkhsEmbedding μ hK κ hκ hdiag) hn _ κ _ φ hlam h b σ

/-- The same actual variance is a positive-square diagonal trace. The
Hilbert--Schmidt construction proves the required diagonal summability and
basis independence; no trace-class certificate is supplied as a premise. -/
theorem rkhsEmpiricalCoefficient_variance_eq_basisTrace {ι : Type*}
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (b : HilbertBasis ι ℝ H) (σ : ℝ) :
    let V := (rkhsEmpiricalPredictionMap (μ := μ) hK κ hκ hdiag hn x φ hlam h).comp
      (empiricalCovarianceSqrt (fun j => rkhsFeature (X := X) (H := H) (x j)))
    σ ^ 2 * ∑ i, ‖rkhsEmpiricalCoefficient (μ := μ) hK κ hκ hdiag hn x φ hlam h i‖ ^ 2 =
      σ ^ 2 / (n : ℝ) * basisTrace b (V.adjoint.comp V) := by
  dsimp only
  rw [rkhsEmpiricalCoefficient_variance_eq_hs hK κ hκ hdiag hn x φ hlam h b σ]
  apply congrArg (fun r : ℝ => σ ^ 2 / (n : ℝ) * r)
  have ht := hilbertSchmidtSquare_trace b (empiricalVarianceColumns
    (fun j => rkhsFeature (X := X) (H := H) (x j))
    (rkhsEmpiricalPredictionMap (μ := μ) hK κ hκ hdiag hn x φ hlam h) b)
  simpa only [hilbertSchmidtOperator_empiricalVarianceColumns] using ht.symm

/-- Canonical conditional risk with the variance written as the actual
Hilbert--Schmidt norm squared, with the exact manuscript factor `σ²/n`. -/
theorem rkhs_conditional_prediction_risk_hs {ι : Type*}
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, MeasurePreserving (fun ω => (Z i ω).1) P μ) (f : Lp ℝ 2 μ)
    (σ : ℝ) (hσ : 0 < σ) (hind : iIndepFun Z P)
    (hmean : ∀ i, P[observationNoise (Z i) (lpRepresentative f) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => observationNoise (Z i) (lpRepresentative f) ω ^ 2) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => σ ^ 2))
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ) (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ)
    (b : HilbertBasis ι ℝ H) :
    Integrable (fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
      (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) P ∧
    P[(fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
      (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) | ⨆ j, observationDesignSigma (Z j)] =ᵐ[P]
      (fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
        (fun j => lpRepresentative f ((Z j ω).1)) φ hlam h - f‖ ^ 2 +
        σ ^ 2 / (n : ℝ) * ‖empiricalVarianceColumns
          (fun j => rkhsFeature (X := X) (H := H) ((Z j ω).1))
          (rkhsEmpiricalPredictionMap (μ := μ) hK κ hκ hdiag hn (fun j => (Z j ω).1) φ hlam h) b‖ ^ 2) := by
  obtain ⟨hi, hr⟩ := rkhs_conditional_prediction_risk hK κ hκ hdiag hn Z hZ hlaw f σ hσ
    hind hmean hsecond φ hlam hf h
  refine ⟨hi, ?_⟩
  filter_upwards [hr] with ω hω
  rw [hω, rkhsEmpiricalCoefficient_variance_eq_hs hK κ hκ hdiag hn (fun j => (Z j ω).1) φ hlam h b σ]

/-- A basis-trace form of the canonical conditional risk. This uses an actual
positive Hilbert--Schmidt square rather than an uninterpreted trace symbol. -/
theorem rkhs_conditional_prediction_risk_basisTrace {ι : Type*}
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, MeasurePreserving (fun ω => (Z i ω).1) P μ) (f : Lp ℝ 2 μ)
    (σ : ℝ) (hσ : 0 < σ) (hind : iIndepFun Z P)
    (hmean : ∀ i, P[observationNoise (Z i) (lpRepresentative f) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => observationNoise (Z i) (lpRepresentative f) ω ^ 2) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => σ ^ 2))
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ) (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ)
    (b : HilbertBasis ι ℝ H) :
    Integrable (fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
      (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) P ∧
    P[(fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
      (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) | ⨆ j, observationDesignSigma (Z j)] =ᵐ[P]
      (fun ω =>
        let V : H →L[ℝ] Lp ℝ 2 μ :=
          (rkhsEmpiricalPredictionMap (μ := μ) hK κ hκ hdiag hn
            (fun j => (Z j ω).1) φ hlam h).comp
            (empiricalCovarianceSqrt (fun j => rkhsFeature (X := X) (H := H) ((Z j ω).1)))
        ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
          (fun j => lpRepresentative f ((Z j ω).1)) φ hlam h - f‖ ^ 2 +
          σ ^ 2 / (n : ℝ) * basisTrace b (V.adjoint.comp V)) := by
  obtain ⟨hi, hr⟩ := rkhs_conditional_prediction_risk hK κ hκ hdiag hn Z hZ hlaw f σ hσ
    hind hmean hsecond φ hlam hf h
  refine ⟨hi, ?_⟩
  filter_upwards [hr] with ω hω
  rw [hω, rkhsEmpiricalCoefficient_variance_eq_basisTrace hK κ hκ hdiag hn
    (fun j => (Z j ω).1) φ hlam h b σ]

end KernelSeq
