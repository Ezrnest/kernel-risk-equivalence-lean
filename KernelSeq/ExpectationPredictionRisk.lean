import KernelSeq.ActualRiskAsymptotics

/-!
# The actual expectation risk and its tower identity

Expectation risk integrates the squared prediction error of the original
empirical estimator over the actual observation law. Its equality with the
integrated all-design conditional risk is proved by conditional expectation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace KernelSeq

variable {H X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The expectation risk of the actual observed-response RKHS estimator. -/
noncomputable def rkhsExpectationPredictionRisk
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (f : Lp ℝ 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) : ℝ :=
  ∫ ω, ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
    (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2 ∂P

/-- The all-design tower identity for the actual estimator. -/
theorem rkhsExpectationPredictionRisk_eq_integral_conditional
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (hZ : ∀ i, Measurable (Z i))
    (f : Lp ℝ 2 μ) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    rkhsExpectationPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h =
      ∫ ω, rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h ω ∂P := by
  have hm : (⨆ j, observationDesignSigma (Z j)) ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup_le fun j => (hZ j).fst.comap_le
  exact (integral_condExp hm).symm

/-- A tower identity using the genuine integrability of the observed-response
loss. The final expectation theorem supplies this from the original model,
so no default value for a nonintegrable loss is used as a risk claim. -/
theorem rkhsExpectationPredictionRisk_eq_integral_conditional_of_integrable
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (hZ : ∀ i, Measurable (Z i))
    (f : Lp ℝ 2 μ) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ)
    (hint : Integrable (fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn
      (fun j => (Z j ω).1) (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) P) :
    rkhsExpectationPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h =
      ∫ ω, rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h ω ∂P := by
  have hm : (⨆ j, observationDesignSigma (Z j)) ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup_le fun j => (hZ j).fst.comap_le
  have he := setIntegral_condExp hm hint MeasurableSet.univ
  simpa only [setIntegral_univ, rkhsExpectationPredictionRisk, rkhsConditionalPredictionRisk] using he.symm

omit [IsProbabilityMeasure P] in
/-- The true conditional risk is nonnegative almost surely. -/
theorem rkhsConditionalPredictionRisk_nonneg_ae
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (f : Lp ℝ 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    0 ≤ᵐ[P] rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h :=
  condExp_nonneg (Eventually.of_forall fun _ => sq_nonneg _)

omit [IsProbabilityMeasure P] in
/-- Conditional risk is genuinely integrable, as a conditional expectation. -/
theorem integrable_rkhsConditionalPredictionRisk
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (f : Lp ℝ 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    Integrable (rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h) P :=
  integrable_condExp

end KernelSeq
