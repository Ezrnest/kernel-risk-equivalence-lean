import KernelSeq.ExpectationGlobalEnvelope
import KernelSeq.ExpectationLeaveOneOutIntegration
import KernelSeq.ExpectationPredictionRisk

/-!
# Integrating the actual conditional risk on a bad-design event

Actual coefficient bounds and leave-one-out independence control the loss of
an arbitrary fixed L2 target. The structural event inputs in this modular
lemma are supplied by the actual covariance leave-one-out construction.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace KernelSeq

variable {H X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The actual bad-event risk is bounded by a quadratic polynomial in
`lambda^-1` times the common bad and leave-one-out event probability bound. -/
theorem integral_rkhs_conditional_risk_bad_le
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, MeasurePreserving (fun ω => (Z i ω).1) P μ)
    (f : Lp ℝ 2 μ) (σ : ℝ) (hσ : 0 < σ) (hind : iIndepFun Z P)
    (hmean : ∀ i, P[observationNoise (Z i) (lpRepresentative f) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => observationNoise (Z i) (lpRepresentative f) ω ^ 2) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => σ ^ 2))
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ)
    (B : Set Ω) (Bi : Fin n → Set Ω)
    (hBi : ∀ i, MeasurableSet[⨆ j, ⨆ (_ : j ≠ i), observationPairSigma (Z j)] (Bi i))
    (hsub : ∀ i, B ≤ᵐ[P] Bi i) {p : ℝ}
    (hprob : P.real B ≤ p) (hprobi : ∀ i, P.real (Bi i) ≤ p) :
    (∫ ω in B, rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h ω ∂P) ≤
      (2 * ‖f‖ ^ 2 + (A * κ ^ 2 / lam) ^ 2 * (2 * ‖f‖ ^ 2 + σ ^ 2)) * p := by
  let C := A * κ ^ 2 / ((n : ℝ) * lam)
  let F := fun ω => ∑ i, lpRepresentative f ((Z i ω).1) ^ 2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hp : 0 ≤ p := (measureReal_nonneg).trans hprob
  have hFint : Integrable F P := integrable_finsetSum _ fun i _ =>
    ((lpRepresentative_memLp f).comp_measurePreserving (hlaw i)).integrable_sq
  have henv := rkhs_conditional_risk_global_le_ae hK κ hκ hdiag hn Z hZ hlaw
    f σ hσ hind hmean hsecond φ hlam hf h
  have hRint := integrable_rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h
  have hFbound := integral_sample_target_sq_bad_le Z hZ hlaw hind f B Bi hBi hsub hprobi
  have hbase := integral_mono_ae (μ := P.restrict B) hRint.integrableOn
    (((integrable_const (2 * ‖f‖ ^ 2)).add (hFint.const_mul (2 * (n : ℝ) * C ^ 2))).add
      (integrable_const (σ ^ 2 * (n : ℝ) * C ^ 2))).integrableOn
    (ae_restrict_of_ae henv)
  have hsq : (n : ℝ) ^ 2 * C ^ 2 = (A * κ ^ 2 / lam) ^ 2 := by
    dsimp only [C]
    field_simp
  have hvar : (n : ℝ) * C ^ 2 ≤ (n : ℝ) ^ 2 * C ^ 2 := by
    exact mul_le_mul_of_nonneg_right (by nlinarith : (n : ℝ) ≤ (n : ℝ) ^ 2) (sq_nonneg C)
  calc
    _ ≤ ∫ ω in B, (2 * ‖f‖ ^ 2 + 2 * (n : ℝ) * C ^ 2 * F ω) +
        σ ^ 2 * (n : ℝ) * C ^ 2 ∂P := hbase
    _ = 2 * ‖f‖ ^ 2 * P.real B +
        (2 * (n : ℝ) * C ^ 2) * (∫ ω in B, F ω ∂P) +
        (σ ^ 2 * (n : ℝ) * C ^ 2) * P.real B := by
      have h1 : Integrable (fun _ : Ω => 2 * ‖f‖ ^ 2) (P.restrict B) := integrable_const _
      have h2 : Integrable (fun ω => 2 * (n : ℝ) * C ^ 2 * F ω) (P.restrict B) :=
        (hFint.const_mul _).integrableOn
      have h3 : Integrable (fun _ : Ω => σ ^ 2 * (n : ℝ) * C ^ 2) (P.restrict B) :=
        integrable_const _
      have he1 := integral_add (h1.add h2) h3
      have he2 := integral_add h1 h2
      dsimp only [Pi.add_apply] at he1 he2
      rw [he1, he2]
      simp only [integral_const_mul, setIntegral_const, smul_eq_mul]
      ring
    _ ≤ 2 * ‖f‖ ^ 2 * p +
        (2 * (n : ℝ) * C ^ 2) * ((n : ℝ) * ‖f‖ ^ 2 * p) +
        (σ ^ 2 * (n : ℝ) * C ^ 2) * p := by
      gcongr
    _ ≤ (2 * ‖f‖ ^ 2 + (n : ℝ) ^ 2 * C ^ 2 * (2 * ‖f‖ ^ 2 + σ ^ 2)) * p := by
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hvar (sq_nonneg σ)) hp]
    _ = _ := by rw [hsq]

end KernelSeq
