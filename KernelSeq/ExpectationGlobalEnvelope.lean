import KernelSeq.ActualRiskAsymptotics

/-!
# Actual global prediction and conditional-risk envelopes

The finite observation rule and its proved coefficient bound control the
actual loss on every design. No concentration event, inverse sample
covariance estimate, or bound on target evaluations is assumed. The target
remains an arbitrary L2 function.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace KernelSeq

section FiniteRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cauchy--Schwarz for the actual finite response rule. -/
theorem norm_sq_finite_response_rule_le {n : ℕ} (y : Fin n → ℝ)
    (a : Fin n → E) {C : ℝ} (_hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ‖∑ i, y i • a i‖ ^ 2 ≤ (n : ℝ) * C ^ 2 * ∑ i, y i ^ 2 := by
  classical
  have hnorm : ‖∑ i, y i • a i‖ ≤ C * ∑ i, |y i| := by
    calc
      _ ≤ ∑ i, ‖y i • a i‖ := norm_sum_le _ _
      _ ≤ ∑ i, |y i| * C := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin n => |y i|)
    (fun _ => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  calc
    _ ≤ (C * ∑ i, |y i|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = C ^ 2 * (∑ i, |y i|) ^ 2 := mul_pow _ _ _
    _ ≤ C ^ 2 * ((∑ i, y i ^ 2) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg C)
    _ = _ := by ring

/-- A global squared-loss envelope for a finite linear prediction rule. -/
theorem finite_response_loss_sq_le {n : ℕ} (y : Fin n → ℝ)
    (a : Fin n → E) (f : E) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ‖(∑ i, y i • a i) - f‖ ^ 2 ≤
      2 * ‖f‖ ^ 2 + 2 * (n : ℝ) * C ^ 2 * ∑ i, y i ^ 2 := by
  have hnorm := norm_sub_le (∑ i, y i • a i) f
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hsum := norm_sq_finite_response_rule_le y a hC ha
  nlinarith [sq_nonneg (‖∑ i, y i • a i‖ - ‖f‖)]

end FiniteRule

section ActualRKHS

variable {H X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The global prediction envelope uses the actual empirical coefficients. -/
theorem rkhs_prediction_loss_global_le
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) (y : Fin n → ℝ) (f : Lp ℝ 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn x y φ hlam h - f‖ ^ 2 ≤
      2 * ‖f‖ ^ 2 + 2 * (n : ℝ) * (A * κ ^ 2 / ((n : ℝ) * lam)) ^ 2 *
        ∑ i, y i ^ 2 := by
  unfold rkhsEmpiricalPrediction
  rw [empiricalSpectralEstimator_prediction_sum]
  apply finite_response_loss_sq_le
  · exact div_nonneg (mul_nonneg (h.constant_nonneg hlam (sq_nonneg κ)) (sq_nonneg κ))
      (mul_nonneg (Nat.cast_nonneg _) hlam.le)
  · intro i
    exact empiricalPredictionCoefficient_norm_le _ hn _ κ hκ
      (rkhsEmbedding_norm_le μ hK κ hκ hdiag) (fun j => rkhsFeature_norm_le κ hκ hdiag (x j))
      φ hlam h i

/-- The actual all-design conditional risk has a global envelope involving
only the target's sampled squares and deterministic constants. -/
theorem rkhs_conditional_risk_global_le_ae
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
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    ∀ᵐ ω ∂P, rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h ω ≤
      2 * ‖f‖ ^ 2 +
        2 * (n : ℝ) * (A * κ ^ 2 / ((n : ℝ) * lam)) ^ 2 *
          ∑ i, lpRepresentative f ((Z i ω).1) ^ 2 +
        σ ^ 2 * (n : ℝ) * (A * κ ^ 2 / ((n : ℝ) * lam)) ^ 2 := by
  have hce := (rkhs_conditional_prediction_risk hK κ hκ hdiag hn Z hZ hlaw f σ hσ
    hind hmean hsecond φ hlam hf h).2
  filter_upwards [hce] with ω hω
  rw [show rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag hn Z f φ hlam h ω = _
    from hω]
  apply add_le_add
  · exact rkhs_prediction_loss_global_le hK κ hκ hdiag hn _ _ f φ hlam h
  · rw [mul_assoc (σ ^ 2)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg σ)
    calc
      _ ≤ ∑ i : Fin n, (A * κ ^ 2 / ((n : ℝ) * lam)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _)
          (empiricalPredictionCoefficient_norm_le _ hn _ κ hκ
            (rkhsEmbedding_norm_le μ hK κ hκ hdiag)
            (fun j => rkhsFeature_norm_le κ hκ hdiag ((Z j ω).1)) φ hlam h i) 2
      _ = _ := by simp

end ActualRKHS

end KernelSeq
