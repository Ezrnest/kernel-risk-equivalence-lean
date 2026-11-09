import KernelSeq.HilbertSchmidtInvariant
import KernelSeq.EmpiricalSpectral

/-!
# Actual empirical variance as a Hilbert--Schmidt norm

For the actual finite-sample covariance, its constructed real square root
`R = T_X^(1/2)` satisfies `R*R = T_X`. An arbitrary bounded prediction map `A`
then has genuinely square-summable columns after composition with `R`, and
`∑ ‖A R b_j‖² = n⁻¹ ∑ ‖A z_i‖²` in every Hilbert basis of the domain.

The proof starts with the actual adjoint columns, uses the empirical quadratic
form and finite-sum Parseval, and transfers energy back through the actual
adjoint. Neither a trace identity nor Hilbert--Schmidt existence is assumed.
Neither Hilbert space is assumed separable or finite dimensional.
-/

open scoped BigOperators ENNReal

namespace KernelSeq

variable {H E ι η : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual unregularized square root of the actual empirical covariance. -/
noncomputable def empiricalCovarianceSqrt {n : ℕ} (z : Fin n → H) : H →L[ℝ] H :=
  compactRegularizedSqrt (empiricalCovariance z) (empiricalCovariance_isCompact z)
    (empiricalCovariance_isPositive z) 0

theorem empiricalCovarianceSqrt_isSelfAdjoint {n : ℕ} (z : Fin n → H) :
    IsSelfAdjoint (empiricalCovarianceSqrt z) :=
  compactRegularizedSqrt_isSelfAdjoint _ _ _ _

theorem empiricalCovarianceSqrt_sq {n : ℕ} (z : Fin n → H) :
    empiricalCovarianceSqrt z * empiricalCovarianceSqrt z = empiricalCovariance z := by
  simpa only [empiricalCovarianceSqrt, zero_smul, add_zero] using
    compactRegularizedSqrt_sq (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) 0 le_rfl

/-- The square-root norm is the actual empirical quadratic form. -/
theorem empiricalCovarianceSqrt_norm_sq {n : ℕ} (z : Fin n → H) (u : H) :
    ‖empiricalCovarianceSqrt z u‖ ^ 2 =
      (n : ℝ)⁻¹ * ∑ i, inner ℝ (z i) u ^ 2 := by
  rw [(empiricalCovarianceSqrt z).apply_norm_sq_eq_inner_adjoint_right]
  change inner ℝ u ((empiricalCovarianceSqrt z).adjoint (empiricalCovarianceSqrt z u)) = _
  rw [(empiricalCovarianceSqrt_isSelfAdjoint z).adjoint_eq]
  change inner ℝ u ((empiricalCovarianceSqrt z * empiricalCovarianceSqrt z) u) = _
  rw [empiricalCovarianceSqrt_sq, empiricalCovariance_quadratic]

/-- Each actual adjoint-column energy is an empirical finite coordinate sum. -/
theorem empiricalCovarianceSqrt_adjoint_norm_sq {n : ℕ} (z : Fin n → H)
    (A : H →L[ℝ] E) (u : E) :
    ‖empiricalCovarianceSqrt z (A.adjoint u)‖ ^ 2 =
      (n : ℝ)⁻¹ * ∑ i, inner ℝ (A (z i)) u ^ 2 := by
  rw [empiricalCovarianceSqrt_norm_sq]
  simp only [A.adjoint_inner_right]

/-- Finite-sum Parseval proves actual adjoint-column summability and its sum.
The codomain basis may have an uncountable or empty index. -/
theorem hasSum_empiricalCovarianceSqrt_adjoint_columns {n : ℕ} (z : Fin n → H)
    (A : H →L[ℝ] E) (e : HilbertBasis η ℝ E) :
    HasSum (fun j => ‖empiricalCovarianceSqrt z (A.adjoint (e j))‖ ^ 2)
      ((n : ℝ)⁻¹ * ∑ i, ‖A (z i)‖ ^ 2) := by
  have hrow (i : Fin n) : HasSum (fun j => inner ℝ (A (z i)) (e j) ^ 2) (‖A (z i)‖ ^ 2) := by
    simpa only [real_inner_comm (e _), ← pow_two, real_inner_self_eq_norm_sq] using
      e.hasSum_inner_mul_inner (A (z i)) (A (z i))
  have hs := (hasSum_sum (s := Finset.univ) (fun i _ => hrow i)).mul_left (n : ℝ)⁻¹
  simpa only [← empiricalCovarianceSqrt_adjoint_norm_sq] using hs

/-- The actual prediction-after-square-root operator has square-summable
columns, with the exact empirical mean prediction energy. -/
theorem empiricalVariance_column_energy {n : ℕ} (z : Fin n → H)
    (A : H →L[ℝ] E) (b : HilbertBasis ι ℝ H) :
    Summable (fun j => ‖A (empiricalCovarianceSqrt z (b j))‖ ^ 2) ∧
      (∑' j, ‖A (empiricalCovarianceSqrt z (b j))‖ ^ 2) =
        (n : ℝ)⁻¹ * ∑ i, ‖A (z i)‖ ^ 2 := by
  obtain ⟨s, ⟨e⟩⟩ := exists_hilbertBasis ℝ E
  have hs := hasSum_empiricalCovarianceSqrt_adjoint_columns z A e
  have ha := hilbertBasis_adjoint_column_energy e b
    ((empiricalCovarianceSqrt z).comp A.adjoint) hs.summable
  have hadj : ((empiricalCovarianceSqrt z).comp A.adjoint).adjoint =
      A.comp (empiricalCovarianceSqrt z) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      (empiricalCovarianceSqrt_isSelfAdjoint z).adjoint_eq]
  rw [hadj] at ha
  refine ⟨ha.1, ?_⟩
  exact ha.2.trans hs.tsum_eq

/-- Actual Hilbert--Schmidt columns of `A T_X^(1/2)`. Membership in `ℓ²` is
proved from the finite sample; it is not part of the input. -/
noncomputable def empiricalVarianceColumns {n : ℕ} (z : Fin n → H)
    (A : H →L[ℝ] E) (b : HilbertBasis ι ℝ H) : HilbertSchmidtColumns ι E :=
  ⟨fun j => A (empiricalCovarianceSqrt z (b j)),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (empiricalVariance_column_energy z A b).1)⟩

@[simp]
theorem empiricalVarianceColumns_apply {n : ℕ} (z : Fin n → H)
    (A : H →L[ℝ] E) (b : HilbertBasis ι ℝ H) (j : ι) :
    empiricalVarianceColumns z A b j = A (empiricalCovarianceSqrt z (b j)) := rfl

/-- These columns reconstruct the same bounded variance operator. -/
theorem hilbertSchmidtOperator_empiricalVarianceColumns {n : ℕ} (z : Fin n → H)
    (A : H →L[ℝ] E) (b : HilbertBasis ι ℝ H) :
    hilbertSchmidtOperator b (empiricalVarianceColumns z A b) =
      A.comp (empiricalCovarianceSqrt z) := by
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro j
  rw [hilbertSchmidtOperator_basis, empiricalVarianceColumns_apply]
  rfl

/-- The genuine Hilbert--Schmidt norm squared is the empirical mean energy. -/
theorem empiricalVarianceColumns_norm_sq {n : ℕ} (z : Fin n → H)
    (A : H →L[ℝ] E) (b : HilbertBasis ι ℝ H) :
    ‖empiricalVarianceColumns z A b‖ ^ 2 = (n : ℝ)⁻¹ * ∑ i, ‖A (z i)‖ ^ 2 := by
  rw [hsColumns_norm_sq]
  exact (empiricalVariance_column_energy z A b).2

/-- The exact variance normalization in the manuscript. It also respects the
empty-sample convention, while the statistical application uses positive `n`. -/
theorem empiricalVariance_eq_scaled_hs_norm {n : ℕ} (z : Fin n → H)
    (A : H →L[ℝ] E) (b : HilbertBasis ι ℝ H) (σ : ℝ) :
    σ ^ 2 / (n : ℝ) * ‖empiricalVarianceColumns z A b‖ ^ 2 =
      σ ^ 2 / (n : ℝ) ^ 2 * ∑ i, ‖A (z i)‖ ^ 2 := by
  rw [empiricalVarianceColumns_norm_sq]
  simp only [div_eq_mul_inv]
  ring

/-- Direct connection to the actual finite noise coefficients used in
conditional risk: their variance is the Hilbert--Schmidt variance norm of the
actual filtered prediction map. Random-design measurability is a separate step. -/
theorem empiricalPredictionCoefficient_variance_eq_hs (S : H →L[ℝ] E)
    {n : ℕ} (hn : 0 < n) (z : Fin n → H) (κ : ℝ)
    (hz : ∀ i, ‖z i‖ ^ 2 ≤ κ ^ 2) (φ : ℝ → ℝ) {lam ρ C : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ C φ)
    (b : HilbertBasis ι ℝ H) (σ : ℝ) :
    σ ^ 2 * ∑ i, ‖empiricalPredictionCoefficient S hn z κ hz φ hlam h i‖ ^ 2 =
      σ ^ 2 / (n : ℝ) * ‖empiricalVarianceColumns z
        (S.comp (empiricalFilterOperator hn z κ hz φ hlam h)) b‖ ^ 2 := by
  rw [empiricalVariance_eq_scaled_hs_norm]
  simp only [empiricalPredictionCoefficient, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    ← Finset.mul_sum, ContinuousLinearMap.comp_apply]
  ring

end KernelSeq
