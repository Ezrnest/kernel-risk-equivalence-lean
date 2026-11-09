import KernelSeq.FiniteSingularDistribution

/-!
# Actual Schatten moments of singular truncations

The actual sorted right singular coordinates give exact moments of every
retained and discarded block. Applying the actual exceedance count as the
truncation rank yields genuine high and low spectral pieces for interpolation.
No singular-value decomposition of the truncated operators is assumed.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H]

/-- Actual right-coordinate restriction in the sorted singular basis. -/
def finiteSingularMask (A : H →L[ℝ] H) (s : Finset (Fin (Module.finrank ℝ H))) : H →L[ℝ] H :=
  A * finiteBasisProjection (finiteRightSingularBasis A).toHilbertBasis s

/-- The covariance of the actual masked operator is diagonal in the
original right singular basis, including all zero singular directions. -/
theorem finiteSingularMask_covariance_eigen (A : H →L[ℝ] H)
    (s : Finset (Fin (Module.finrank ℝ H))) (i : Fin (Module.finrank ℝ H)) :
    ((finiteSingularMask A s).adjoint * finiteSingularMask A s)
        (finiteRightSingularBasis A i) =
      (if i ∈ s then A.toLinearMap.singularValues i ^ 2 else 0) • finiteRightSingularBasis A i := by
  classical
  let e := (finiteRightSingularBasis A).toHilbertBasis
  let P := finiteBasisProjection e s
  have hP : P.adjoint = P := (finiteBasisProjection_isSelfAdjoint e s).adjoint_eq
  have hi : P (e i) = if i ∈ s then e i else 0 := by
    by_cases his : i ∈ s
    · simpa only [P, if_pos his] using finiteBasisProjection_basis e s i
    · simpa only [P, if_neg his] using finiteBasisProjection_basis e s i
  have hcov : (A.adjoint * A) (e i) = A.toLinearMap.singularValues i ^ 2 • e i := by
    simpa only [e, OrthonormalBasis.coe_toHilbertBasis] using finiteRightSingularBasis_covariance_eigen A i
  have he : e i = finiteRightSingularBasis A i := by
    simp only [e, OrthonormalBasis.coe_toHilbertBasis]
  rw [← he]
  change ((A * P).adjoint * (A * P)) (e i) = _
  have hadj : (A * P).adjoint = P * A.adjoint := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp, hP]
  rw [hadj]
  by_cases his : i ∈ s
  · simp only [mul_apply_eq_comp, ← mul_apply_eq_comp A.adjoint A, hcov,
      map_smul, hi, if_pos his]
  · simp only [mul_apply_eq_comp, hi, if_neg his, map_zero, zero_smul]

/-- Exact actual Schatten moment of a singular-coordinate block, at every
positive real exponent. -/
theorem finiteSingularMask_rpow {ι : Type*} [Fintype ι] (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) (s : Finset (Fin (Module.finrank ℝ H))) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b (finiteSingularMask A s)) p ^ p =
      ∑ i ∈ s, A.toLinearMap.singularValues i ^ p := by
  classical
  let B := finiteSingularMask A s
  let C := B.adjoint * B
  have hC : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self B
  let e := (finiteRightSingularBasis A).toHilbertBasis
  have hc : hsSingularCovariance b (finiteOperatorColumns b B) = C := by
    simp only [hsSingularCovariance, hilbertSchmidtOperator_finiteOperatorColumns,
      ContinuousLinearMap.mul_def, C]
  have hpower := hsSchattenNorm_rpow b (finiteOperatorColumns b B) hp
  change _ = compactPositivePowerSum (hsSingularCovariance b (finiteOperatorColumns b B)) (p / 2) at hpower
  rw [hc, ← finitePositivePower_trace e C hC (p / 2) (by positivity)] at hpower
  rw [hpower]
  simp only [basisTrace, tsum_fintype]
  trans (∑ i : Fin (Module.finrank ℝ H), if i ∈ s then A.toLinearMap.singularValues i ^ p else 0)
  · apply Finset.sum_congr rfl
    intro i _
    have he : C (e i) = (if i ∈ s then A.toLinearMap.singularValues i ^ 2 else 0) • e i := by
      simpa only [C, B, e, OrthonormalBasis.coe_toHilbertBasis] using finiteSingularMask_covariance_eigen A s i
    rw [finitePositivePower_eigen C hC (p / 2) (by positivity) he]
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, e.orthonormal.norm_eq_one, one_pow, mul_one]
    by_cases hi : i ∈ s
    · simp only [if_pos hi]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (A.toLinearMap.singularValues_nonneg i)]
      congr 1
      ring
    · simp only [if_neg hi, Real.zero_rpow (by positivity : p / 2 ≠ 0)]
  · simp

omit [CompleteSpace H] in
/-- Counting selects exactly the strict-high singular coordinates, retaining
equal-threshold singular values in the low part. -/
theorem finiteSingularPrefix_count_iff (A : H →L[ℝ] H) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin (Module.finrank ℝ H)) :
    i ∈ finiteSingularPrefix (H := H) (finiteSingularCount A t) ↔ t < A.toLinearMap.singularValues i := by
  rw [mem_finiteSingularPrefix]
  simpa only [not_le] using not_congr (finiteSingularCount_le_iff A ht i.val)

omit [FiniteDimensional ℝ H] [CompleteSpace H] in
theorem finiteBasisProjection_finset_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    finiteBasisProjection b sᶜ = 1 - finiteBasisProjection b s := by
  classical
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro i
  by_cases hi : i ∈ s <;> simp [finiteBasisProjection_basis, hi]

/-- Exact moment of the actual optimal rank truncation. -/
theorem finiteSingularTruncation_rpow {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (k : ℕ) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b (finiteSingularTruncation A k)) p ^ p =
      ∑ i ∈ finiteSingularPrefix (H := H) k, A.toLinearMap.singularValues i ^ p := by
  simpa only [finiteSingularTruncation, finiteSingularMask] using
    finiteSingularMask_rpow b A (finiteSingularPrefix k) hp

/-- Exact moment of the actual discarded tail, proved by complementing the
genuine right-coordinate projection. -/
theorem finiteSingularRemainder_rpow {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (k : ℕ) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b (A - finiteSingularTruncation A k)) p ^ p =
      ∑ i ∈ (finiteSingularPrefix (H := H) k)ᶜ, A.toLinearMap.singularValues i ^ p := by
  have heq : A - finiteSingularTruncation A k =
      finiteSingularMask A (finiteSingularPrefix (H := H) k)ᶜ := by
    unfold finiteSingularMask finiteSingularTruncation
    rw [finiteBasisProjection_finset_compl (finiteRightSingularBasis A).toHilbertBasis
      (finiteSingularPrefix (H := H) k)]
    noncomm_ring
  rw [heq]
  exact finiteSingularMask_rpow b A _ hp

/-- Counting at the threshold gives exactly the true strict-high moment. -/
theorem finiteSingularHigh_rpow {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) {t p : ℝ} (ht : 0 ≤ t) (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b
      (finiteSingularTruncation A (finiteSingularCount A t))) p ^ p =
        ∑ i : Fin (Module.finrank ℝ H), if t < A.toLinearMap.singularValues i then
          A.toLinearMap.singularValues i ^ p else 0 := by
  classical
  rw [finiteSingularTruncation_rpow b A _ hp]
  have hset : finiteSingularPrefix (H := H) (finiteSingularCount A t) =
      Finset.univ.filter (fun i : Fin (Module.finrank ℝ H) => t < A.toLinearMap.singularValues i) := by
    ext i
    simp only [finiteSingularPrefix_count_iff A ht i, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset, Finset.sum_filter]

/-- The complementary true low moment includes every threshold equality. -/
theorem finiteSingularLow_rpow {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) {t p : ℝ} (ht : 0 ≤ t) (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b
      (A - finiteSingularTruncation A (finiteSingularCount A t))) p ^ p =
        ∑ i : Fin (Module.finrank ℝ H), if A.toLinearMap.singularValues i ≤ t then
          A.toLinearMap.singularValues i ^ p else 0 := by
  classical
  rw [finiteSingularRemainder_rpow b A _ hp]
  have hset : (finiteSingularPrefix (H := H) (finiteSingularCount A t))ᶜ =
      Finset.univ.filter (fun i : Fin (Module.finrank ℝ H) => A.toLinearMap.singularValues i ≤ t) := by
    ext i
    simp only [Finset.mem_compl, finiteSingularPrefix_count_iff A ht i, not_lt,
      Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset, Finset.sum_filter]

end
end KernelSeq
