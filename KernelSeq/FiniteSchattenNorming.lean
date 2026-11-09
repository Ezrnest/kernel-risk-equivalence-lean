import KernelSeq.FiniteTraceDuality

/-!
# Actual finite Schatten norming operators

Positive spectral powers of the actual covariance construct the genuine
norming operator. Its two exact trace and Schatten identities include the
zero operator, zero eigenvalues and the endpoint q = 2. No norming operator,
spectral factorization or trace-duality certificate is assumed.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

private theorem positivePower_congr {C D : H →L[ℝ] H}
    (hC : C.IsPositive) (hD : D.IsPositive) (hCD : C = D) (r : ℝ) (hr : 0 ≤ r) :
    finitePositivePower C hC r hr = finitePositivePower D hD r hr := by
  subst D
  rfl

/-- Actual nonnegative powers of the same positive operator multiply by
adding exponents, including the zero spectral subspace. -/
theorem finitePositivePower_mul_same (C : H →L[ℝ] H) (hC : C.IsPositive)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    finitePositivePower C hC r hr * finitePositivePower C hC s hs =
      finitePositivePower C hC (r + s) (add_nonneg hr hs) := by
  let e := compactEigenbasis C (isCompactOperator_of_locallyCompactSpace_dom C) hC.isSymmetric
  apply continuousLinearMap_eq_of_hilbertBasis e
  intro i
  have he : C (e i) = i.1 • e i := compactEigenbasis_eigen C _ hC.isSymmetric i
  rw [mul_apply_eq_comp, finitePositivePower_eigen C hC s hs he, map_smul,
    finitePositivePower_eigen C hC r hr he, finitePositivePower_eigen C hC (r + s) _ he,
    smul_smul, Real.rpow_add_of_nonneg
      (compactEigenvalue_nonneg C (isCompactOperator_of_locallyCompactSpace_dom C) hC i) hr hs]
  congr 1
  ring

/-- The actual positive spectral power of an actual positive spectral power
is the product exponent, with no abstract functional-calculus assumption. -/
theorem finitePositivePower_rpow_same (C : H →L[ℝ] H) (hC : C.IsPositive)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    finitePositivePower (finitePositivePower C hC r hr)
      (finitePositivePower_isPositive C hC r hr) s hs =
        finitePositivePower C hC (r * s) (mul_nonneg hr hs) := by
  let e := compactEigenbasis C (isCompactOperator_of_locallyCompactSpace_dom C) hC.isSymmetric
  apply continuousLinearMap_eq_of_hilbertBasis e
  intro i
  have he : C (e i) = i.1 • e i := compactEigenbasis_eigen C _ hC.isSymmetric i
  have hp := finitePositivePower_eigen C hC r hr he
  rw [finitePositivePower_eigen _ _ s hs hp, finitePositivePower_eigen C hC (r * s) _ he,
    Real.rpow_mul (compactEigenvalue_nonneg C (isCompactOperator_of_locallyCompactSpace_dom C) hC i)]

/-- Every positive real Schatten moment of an actual finite operator is the
trace of the corresponding actual covariance power. -/
theorem finiteSchatten_rpow_eq_covariancePowerTrace (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b A) p ^ p =
      basisTrace b (finitePositivePower (A.adjoint * A)
        (ContinuousLinearMap.isPositive_adjoint_comp_self A) (p / 2) (by positivity)) := by
  have hcov : hsSingularCovariance b (finiteOperatorColumns b A) = A.adjoint * A := by
    simp only [hsSingularCovariance, hilbertSchmidtOperator_finiteOperatorColumns, ContinuousLinearMap.mul_def]
  have h := hsSchattenNorm_rpow b (finiteOperatorColumns b A) hp
  change _ = compactPositivePowerSum (hsSingularCovariance b (finiteOperatorColumns b A)) (p / 2) at h
  rw [hcov] at h
  exact h.trans (finitePositivePower_trace b _ _ _ (by positivity)).symm

/-- The actual unnormalized dual operator, built from the actual covariance. -/
def finiteSchattenNormingOperator (A : H →L[ℝ] H) (q : ℝ) (hq : 2 ≤ q) : H →L[ℝ] H :=
  A * finitePositivePower (A.adjoint * A) (ContinuousLinearMap.isPositive_adjoint_comp_self A)
    ((q - 2) / 2) (by positivity)

/-- The actual trace-pairing operator is the q/2 covariance power. -/
theorem finiteSchattenNormingOperator_pairing_operator (A : H →L[ℝ] H)
    {q : ℝ} (hq : 2 ≤ q) :
    A.adjoint * finiteSchattenNormingOperator A q hq =
      finitePositivePower (A.adjoint * A) (ContinuousLinearMap.isPositive_adjoint_comp_self A)
        (q / 2) (by positivity) := by
  let C := A.adjoint * A
  have hC : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hOne : finitePositivePower C hC 1 (by norm_num) = C := by
    simpa only [Nat.cast_one, pow_one] using finitePositivePower_natCast_eq_pow C hC 1
  change C * finitePositivePower C hC ((q - 2) / 2) (by positivity) = _
  calc
    _ = finitePositivePower C hC 1 (by norm_num) * finitePositivePower C hC ((q - 2) / 2) (by positivity) := by rw [hOne]
    _ = finitePositivePower C hC (1 + (q - 2) / 2) (by positivity) := finitePositivePower_mul_same C hC _ _ _ _
    _ = _ := by congr 1; ring

/-- The true covariance of the constructed dual operator is the actual
(q-1) power of the original covariance. -/
theorem finiteSchattenNormingOperator_covariance (A : H →L[ℝ] H)
    {q : ℝ} (hq : 2 ≤ q) :
    (finiteSchattenNormingOperator A q hq).adjoint * finiteSchattenNormingOperator A q hq =
      finitePositivePower (A.adjoint * A) (ContinuousLinearMap.isPositive_adjoint_comp_self A)
        (q - 1) (by linarith) := by
  let C := A.adjoint * A
  have hC : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self A
  let r := (q - 2) / 2
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  let R := finitePositivePower C hC r hr
  have hRadj : R.adjoint = R := (finitePositivePower_isPositive C hC r hr).isSelfAdjoint.adjoint_eq
  have hOne : finitePositivePower C hC 1 (by norm_num) = C := by
    simpa only [Nat.cast_one, pow_one] using finitePositivePower_natCast_eq_pow C hC 1
  have hD : finiteSchattenNormingOperator A q hq = A * R := rfl
  rw [hD, show (A * R).adjoint = R.adjoint * A.adjoint from ContinuousLinearMap.adjoint_comp A R, hRadj]
  calc
    _ = (R * C) * R := by dsimp only [C]; noncomm_ring
    _ = (R * finitePositivePower C hC 1 (by norm_num)) * R := by rw [hOne]
    _ = finitePositivePower C hC (r + 1) (by positivity) * R := by
      rw [finitePositivePower_mul_same]
    _ = finitePositivePower C hC ((r + 1) + r) (by positivity) := finitePositivePower_mul_same C hC _ _ _ hr
    _ = _ := by congr 1; dsimp only [r]; ring

/-- The actual norming operator realizes the exact q-th Schatten moment in
the genuine finite trace pairing. -/
theorem finiteSchattenNormingOperator_trace (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {q : ℝ} (hq : 2 ≤ q) :
    basisTrace b (A.adjoint * finiteSchattenNormingOperator A q hq) =
      hsSchattenNorm b (finiteOperatorColumns b A) q ^ q := by
  rw [finiteSchattenNormingOperator_pairing_operator]
  exact (finiteSchatten_rpow_eq_covariancePowerTrace b A (by linarith : 0 < q)).symm

/-- The actual dual operator has precisely the expected conjugate Schatten
quantity, including q = 2 and zero singular values. -/
theorem finiteSchattenNormingOperator_schatten (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    hsSchattenNorm b (finiteOperatorColumns b (finiteSchattenNormingOperator A q hq)) p =
      hsSchattenNorm b (finiteOperatorColumns b A) q ^ (q - 1) := by
  have hp0 : 0 < p := hpq.pos
  have hq1 : 0 ≤ q - 1 := by linarith
  let C := A.adjoint * A
  have hC : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hrel : (q - 1) * (p / 2) = q / 2 := by nlinarith [hpq.symm.sub_one_mul_conj]
  have hm := finiteSchatten_rpow_eq_covariancePowerTrace b (finiteSchattenNormingOperator A q hq) hpq.pos
  have hpower : finitePositivePower
      ((finiteSchattenNormingOperator A q hq).adjoint * finiteSchattenNormingOperator A q hq)
      (ContinuousLinearMap.isPositive_adjoint_comp_self _) (p / 2) (by positivity) =
        finitePositivePower C hC (q / 2) (by positivity) := by
    calc
      _ = finitePositivePower (finitePositivePower C hC (q - 1) (by linarith))
          (finitePositivePower_isPositive C hC (q - 1) (by linarith)) (p / 2) (by positivity) :=
        positivePower_congr _ _ (finiteSchattenNormingOperator_covariance A hq) _ _
      _ = finitePositivePower C hC ((q - 1) * (p / 2)) (by positivity) :=
        finitePositivePower_rpow_same C hC _ _ _ _
      _ = _ := by congr 1
  rw [hpower] at hm
  have hbase := finiteSchatten_rpow_eq_covariancePowerTrace b A hpq.symm.pos
  rw [← hbase] at hm
  apply (Real.rpow_left_inj (hsSchattenNorm_nonneg b _ p)
    (Real.rpow_nonneg (hsSchattenNorm_nonneg b _ q) _) hpq.ne_zero).mp
  rw [hm, ← Real.rpow_mul (hsSchattenNorm_nonneg b _ q), hpq.symm.sub_one_mul_conj]

@[simp]
theorem finiteSchattenNormingOperator_zero (q : ℝ) (hq : 2 ≤ q) :
    finiteSchattenNormingOperator (0 : H →L[ℝ] H) q hq = 0 := by
  simp only [finiteSchattenNormingOperator, zero_mul]

/-- At q = 2 the actual norming operator is the original operator, including
its kernel. The zeroth spectral power is the full identity. -/
theorem finiteSchattenNormingOperator_two (A : H →L[ℝ] H) :
    finiteSchattenNormingOperator A 2 le_rfl = A := by
  have hz : finitePositivePower (A.adjoint * A) (ContinuousLinearMap.isPositive_adjoint_comp_self A)
      0 (by norm_num) = 1 := by
    simpa only [Nat.cast_zero, pow_zero] using finitePositivePower_natCast_eq_pow
      (A.adjoint * A) (ContinuousLinearMap.isPositive_adjoint_comp_self A) 0
  simp only [finiteSchattenNormingOperator, sub_self, zero_div, hz, mul_one]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
private theorem finiteNorming_columns_smul (b : HilbertBasis ι ℝ H)
    (a : ℝ) (A : H →L[ℝ] H) :
    finiteOperatorColumns b (a • A) = a • finiteOperatorColumns b A := by
  ext j
  simp only [finiteOperatorColumns_apply, smul_apply, lp.coeFn_smul, Pi.smul_apply]

/-- A genuine unit-ball norming witness is constructed by first normalizing
the q-operator. This avoids any unproved scalar-homogeneity lemma below two. -/
theorem exists_finiteSchatten_norming (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    ∃ D : H →L[ℝ] H, hsSchattenNorm b (finiteOperatorColumns b D) p ≤ 1 ∧
      basisTrace b (A.adjoint * D) = hsSchattenNorm b (finiteOperatorColumns b A) q := by
  let a := hsSchattenNorm b (finiteOperatorColumns b A) q
  have ha0 : 0 ≤ a := hsSchattenNorm_nonneg b _ q
  by_cases ha : a = 0
  · have hA0 : hsSchattenNorm b (finiteOperatorColumns b A) q = 0 := ha
    refine ⟨finiteSchattenNormingOperator A q hq, ?_, ?_⟩
    · rw [finiteSchattenNormingOperator_schatten b A hpq hq, hA0,
        Real.zero_rpow (by linarith : q - 1 ≠ 0)]
      norm_num
    · rw [finiteSchattenNormingOperator_trace b A hq, hA0,
        Real.zero_rpow (by linarith : q ≠ 0)]
  · have haPos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    let A' := a⁻¹ • A
    have hA' : hsSchattenNorm b (finiteOperatorColumns b A') q = 1 := by
      dsimp only [A']
      rw [finiteNorming_columns_smul, hsSchattenNorm_smul b _ _ hq]
      change |a⁻¹| * a = 1
      rw [abs_of_pos (inv_pos.mpr haPos), inv_mul_cancel₀ ha]
    let D := finiteSchattenNormingOperator A' q hq
    have hDnorm : hsSchattenNorm b (finiteOperatorColumns b D) p = 1 := by
      rw [finiteSchattenNormingOperator_schatten b A' hpq hq, hA', Real.one_rpow]
    have hDtrace : basisTrace b (A'.adjoint * D) = 1 := by
      rw [finiteSchattenNormingOperator_trace b A' hq, hA', Real.one_rpow]
    have hAeq : A = a • A' := by
      dsimp only [A']
      rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
    have hcols : finiteOperatorColumns b A = a • finiteOperatorColumns b A' :=
      (congrArg (finiteOperatorColumns b) hAeq).trans (finiteNorming_columns_smul b a A')
    refine ⟨D, hDnorm.le, ?_⟩
    calc
      _ = a * basisTrace b (A'.adjoint * D) := by
        rw [finiteOperatorColumns_trace_inner, hcols, inner_smul_left, conj_trivial,
          ← finiteOperatorColumns_trace_inner]
      _ = a := by rw [hDtrace, mul_one]

/-- The actual scalar trace-pairing values over the actual finite p-unit ball. -/
def finiteSchattenTracePairingValues (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (p : ℝ) : Set ℝ :=
  (fun D : H →L[ℝ] H => basisTrace b (A.adjoint * D)) ''
    {D | hsSchattenNorm b (finiteOperatorColumns b D) p ≤ 1}

/-- The q-Schatten quantity is the attained maximum of the actual trace
pairing over the conjugate p-unit ball. No abstract Schatten norm or duality
structure is assumed. -/
theorem finiteSchattenTracePairing_isGreatest (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    IsGreatest (finiteSchattenTracePairingValues b A p)
      (hsSchattenNorm b (finiteOperatorColumns b A) q) := by
  obtain ⟨D, hD, htrace⟩ := exists_finiteSchatten_norming b A hpq hq
  refine ⟨⟨D, hD, htrace⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  have hsym : basisTrace b (A.adjoint * B) = basisTrace b (B.adjoint * A) := by
    rw [finiteOperatorColumns_trace_inner, finiteOperatorColumns_trace_inner, real_inner_comm]
  calc
    _ = basisTrace b (B.adjoint * A) := hsym
    _ ≤ |basisTrace b (B.adjoint * A)| := le_abs_self _
    _ ≤ hsSchattenNorm b (finiteOperatorColumns b B) p * hsSchattenNorm b (finiteOperatorColumns b A) q :=
      finiteBasisTrace_adjoint_mul_holder b B A hpq hq
    _ ≤ 1 * hsSchattenNorm b (finiteOperatorColumns b A) q :=
      mul_le_mul_of_nonneg_right hB (hsSchattenNorm_nonneg b _ q)
    _ = _ := one_mul _

/-- The attained dual characterization also gives the exact real supremum. -/
theorem finiteSchatten_eq_sSup_tracePairing (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    hsSchattenNorm b (finiteOperatorColumns b A) q = sSup (finiteSchattenTracePairingValues b A p) :=
  (finiteSchattenTracePairing_isGreatest b A hpq hq).csSup_eq.symm

end
end KernelSeq
