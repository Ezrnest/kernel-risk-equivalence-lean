import KernelSeq.FiniteFieldMarcinkiewicz
import KernelSeq.FiniteSchattenNorming

/-!
# Actual normalized finite-field Schatten duality

The pairing is the normalized average of the genuine finite trace. Actual
covariance powers construct the pointwise norming field; normalizing the
whole field at exponent q ≥ 2 produces an attained conjugate-unit-ball
duality. No norm structure or scalar-homogeneity theorem below two is
assumed. Empty probability index types are included.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {Ω ι H : Type*} [Fintype Ω] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/-- Actual normalized finite-field trace pairing. -/
def finiteFieldTracePairing (b : HilbertBasis ι ℝ H)
    (A B : Ω → H →L[ℝ] H) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, basisTrace b ((A ω).adjoint * B ω)

omit [FiniteDimensional ℝ H] in
theorem finiteFieldTracePairing_comm (b : HilbertBasis ι ℝ H)
    (A B : Ω → H →L[ℝ] H) : finiteFieldTracePairing b A B = finiteFieldTracePairing b B A := by
  unfold finiteFieldTracePairing
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [finiteOperatorColumns_trace_inner, finiteOperatorColumns_trace_inner, real_inner_comm]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
private theorem fieldDuality_columns_smul (b : HilbertBasis ι ℝ H)
    (a : ℝ) (A : H →L[ℝ] H) :
    finiteOperatorColumns b (a • A) = a • finiteOperatorColumns b A := by
  ext j
  simp only [finiteOperatorColumns_apply, smul_apply, lp.coeFn_smul, Pi.smul_apply]

omit [FiniteDimensional ℝ H] in
theorem finiteFieldTracePairing_smul_left (b : HilbertBasis ι ℝ H)
    (a : ℝ) (A B : Ω → H →L[ℝ] H) :
    finiteFieldTracePairing b (a • A) B = a * finiteFieldTracePairing b A B := by
  unfold finiteFieldTracePairing
  simp only [Pi.smul_apply, finiteOperatorColumns_trace_inner, fieldDuality_columns_smul,
    inner_smul_left, conj_trivial]
  rw [← Finset.mul_sum]
  ring

/-- Actual averaged trace Holder. The first exponent may be below two;
the outer field exponent matches each Schatten exponent. -/
theorem finiteFieldTracePairing_holder (b : HilbertBasis ι ℝ H)
    (A B : Ω → H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    |finiteFieldTracePairing b A B| ≤ finiteFieldSchattenNorm b A p * finiteFieldSchattenNorm b B q := by
  let w : ℝ := (Fintype.card Ω : ℝ)⁻¹
  have hw : 0 ≤ w := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hscalar := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) hpq
    (fun ω _ => hsSchattenNorm_nonneg b (finiteOperatorColumns b (A ω)) p)
    (fun ω _ => hsSchattenNorm_nonneg b (finiteOperatorColumns b (B ω)) q)
  have hwpow : w ^ p⁻¹ * w ^ q⁻¹ = w := by
    rw [← Real.rpow_add_of_nonneg hw (inv_nonneg.mpr hpq.pos.le)
      (inv_nonneg.mpr hpq.symm.pos.le), hpq.inv_add_inv_eq_one, Real.rpow_one]
  have hsA : 0 ≤ ∑ ω, hsSchattenNorm b (finiteOperatorColumns b (A ω)) p ^ p :=
    Finset.sum_nonneg fun ω _ => Real.rpow_nonneg (hsSchattenNorm_nonneg b _ p) p
  have hsB : 0 ≤ ∑ ω, hsSchattenNorm b (finiteOperatorColumns b (B ω)) q ^ q :=
    Finset.sum_nonneg fun ω _ => Real.rpow_nonneg (hsSchattenNorm_nonneg b _ q) q
  calc
    _ = w * |∑ ω, basisTrace b ((A ω).adjoint * B ω)| := by
      rw [finiteFieldTracePairing, abs_mul, abs_of_nonneg hw]
    _ ≤ w * ∑ ω, hsSchattenNorm b (finiteOperatorColumns b (A ω)) p *
        hsSchattenNorm b (finiteOperatorColumns b (B ω)) q := by
      apply mul_le_mul_of_nonneg_left _ hw
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ =>
        finiteBasisTrace_adjoint_mul_holder b (A ω) (B ω) hpq hq)
    _ ≤ w * ((∑ ω, hsSchattenNorm b (finiteOperatorColumns b (A ω)) p ^ p) ^ (1 / p) *
        (∑ ω, hsSchattenNorm b (finiteOperatorColumns b (B ω)) q ^ q) ^ (1 / q)) :=
      mul_le_mul_of_nonneg_left hscalar hw
    _ = _ := by
      unfold finiteFieldSchattenNorm finiteFieldSchattenMoment
      rw [Real.mul_rpow hw hsA, Real.mul_rpow hw hsB]
      simp only [one_div]
      rw [show (w ^ p⁻¹ * (∑ ω, hsSchattenNorm b (finiteOperatorColumns b (A ω)) p ^ p) ^ p⁻¹) *
          (w ^ q⁻¹ * (∑ ω, hsSchattenNorm b (finiteOperatorColumns b (B ω)) q ^ q) ^ q⁻¹) =
        (w ^ p⁻¹ * w ^ q⁻¹) * ((∑ ω, hsSchattenNorm b (finiteOperatorColumns b (A ω)) p ^ p) ^ p⁻¹ *
          (∑ ω, hsSchattenNorm b (finiteOperatorColumns b (B ω)) q ^ q) ^ q⁻¹) by ring,
        hwpow]

omit [FiniteDimensional ℝ H] in
/-- Only the q ≥ 2 homogeneity result is used for global normalization. -/
theorem finiteFieldSchattenMoment_smul (b : HilbertBasis ι ℝ H)
    (a : ℝ) (A : Ω → H →L[ℝ] H) {q : ℝ} (hq : 2 ≤ q) :
    finiteFieldSchattenMoment b (a • A) q = |a| ^ q * finiteFieldSchattenMoment b A q := by
  unfold finiteFieldSchattenMoment
  simp only [Pi.smul_apply, fieldDuality_columns_smul, hsSchattenNorm_smul b _ _ hq]
  simp_rw [Real.mul_rpow (abs_nonneg a) (hsSchattenNorm_nonneg b _ q)]
  rw [← Finset.mul_sum]
  ring

omit [FiniteDimensional ℝ H] in
theorem finiteFieldSchattenNorm_smul (b : HilbertBasis ι ℝ H)
    (a : ℝ) (A : Ω → H →L[ℝ] H) {q : ℝ} (hq : 2 ≤ q) :
    finiteFieldSchattenNorm b (a • A) q = |a| * finiteFieldSchattenNorm b A q := by
  unfold finiteFieldSchattenNorm
  rw [finiteFieldSchattenMoment_smul b a A hq,
    Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) q) (finiteFieldSchattenMoment_nonneg b A q),
    Real.rpow_rpow_inv (abs_nonneg a) (by linarith : q ≠ 0)]

/-- Actual pointwise covariance-power norming field. -/
def finiteFieldNormingOperator (A : Ω → H →L[ℝ] H) (q : ℝ) (hq : 2 ≤ q) : Ω → H →L[ℝ] H :=
  fun ω => finiteSchattenNormingOperator (A ω) q hq

theorem finiteFieldNormingOperator_pairing (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {q : ℝ} (hq : 2 ≤ q) :
    finiteFieldTracePairing b A (finiteFieldNormingOperator A q hq) = finiteFieldSchattenMoment b A q := by
  unfold finiteFieldTracePairing finiteFieldSchattenMoment finiteFieldNormingOperator
  simp_rw [finiteSchattenNormingOperator_trace b _ hq]

theorem finiteFieldNormingOperator_moment (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    finiteFieldSchattenMoment b (finiteFieldNormingOperator A q hq) p =
      finiteFieldSchattenMoment b A q := by
  unfold finiteFieldSchattenMoment finiteFieldNormingOperator
  simp_rw [finiteSchattenNormingOperator_schatten b _ hpq hq,
    ← Real.rpow_mul (hsSchattenNorm_nonneg b _ q), hpq.symm.sub_one_mul_conj]

/-- An actual field in the conjugate unit ball attains the full field
q-norm. The zero-norm and empty-index cases require no division. -/
theorem exists_finiteFieldSchatten_norming (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    ∃ D : Ω → H →L[ℝ] H, finiteFieldSchattenNorm b D p ≤ 1 ∧
      finiteFieldTracePairing b A D = finiteFieldSchattenNorm b A q := by
  let a := finiteFieldSchattenNorm b A q
  have ha0 : 0 ≤ a := finiteFieldSchattenNorm_nonneg b A q
  by_cases ha : a = 0
  · have hmoment : finiteFieldSchattenMoment b A q = 0 := by
      rw [← finiteFieldSchattenNorm_rpow b A hpq.symm.pos]
      change a ^ q = 0
      rw [ha, Real.zero_rpow hpq.symm.ne_zero]
    refine ⟨finiteFieldNormingOperator A q hq, ?_, ?_⟩
    · rw [finiteFieldSchattenNorm, finiteFieldNormingOperator_moment b A hpq hq,
        hmoment, Real.zero_rpow (inv_ne_zero hpq.ne_zero)]
      norm_num
    · rw [finiteFieldNormingOperator_pairing b A hq, hmoment]
      exact ha.symm
  · have haPos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    let A' : Ω → H →L[ℝ] H := a⁻¹ • A
    have hA' : finiteFieldSchattenNorm b A' q = 1 := by
      rw [show A' = a⁻¹ • A from rfl, finiteFieldSchattenNorm_smul b _ A hq]
      change |a⁻¹| * a = 1
      rw [abs_of_pos (inv_pos.mpr haPos), inv_mul_cancel₀ ha]
    have hmoment : finiteFieldSchattenMoment b A' q = 1 := by
      rw [← finiteFieldSchattenNorm_rpow b A' hpq.symm.pos, hA', Real.one_rpow]
    let D := finiteFieldNormingOperator A' q hq
    have hDn : finiteFieldSchattenNorm b D p = 1 := by
      rw [finiteFieldSchattenNorm, finiteFieldNormingOperator_moment b A' hpq hq,
        hmoment, Real.one_rpow]
    have hDt : finiteFieldTracePairing b A' D = 1 := by
      rw [finiteFieldNormingOperator_pairing b A' hq, hmoment]
    have hAeq : A = a • A' := by
      dsimp only [A']
      rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
    refine ⟨D, hDn.le, ?_⟩
    calc
      _ = a * finiteFieldTracePairing b A' D := by rw [hAeq, finiteFieldTracePairing_smul_left]
      _ = a := by rw [hDt, mul_one]

/-- Actual trace-pairing values over the actual normalized p-unit ball. -/
def finiteFieldTracePairingValues (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) (p : ℝ) : Set ℝ :=
  (fun D : Ω → H →L[ℝ] H => finiteFieldTracePairing b A D) ''
    {D | finiteFieldSchattenNorm b D p ≤ 1}

/-- True attained normalized field duality, including empty index types. -/
theorem finiteFieldTracePairing_isGreatest (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    IsGreatest (finiteFieldTracePairingValues b A p) (finiteFieldSchattenNorm b A q) := by
  obtain ⟨D, hD, htrace⟩ := exists_finiteFieldSchatten_norming b A hpq hq
  refine ⟨⟨D, hD, htrace⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  calc
    _ = finiteFieldTracePairing b B A := finiteFieldTracePairing_comm b A B
    _ ≤ |finiteFieldTracePairing b B A| := le_abs_self _
    _ ≤ finiteFieldSchattenNorm b B p * finiteFieldSchattenNorm b A q :=
      finiteFieldTracePairing_holder b B A hpq hq
    _ ≤ 1 * finiteFieldSchattenNorm b A q :=
      mul_le_mul_of_nonneg_right hB (finiteFieldSchattenNorm_nonneg b A q)
    _ = _ := one_mul _

theorem finiteFieldSchattenNorm_eq_sSup_tracePairing (b : HilbertBasis ι ℝ H)
    (A : Ω → H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    finiteFieldSchattenNorm b A q = sSup (finiteFieldTracePairingValues b A p) :=
  (finiteFieldTracePairing_isGreatest b A hpq hq).csSup_eq.symm

/-- A genuine trace-selfadjoint field map transfers its actual matching-p
bound to the conjugate matching-q bound by the constructed norming field. -/
theorem finiteFieldSchattenNorm_dual_transfer (b : HilbertBasis ι ℝ H)
    (T : (Ω → H →L[ℝ] H) →ₗ[ℝ] (Ω → H →L[ℝ] H)) {p q C : ℝ}
    (hpq : p.HolderConjugate q) (hq : 2 ≤ q) (hC : 0 ≤ C)
    (hself : ∀ A B, finiteFieldTracePairing b (T A) B = finiteFieldTracePairing b A (T B))
    (hbound : ∀ B, finiteFieldSchattenNorm b (T B) p ≤ C * finiteFieldSchattenNorm b B p)
    (A : Ω → H →L[ℝ] H) :
    finiteFieldSchattenNorm b (T A) q ≤ C * finiteFieldSchattenNorm b A q := by
  obtain ⟨D, hDn, hDt⟩ := exists_finiteFieldSchatten_norming b (T A) hpq hq
  calc
    _ = finiteFieldTracePairing b (T A) D := hDt.symm
    _ = finiteFieldTracePairing b A (T D) := hself A D
    _ = finiteFieldTracePairing b (T D) A := finiteFieldTracePairing_comm b A (T D)
    _ ≤ |finiteFieldTracePairing b (T D) A| := le_abs_self _
    _ ≤ finiteFieldSchattenNorm b (T D) p * finiteFieldSchattenNorm b A q :=
      finiteFieldTracePairing_holder b (T D) A hpq hq
    _ ≤ (C * finiteFieldSchattenNorm b D p) * finiteFieldSchattenNorm b A q :=
      mul_le_mul_of_nonneg_right (hbound D) (finiteFieldSchattenNorm_nonneg b A q)
    _ ≤ (C * 1) * finiteFieldSchattenNorm b A q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDn hC)
        (finiteFieldSchattenNorm_nonneg b A q)
    _ = _ := by rw [mul_one]

/-- Actual weak-(1,1), strong-(2,2) interpolation followed by the genuine
field duality. The transform's weak estimate and trace selfadjointness
remain explicit inputs; this theorem does not assume their application. -/
theorem finiteFieldMarcinkiewicz_dual_norm_le (b : HilbertBasis ι ℝ H)
    (T : (Ω → H →L[ℝ] H) →ₗ[ℝ] (Ω → H →L[ℝ] H)) {K L p q : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hpq : p.HolderConjugate q) (hq : 2 ≤ q) (hp2 : p < 2)
    (hweak : ∀ A t, 0 < t → t * finiteFieldSingularCount (T A) t ≤
      K * finiteFieldSchattenMoment b A 1)
    (hstrong : ∀ A, finiteFieldSchattenMoment b (T A) 2 ≤
      L ^ 2 * finiteFieldSchattenMoment b A 2)
    (hself : ∀ A B, finiteFieldTracePairing b (T A) B = finiteFieldTracePairing b A (T B))
    (A : Ω → H →L[ℝ] H) :
    finiteFieldSchattenNorm b (T A) q ≤
      (2 * K * p / (p - 1) + 4 * L ^ 2 * p / (2 - p)) ^ p⁻¹ *
        finiteFieldSchattenNorm b A q := by
  have hp1 : 1 < p := hpq.lt
  have hC : 0 ≤ (2 * K * p / (p - 1) + 4 * L ^ 2 * p / (2 - p)) ^ p⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  exact finiteFieldSchattenNorm_dual_transfer b T hpq hq hC hself
    (fun B => finiteFieldMarcinkiewicz_norm_le b T hK hL hweak hstrong B hp1 hp2) A

end
end KernelSeq
