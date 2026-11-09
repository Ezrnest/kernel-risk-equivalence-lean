import KernelSeq.SchattenFour
import KernelSeq.CompactCalculus

/-!
# Genuine finite positive spectral-power order

A shorter route than a sorted min--max theorem suffices for the power-sum
order needed here. Scalar spectral Jensen, the actual Loewner quadratic-form
inequality, and finite basis trace invariance prove monotonicity of actual
positive spectral power sums. No variational or eigenvalue-order certificate
is assumed. The sorted finite eigenvalue sum is identified with the same actual
compact spectral power sum, and the actual positive Schatten quantities are
Loewner monotone for all real exponents at least one. Pointwise sorted
eigenvalue monotonicity and a general product-power inequality are not asserted.
-/

open scoped BigOperators

namespace KernelSeq

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/-- The actual compact spectral index is finite in a finite-dimensional space;
this includes the full zero eigenspace. -/
theorem finite_compactSpectralIndex (T : H →L[ℝ] H) (hT : T.IsPositive) :
    Finite (CompactSpectralIndex T) :=
  (compactEigenbasis T (isCompactOperator_of_locallyCompactSpace_dom T) hT.isSymmetric).orthonormal.linearIndependent.finite

/-- The actual positive spectral power, constructed from the existing compact
calculus. Its scalar profile bound follows from `r ≥ 0`. -/
def finitePositivePower (T : H →L[ℝ] H) (hT : T.IsPositive) (r : ℝ) (hr : 0 ≤ r) : H →L[ℝ] H :=
  compactSpectralMultiplier T (isCompactOperator_of_locallyCompactSpace_dom T) hT
    (fun t => t ^ r) (‖T‖ ^ r) (Real.rpow_nonneg (norm_nonneg T) r)
    (fun t ht => by
      rw [abs_of_nonneg (Real.rpow_nonneg ht.1 r)]
      exact Real.rpow_le_rpow ht.1 ht.2 hr)

/-- The actual power acts on every eigenvector by the actual scalar power. -/
theorem finitePositivePower_eigen (T : H →L[ℝ] H) (hT : T.IsPositive)
    (r : ℝ) (hr : 0 ≤ r) {v : H} {t : ℝ} (hv : T v = t • v) :
    finitePositivePower T hT r hr v = t ^ r • v :=
  compactSpectralMultiplier_eigen T _ hT _ _ _ _ hv

section Trace

variable {ι : Type*} [Fintype ι]

/-- Actual positive power trace equals the already defined actual compact
spectral power sum. Its finiteness is derived from finite-dimensionality. -/
theorem finitePositivePower_trace (b : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)
    (hT : T.IsPositive) (r : ℝ) (hr : 0 ≤ r) :
    basisTrace b (finitePositivePower T hT r hr) = compactPositivePowerSum T r := by
  letI : Finite (CompactSpectralIndex T) := finite_compactSpectralIndex T hT
  letI := Fintype.ofFinite (CompactSpectralIndex T)
  let e := compactEigenbasis T (isCompactOperator_of_locallyCompactSpace_dom T) hT.isSymmetric
  rw [finiteBasisTrace_basis_independent b e]
  unfold basisTrace compactPositivePowerSum
  apply tsum_congr
  intro i
  have he : T (e i) = i.1 • e i := compactEigenbasis_eigen T _ hT.isSymmetric i
  rw [finitePositivePower_eigen T hT r hr he]
  simp only [inner_smul_right, real_inner_self_eq_norm_sq, e.orthonormal.norm_eq_one, one_pow, mul_one]

/-- The actual power's quadratic form in the actual compact eigenbasis. -/
theorem finitePositivePower_quadratic (T : H →L[ℝ] H) (hT : T.IsPositive)
    (r : ℝ) (hr : 0 ≤ r) (x : H) :
    inner ℝ x (finitePositivePower T hT r hr x) =
      ∑' i : CompactSpectralIndex T, i.1 ^ r *
        (compactEigenbasis T (isCompactOperator_of_locallyCompactSpace_dom T) hT.isSymmetric).repr x i ^ 2 := by
  let e := compactEigenbasis T (isCompactOperator_of_locallyCompactSpace_dom T) hT.isSymmetric
  rw [← e.tsum_inner_mul_inner x (finitePositivePower T hT r hr x)]
  apply tsum_congr
  intro i
  have hleft : inner ℝ x (e i) = e.repr x i := by
    rw [HilbertBasis.repr_apply_apply, real_inner_comm]
  have hcoef : e.repr (finitePositivePower T hT r hr x) i = i.1 ^ r * e.repr x i := by
    simp only [e, finitePositivePower, compactSpectralMultiplier_repr]
  have hright : inner ℝ (e i) (finitePositivePower T hT r hr x) = i.1 ^ r * e.repr x i := by
    simpa only [HilbertBasis.repr_apply_apply] using hcoef
  rw [hleft, hright]
  change e.repr x i * (i.1 ^ r * e.repr x i) = i.1 ^ r * (e.repr x i) ^ 2
  ring

/-- Genuine spectral Jensen for a finite positive operator and every real
power at least one. No min--max characterization is required. -/
theorem finitePositivePower_jensen (T : H →L[ℝ] H) (hT : T.IsPositive)
    {r : ℝ} (hr : 1 ≤ r) {x : H} (hx : ‖x‖ = 1) :
    (inner ℝ x (T x)) ^ r ≤ inner ℝ x (finitePositivePower T hT r (by linarith) x) := by
  letI : Finite (CompactSpectralIndex T) := finite_compactSpectralIndex T hT
  letI := Fintype.ofFinite (CompactSpectralIndex T)
  let e := compactEigenbasis T (isCompactOperator_of_locallyCompactSpace_dom T) hT.isSymmetric
  let w : CompactSpectralIndex T → ℝ := fun i => e.repr x i ^ 2
  let t : CompactSpectralIndex T → ℝ := fun i => i.1
  have hw1 : ∑' i, w i = 1 := by
    rw [← hilbertBasis_norm_sq_eq_tsum e x, hx]
    norm_num
  have hq := compact_quadratic_hasSum T (isCompactOperator_of_locallyCompactSpace_dom T) hT x
  have henergy : (∑' i, w i * t i) = inner ℝ x (T x) := by
    rw [← hq.tsum_eq]
    apply tsum_congr
    intro i
    dsimp only [w, t, e]
    ring
  have hj := rpow_tsum_probability_le w t hr (fun i => sq_nonneg _)
    (compactEigenvalue_nonneg T (isCompactOperator_of_locallyCompactSpace_dom T) hT) (hasSum_fintype _).summable hw1
    (hasSum_fintype _).summable (hasSum_fintype _).summable
  rw [henergy] at hj
  rw [finitePositivePower_quadratic]
  simpa only [w, t, mul_comm] using hj

/-- Actual positive spectral-power traces are monotone under actual Loewner
order for every real power at least one. -/
theorem finitePositivePower_trace_mono (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : A.IsPositive) (hB : B.IsPositive) (hAB : A ≤ B) {r : ℝ} (hr : 1 ≤ r) :
    basisTrace b (finitePositivePower A hA r (by linarith)) ≤
      basisTrace b (finitePositivePower B hB r (by linarith)) := by
  letI : Finite (CompactSpectralIndex A) := finite_compactSpectralIndex A hA
  letI := Fintype.ofFinite (CompactSpectralIndex A)
  let a := compactEigenbasis A (isCompactOperator_of_locallyCompactSpace_dom A) hA.isSymmetric
  rw [finiteBasisTrace_basis_independent b a, finiteBasisTrace_basis_independent b a]
  simp only [basisTrace, tsum_fintype]
  apply Finset.sum_le_sum
  intro i _
  have hi := a.orthonormal.norm_eq_one i
  have he : A (a i) = i.1 • a i := compactEigenbasis_eigen A _ hA.isSymmetric i
  have heval : inner ℝ (a i) (A (a i)) = i.1 := by
    rw [he]
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, hi, one_pow, mul_one]
  have hle : i.1 ≤ inner ℝ (a i) (B (a i)) := by
    have h := ((ContinuousLinearMap.le_def A B).mp hAB).inner_nonneg_right (a i)
    simpa only [sub_apply, inner_sub_right, heval, sub_nonneg] using h
  rw [finitePositivePower_eigen A hA r (by linarith) he]
  simp only [inner_smul_right, real_inner_self_eq_norm_sq, hi, one_pow, mul_one]
  exact (Real.rpow_le_rpow (compactEigenvalue_nonneg A (isCompactOperator_of_locallyCompactSpace_dom A) hA i) hle (by linarith)).trans
    (finitePositivePower_jensen B hB hr hi)

end Trace

/-- A genuine actual compact spectral power-sum order theorem, derived from
quadratic-form order and spectral Jensen. -/
theorem compactPositivePowerSum_mono_finite (A B : H →L[ℝ] H)
    (hA : A.IsPositive) (hB : B.IsPositive) (hAB : A ≤ B) {r : ℝ} (hr : 1 ≤ r) :
    compactPositivePowerSum A r ≤ compactPositivePowerSum B r := by
  let b := (hA.isSymmetric.eigenvectorBasis (rfl : Module.finrank ℝ H = Module.finrank ℝ H)).toHilbertBasis
  rw [← finitePositivePower_trace b A hA r (by linarith),
    ← finitePositivePower_trace b B hB r (by linarith)]
  exact finitePositivePower_trace_mono b A B hA hB hAB hr

/-- The genuine finite eigenvalues supplied by Mathlib are sorted in
nonincreasing order; no chosen ordering certificate is an input. -/
def finitePositiveEigenvalues (T : H →L[ℝ] H) (hT : T.IsPositive) :
    Fin (Module.finrank ℝ H) → ℝ := hT.isSymmetric.eigenvalues rfl

omit [CompleteSpace H] in
theorem finitePositiveEigenvalues_antitone (T : H →L[ℝ] H) (hT : T.IsPositive) :
    Antitone (finitePositiveEigenvalues T hT) := hT.isSymmetric.eigenvalues_antitone rfl

/-- Actual compact spectral power sums agree with the power sums of the
actual sorted finite eigenvalues, including multiplicity and the zero eigenspace. -/
theorem compactPositivePowerSum_eq_sorted_finite (T : H →L[ℝ] H) (hT : T.IsPositive)
    (r : ℝ) (hr : 0 ≤ r) :
    compactPositivePowerSum T r = ∑ i, finitePositiveEigenvalues T hT i ^ r := by
  let e := hT.isSymmetric.eigenvectorBasis (rfl : Module.finrank ℝ H = Module.finrank ℝ H)
  let b := e.toHilbertBasis
  rw [← finitePositivePower_trace b T hT r hr]
  simp only [basisTrace, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  have he : T (b i) = finitePositiveEigenvalues T hT i • b i := by
    simpa only [b, e, OrthonormalBasis.coe_toHilbertBasis, finitePositiveEigenvalues,
      RCLike.ofReal_real_eq_id, id_eq, ContinuousLinearMap.coe_coe] using
      hT.isSymmetric.apply_eigenvectorBasis (rfl : Module.finrank ℝ H = Module.finrank ℝ H) i
  rw [finitePositivePower_eigen T hT r hr he]
  simp only [inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow, mul_one]

omit [FiniteDimensional ℝ H] in
/-- A positive actual operator has an actual positive square. -/
theorem finitePositive_square_isPositive (A : H →L[ℝ] H) (hA : A.IsPositive) :
    (A ^ 2).IsPositive := by
  have h := ContinuousLinearMap.isPositive_adjoint_comp_self A
  simpa only [← ContinuousLinearMap.mul_def, hA.isSelfAdjoint.adjoint_eq, ← pow_two] using h

/-- Powering the actual square by `r/2` equals the actual positive power `r`.
The proof uses every actual eigenvector, rather than a singular-value certificate. -/
theorem finitePositivePower_square (A : H →L[ℝ] H) (hA : A.IsPositive) (r : ℝ) (hr : 0 ≤ r) :
    finitePositivePower (A ^ 2) (finitePositive_square_isPositive A hA) (r / 2) (by positivity) =
      finitePositivePower A hA r hr := by
  let e := compactEigenbasis A (isCompactOperator_of_locallyCompactSpace_dom A) hA.isSymmetric
  apply continuousLinearMap_eq_of_hilbertBasis e
  intro i
  have he : A (e i) = i.1 • e i := compactEigenbasis_eigen A _ hA.isSymmetric i
  have he₂ : (A ^ 2) (e i) = i.1 ^ 2 • e i := by
    rw [pow_two, mul_apply_eq_comp, he, map_smul, he, smul_smul, pow_two]
  rw [finitePositivePower_eigen _ _ _ _ he₂, finitePositivePower_eigen _ _ _ _ he]
  congr 1
  have hi := compactEigenvalue_nonneg A (isCompactOperator_of_locallyCompactSpace_dom A) hA i
  calc
    (i.1 ^ 2) ^ (r / 2) = i.1 ^ ((2 : ℝ) * (r / 2)) := by rw [Real.rpow_mul hi, Real.rpow_two]
    _ = i.1 ^ r := by congr 1; ring

section Schatten

variable {ι : Type*} [Fintype ι]

/-- The actual finite Schatten power is the actual positive spectral-power
trace, for every positive real exponent. -/
theorem finiteSchatten_rpow_eq_positivePowerTrace (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) (hA : A.IsPositive) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b A) p ^ p =
      basisTrace b (finitePositivePower A hA p hp.le) := by
  have hcov : hsSingularCovariance b (finiteOperatorColumns b A) = A ^ 2 := by
    simp only [hsSingularCovariance, hilbertSchmidtOperator_finiteOperatorColumns,
      hA.isSelfAdjoint.adjoint_eq, ← ContinuousLinearMap.mul_def, pow_two]
  calc
    _ = compactPositivePowerSum (hsSingularCovariance b (finiteOperatorColumns b A)) (p / 2) :=
      hsSchattenNorm_rpow b _ hp
    _ = compactPositivePowerSum (A ^ 2) (p / 2) := by rw [hcov]
    _ = basisTrace b (finitePositivePower (A ^ 2) (finitePositive_square_isPositive A hA) (p / 2) (by positivity)) :=
      (finitePositivePower_trace b _ _ _ (by positivity)).symm
    _ = _ := by rw [finitePositivePower_square]

/-- Genuine finite positive Schatten monotonicity under actual Loewner order,
for every real exponent at least one. No sorted-eigenvalue-order, min--max,
or Schatten order theorem is an input. -/
theorem finiteSchatten_positive_mono (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (hA : A.IsPositive) (hB : B.IsPositive) (hAB : A ≤ B)
    {p : ℝ} (hp : 1 ≤ p) :
    hsSchattenNorm b (finiteOperatorColumns b A) p ≤ hsSchattenNorm b (finiteOperatorColumns b B) p := by
  have hp0 : 0 < p := by linarith
  apply (Real.rpow_le_rpow_iff (hsSchattenNorm_nonneg b _ p) (hsSchattenNorm_nonneg b _ p) hp0).mp
  rw [finiteSchatten_rpow_eq_positivePowerTrace b A hA hp0,
    finiteSchatten_rpow_eq_positivePowerTrace b B hB hp0]
  exact finitePositivePower_trace_mono b A B hA hB hAB hp

/-- Natural powers of the actual positive spectral calculus are the actual
operator powers, including the zeroth power on a zero-dimensional space. -/
theorem finitePositivePower_natCast_eq_pow (A : H →L[ℝ] H) (hA : A.IsPositive) (n : ℕ) :
    finitePositivePower A hA (n : ℝ) (Nat.cast_nonneg n) = A ^ n := by
  let e := compactEigenbasis A (isCompactOperator_of_locallyCompactSpace_dom A) hA.isSymmetric
  apply continuousLinearMap_eq_of_hilbertBasis e
  intro i
  have he : A (e i) = i.1 • e i := compactEigenbasis_eigen A _ hA.isSymmetric i
  rw [finitePositivePower_eigen A hA (n : ℝ) (Nat.cast_nonneg n) he, Real.rpow_natCast]
  symm
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, he, smul_smul, pow_succ']
    congr 1
    ring

/-- Genuine trace monotonicity for actual positive operator powers, with no
operator-monotonicity claim about the powers themselves. -/
theorem finiteBasisTrace_positive_pow_mono (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (hA : A.IsPositive) (hB : B.IsPositive) (hAB : A ≤ B)
    {n : ℕ} (hn : 1 ≤ n) : basisTrace b (A ^ n) ≤ basisTrace b (B ^ n) := by
  rw [← finitePositivePower_natCast_eq_pow A hA n, ← finitePositivePower_natCast_eq_pow B hB n]
  apply finitePositivePower_trace_mono b A B hA hB hAB
  exact_mod_cast hn

/-- The proved positive power-sum order also holds for the actual sorted
finite eigenvalue lists, with every multiplicity counted. -/
theorem finitePositiveEigenvalues_power_sum_mono (A B : H →L[ℝ] H)
    (hA : A.IsPositive) (hB : B.IsPositive) (hAB : A ≤ B) {r : ℝ} (hr : 1 ≤ r) :
    (∑ i, finitePositiveEigenvalues A hA i ^ r) ≤ ∑ i, finitePositiveEigenvalues B hB i ^ r := by
  rw [← compactPositivePowerSum_eq_sorted_finite A hA r (by linarith),
    ← compactPositivePowerSum_eq_sorted_finite B hB r (by linarith)]
  exact compactPositivePowerSum_mono_finite A B hA hB hAB hr

end Schatten
end
end KernelSeq
