import KernelSeq.FiniteSingularOrder
import Mathlib.Analysis.MeanInequalities

/-!
# Actual finite positive trace Holder inequalities

The actual positive spectral powers are those constructed in
`FiniteSingularOrder`. Diagonalizing the first positive operator, applying the
scalar finite Holder inequality, and using actual spectral Jensen for the
second operator proves trace Holder without a trace-ideal certificate.
Zero spectral values, zero energies, and an empty finite basis are retained.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/-- Actual nonnegative spectral powers are genuinely positive operators. -/
theorem finitePositivePower_isPositive (A : H →L[ℝ] H) (hA : A.IsPositive)
    (r : ℝ) (hr : 0 ≤ r) : (finitePositivePower A hA r hr).IsPositive := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
  unfold finitePositivePower compactSpectralMultiplier
  apply hilbertDiagonal_nonneg
  intro i
  exact Real.rpow_nonneg
    (compactEigenvalue_nonneg A (isCompactOperator_of_locallyCompactSpace_dom A) hA i) r

omit [Fintype ι] in
/-- The finite trace of an actual positive power is nonnegative, including
the degenerate zero-dimensional and zero-energy cases. -/
theorem finitePositivePower_trace_nonneg (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) (hA : A.IsPositive) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ basisTrace b (finitePositivePower A hA r hr) :=
  finiteBasisTrace_nonneg b _ (finitePositivePower_isPositive A hA r hr)

/-- Diagonalizing an actual positive first factor gives the exact trace
product with an arbitrary second operator. The entire zero eigenspace is
included in the actual spectral index. -/
theorem finiteBasisTrace_positive_mul_eq_eigen_sum (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (hA : A.IsPositive) :
    basisTrace b (A * B) =
      ∑' i : CompactSpectralIndex A, i.1 *
        inner ℝ (compactEigenbasis A (isCompactOperator_of_locallyCompactSpace_dom A) hA.isSymmetric i)
          (B (compactEigenbasis A (isCompactOperator_of_locallyCompactSpace_dom A) hA.isSymmetric i)) := by
  letI : Finite (CompactSpectralIndex A) := finite_compactSpectralIndex A hA
  letI := Fintype.ofFinite (CompactSpectralIndex A)
  let e := compactEigenbasis A (isCompactOperator_of_locallyCompactSpace_dom A) hA.isSymmetric
  rw [finiteBasisTrace_basis_independent b e]
  unfold basisTrace
  apply tsum_congr
  intro i
  change inner ℝ (e i) (A (B (e i))) = i.1 * inner ℝ (e i) (B (e i))
  rw [← hA.inner_left_eq_inner_right, compactEigenbasis_eigen A _ hA.isSymmetric i]
  simp only [inner_smul_left, conj_trivial]
  rfl

/-- Actual positive trace Young, derived from the scalar Young inequality
and spectral Jensen, without a prior trace Holder premise. -/
theorem finiteBasisTrace_positive_young (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (hA : A.IsPositive) (hB : B.IsPositive)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    basisTrace b (A * B) ≤
      basisTrace b (finitePositivePower A hA p hpq.pos.le) / p +
      basisTrace b (finitePositivePower B hB q hpq.symm.pos.le) / q := by
  letI : Finite (CompactSpectralIndex A) := finite_compactSpectralIndex A hA
  letI := Fintype.ofFinite (CompactSpectralIndex A)
  let e := compactEigenbasis A (isCompactOperator_of_locallyCompactSpace_dom A) hA.isSymmetric
  rw [finiteBasisTrace_basis_independent b e, finiteBasisTrace_basis_independent b e,
    finiteBasisTrace_basis_independent b e]
  simp only [basisTrace, tsum_fintype]
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have he : A (e i) = i.1 • e i := compactEigenbasis_eigen A _ hA.isSymmetric i
  have hmul : inner ℝ (e i) ((A * B) (e i)) = i.1 * inner ℝ (e i) (B (e i)) := by
    rw [mul_apply_eq_comp, ← hA.inner_left_eq_inner_right, he, inner_smul_left]
    simp only [conj_trivial]
  have hpower : inner ℝ (e i) (finitePositivePower A hA p hpq.pos.le (e i)) = i.1 ^ p := by
    rw [finitePositivePower_eigen A hA p hpq.pos.le he]
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, e.orthonormal.norm_eq_one, one_pow, mul_one]
  rw [hmul, hpower]
  have hy := Real.young_inequality_of_nonneg
    (compactEigenvalue_nonneg A (isCompactOperator_of_locallyCompactSpace_dom A) hA i)
    (hB.inner_nonneg_right (e i)) hpq
  have hj := finitePositivePower_jensen B hB hpq.symm.lt.le (e.orthonormal.norm_eq_one i)
  exact hy.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hj hpq.symm.pos.le))

/-- Genuine finite positive trace Holder for arbitrary conjugate real
exponents. No inverse-energy or nonzero-operator assumption is required. -/
theorem finiteBasisTrace_positive_holder (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (hA : A.IsPositive) (hB : B.IsPositive)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    basisTrace b (A * B) ≤
      basisTrace b (finitePositivePower A hA p hpq.pos.le) ^ (1 / p) *
        basisTrace b (finitePositivePower B hB q hpq.symm.pos.le) ^ (1 / q) := by
  letI : Finite (CompactSpectralIndex A) := finite_compactSpectralIndex A hA
  letI := Fintype.ofFinite (CompactSpectralIndex A)
  let e := compactEigenbasis A (isCompactOperator_of_locallyCompactSpace_dom A) hA.isSymmetric
  let f : CompactSpectralIndex A → ℝ := fun i => i.1
  let g : CompactSpectralIndex A → ℝ := fun i => inner ℝ (e i) (B (e i))
  have hf : ∀ i ∈ (Finset.univ : Finset (CompactSpectralIndex A)), 0 ≤ f i :=
    fun i _ => compactEigenvalue_nonneg A (isCompactOperator_of_locallyCompactSpace_dom A) hA i
  have hg : ∀ i ∈ (Finset.univ : Finset (CompactSpectralIndex A)), 0 ≤ g i :=
    fun i _ => hB.inner_nonneg_right (e i)
  have hApower : basisTrace b (finitePositivePower A hA p hpq.pos.le) = ∑ i, f i ^ p := by
    simpa only [compactPositivePowerSum, tsum_fintype, f] using finitePositivePower_trace b A hA p hpq.pos.le
  have hBpower : (∑ i, g i ^ q) ≤ basisTrace b (finitePositivePower B hB q hpq.symm.pos.le) := by
    rw [finiteBasisTrace_basis_independent b e]
    simp only [basisTrace, tsum_fintype]
    exact Finset.sum_le_sum (fun i _ => finitePositivePower_jensen B hB hpq.symm.lt.le
      (e.orthonormal.norm_eq_one i))
  have hscalar := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) hpq hf hg
  have hleft : basisTrace b (A * B) = ∑ i, f i * g i := by
    simpa only [tsum_fintype, f, g, e] using finiteBasisTrace_positive_mul_eq_eigen_sum b A B hA
  rw [← hApower] at hscalar
  calc
    _ = ∑ i, f i * g i := hleft
    _ ≤ basisTrace b (finitePositivePower A hA p hpq.pos.le) ^ (1 / p) *
        (∑ i, g i ^ q) ^ (1 / q) := hscalar
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hg i (Finset.mem_univ i)) q))
        hBpower hpq.symm.one_div_nonneg)
      (Real.rpow_nonneg (finitePositivePower_trace_nonneg b A hA p hpq.pos.le) _)

/-- The same actual positive trace Holder estimate in terms of the existing
finite spectral Schatten quantities, for all real conjugate exponents. -/
theorem finiteBasisTrace_positive_holder_schatten (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (hA : A.IsPositive) (hB : B.IsPositive)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    basisTrace b (A * B) ≤
      hsSchattenNorm b (finiteOperatorColumns b A) p *
        hsSchattenNorm b (finiteOperatorColumns b B) q := by
  have h := finiteBasisTrace_positive_holder b A B hA hB hpq
  rw [← finiteSchatten_rpow_eq_positivePowerTrace b A hA hpq.pos,
    ← finiteSchatten_rpow_eq_positivePowerTrace b B hB hpq.symm.pos] at h
  simpa only [one_div, Real.rpow_rpow_inv (hsSchattenNorm_nonneg b _ p) hpq.ne_zero,
    Real.rpow_rpow_inv (hsSchattenNorm_nonneg b _ q) hpq.symm.ne_zero] using h

end
end KernelSeq
