import KernelSeq.OperatorTrace
import KernelSeq.CovarianceMoments
import Mathlib.LinearAlgebra.Trace

/-!
# Genuine finite operator traces and Bochner expectations

Connects the actual Hilbert-basis trace to Mathlib's algebraic trace and to a
continuous linear functional. Cyclicity, basis independence, finite Loewner
comparison and integral interchange are derived for actual operators. These
are foundations for the still unproved finite matrix Bernstein result.
-/

open MeasureTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual finite trace as a continuous linear functional. -/
def finiteBasisTraceCLM (b : HilbertBasis ι ℝ H) : (H →L[ℝ] H) →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (b i)).comp (ContinuousLinearMap.apply ℝ H (b i))

@[simp]
theorem finiteBasisTraceCLM_apply (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    finiteBasisTraceCLM b A = basisTrace b A := by
  simp only [finiteBasisTraceCLM, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, basisTrace, tsum_fintype]
  rfl

/-- The finite actual diagonal sum is exactly the established algebraic trace. -/
theorem finiteBasisTrace_eq_linearTrace (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    basisTrace b A = LinearMap.trace ℝ H A.toLinearMap := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toOrthonormalBasis.toBasis A.toLinearMap]
  simp only [basisTrace, tsum_fintype, Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.coe_toBasis, HilbertBasis.coe_toOrthonormalBasis,
    ContinuousLinearMap.coe_coe]

theorem finiteBasisTrace_basis_independent (b : HilbertBasis ι ℝ H)
    (a : HilbertBasis κ ℝ H) (A : H →L[ℝ] H) : basisTrace b A = basisTrace a A := by
  rw [finiteBasisTrace_eq_linearTrace b A, finiteBasisTrace_eq_linearTrace a A]

/-- Full cyclicity for actual arbitrary finite operators, not just squares. -/
theorem finiteBasisTrace_mul_comm (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) :
    basisTrace b (A * B) = basisTrace b (B * A) := by
  rw [finiteBasisTrace_eq_linearTrace, finiteBasisTrace_eq_linearTrace,
    ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul]
  exact LinearMap.trace_mul_comm ℝ A.toLinearMap B.toLinearMap

theorem finiteBasisTrace_mul_cycle (b : HilbertBasis ι ℝ H) (A B C : H →L[ℝ] H) :
    basisTrace b (A * B * C) = basisTrace b (C * A * B) := by
  rw [finiteBasisTrace_mul_comm b (A * B) C, mul_assoc]

theorem finiteBasisTrace_norm_bound (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    |basisTrace b A| ≤ (Fintype.card ι : ℝ) * ‖A‖ := by
  rw [basisTrace, tsum_fintype]
  calc
    _ ≤ ∑ i, |inner ℝ (b i) (A (b i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖A‖ := Finset.sum_le_sum (fun i _ => by
      have hn := b.orthonormal.norm_eq_one i
      exact (abs_real_inner_le_norm _ _).trans (by simpa only [hn, one_mul, mul_one] using A.le_opNorm (b i)))
    _ = _ := by simp

theorem finiteBasisTrace_mono (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (hAB : A ≤ B) :
    basisTrace b A ≤ basisTrace b B := by
  simp only [basisTrace, tsum_fintype]
  apply Finset.sum_le_sum
  intro i _
  have h := ((ContinuousLinearMap.le_def A B).mp hAB).inner_nonneg_right (b i)
  simpa only [_root_.sub_apply, inner_sub_right, sub_nonneg] using h

omit [Fintype ι] in
theorem finiteBasisTrace_nonneg (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (hA : A.IsPositive) :
    0 ≤ basisTrace b A := by
  exact tsum_nonneg (fun i => hA.inner_nonneg_right (b i))

variable [CompleteSpace H]

omit [Fintype ι] in
theorem finiteBasisTrace_adjoint (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    basisTrace b A.adjoint = basisTrace b A := by
  apply tsum_congr
  intro i
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]

/-- The product need not be positive, but the trace of a product of two
positive finite operators is genuinely nonnegative. -/
theorem finiteBasisTrace_mul_nonneg (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : A.IsPositive) (hB : B.IsPositive) : 0 ≤ basisTrace b (A * B) := by
  letI : FiniteDimensional ℝ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  have hcB : IsCompactOperator B := isCompactOperator_of_locallyCompactSpace_dom B
  let R := compactRegularizedSqrt B hcB hB 0
  have hRsq : R * R = B := by
    simpa only [zero_smul, add_zero] using compactRegularizedSqrt_sq B hcB hB 0 le_rfl
  have hRadj : R.adjoint = R := compactRegularizedSqrt_isSelfAdjoint B hcB hB 0
  have hpos := hA.conj_adjoint R
  change (R * A * R.adjoint).IsPositive at hpos
  rw [hRadj] at hpos
  rw [← hRsq, ← mul_assoc, finiteBasisTrace_mul_cycle b A R R]
  exact finiteBasisTrace_nonneg b _ hpos

theorem finiteBasisTrace_mul_mono (b : HilbertBasis ι ℝ H) (A B C : H →L[ℝ] H)
    (hA : A.IsPositive) (hBC : B ≤ C) : basisTrace b (A * B) ≤ basisTrace b (A * C) := by
  have hpos := finiteBasisTrace_mul_nonneg b A (C - B) hA ((ContinuousLinearMap.le_def B C).mp hBC)
  rw [mul_sub, basisTrace_sub b _ _ (hasSum_fintype _).summable (hasSum_fintype _).summable] at hpos
  exact sub_nonneg.mp hpos

omit [CompleteSpace H] in
/-- Integrability of the actual trace is inherited from genuine Bochner
integrability of the operator-valued field. -/
theorem integrable_finiteBasisTrace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (b : HilbertBasis ι ℝ H) (Y : Ω → H →L[ℝ] H) (hY : Integrable Y P) :
    Integrable (fun ω => basisTrace b (Y ω)) P := by
  simpa only [finiteBasisTraceCLM_apply] using (finiteBasisTraceCLM b).integrable_comp hY

theorem finiteBasisTrace_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (b : HilbertBasis ι ℝ H) (Y : Ω → H →L[ℝ] H) (hY : Integrable Y P) :
    basisTrace b (∫ ω, Y ω ∂P) = ∫ ω, basisTrace b (Y ω) ∂P := by
  simpa only [finiteBasisTraceCLM_apply] using ((finiteBasisTraceCLM b).integral_comp_comm hY).symm

end
end KernelSeq
