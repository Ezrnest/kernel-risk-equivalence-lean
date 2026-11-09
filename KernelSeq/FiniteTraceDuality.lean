import KernelSeq.FiniteSingularApproximation
import KernelSeq.PositiveTraceHolder
import KernelSeq.SchattenTriangle

/-!
# Actual finite trace Holder with arbitrary operator arguments

The right singular basis of the first operator and scalar Holder give the
mixed-exponent trace estimate. The second exponent is at least two, while
the conjugate first exponent may be below two. Positivity of the operator
arguments, a trace norm structure and a duality certificate are not inputs.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/-- The actual image of a sorted right singular unit vector has norm equal
to the corresponding genuine singular value, including zero values. -/
theorem finiteRightSingularBasis_image_norm
    (A : H →L[ℝ] H) (i : Fin (Module.finrank ℝ H)) :
    ‖A (finiteRightSingularBasis A i)‖ = A.toLinearMap.singularValues i := by
  have h := finiteRightSingularBasis_covariance_eigen A i
  have he : ‖finiteRightSingularBasis A i‖ = 1 :=
    (finiteRightSingularBasis A).orthonormal.norm_eq_one i
  have hn : ‖A (finiteRightSingularBasis A i)‖ ^ 2 =
      A.toLinearMap.singularValues i ^ 2 := by
    calc
      _ = inner ℝ (finiteRightSingularBasis A i)
          ((A.adjoint * A) (finiteRightSingularBasis A i)) := by
        rw [mul_apply_eq_comp, A.adjoint_inner_right, real_inner_self_eq_norm_sq]
      _ = _ := by rw [h, inner_smul_right, real_inner_self_eq_norm_sq, he]; ring
  nlinarith [norm_nonneg (A (finiteRightSingularBasis A i)), A.toLinearMap.singularValues_nonneg i]

/-- The actual singular-vector Lp energy is exactly the existing finite
Schatten quantity, for every positive real exponent. -/
theorem finiteRightSingularBasis_lp_eq (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    (∑ i : Fin (Module.finrank ℝ H), ‖A (finiteRightSingularBasis A i)‖ ^ p) ^ (1 / p) =
      hsSchattenNorm b (finiteOperatorColumns b A) p := by
  simp_rw [finiteRightSingularBasis_image_norm]
  rw [← finiteSchatten_rpow_eq_sum_singularValues b A hp, one_div,
    Real.rpow_rpow_inv (hsSchattenNorm_nonneg b _ p) hp.ne']

/-- Genuine trace Holder for arbitrary real finite operators and conjugate
exponents, with the second exponent at least two. The first may be below two. -/
theorem finiteBasisTrace_adjoint_mul_holder (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q) :
    |basisTrace b (A.adjoint * B)| ≤
      hsSchattenNorm b (finiteOperatorColumns b A) p *
        hsSchattenNorm b (finiteOperatorColumns b B) q := by
  let e := (finiteRightSingularBasis A).toHilbertBasis
  have htrace : basisTrace b (A.adjoint * B) =
      ∑ i : Fin (Module.finrank ℝ H), inner ℝ (A (e i)) (B (e i)) := by
    rw [finiteBasisTrace_basis_independent b e]
    simp only [basisTrace, tsum_fintype, mul_apply_eq_comp, A.adjoint_inner_right]
  have hscalar := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) hpq
    (fun i _ => norm_nonneg (A (e i))) (fun i _ => norm_nonneg (B (e i)))
  have hA := finiteRightSingularBasis_lp_eq b A hpq.pos
  have hA' : (∑ i : Fin (Module.finrank ℝ H), ‖A (e i)‖ ^ p) ^ (1 / p) =
      hsSchattenNorm b (finiteOperatorColumns b A) p := by
    simpa only [e, OrthonormalBasis.coe_toHilbertBasis] using hA
  have hB := hs_orthonormal_lp_le b (finiteOperatorColumns b B) hq e e.orthonormal Finset.univ
  simp only [hilbertSchmidtOperator_finiteOperatorColumns] at hB
  calc
    _ = |∑ i : Fin (Module.finrank ℝ H), inner ℝ (A (e i)) (B (e i))| := congrArg abs htrace
    _ ≤ ∑ i : Fin (Module.finrank ℝ H), ‖A (e i)‖ * ‖B (e i)‖ := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => abs_real_inner_le_norm _ _)
    _ ≤ (∑ i : Fin (Module.finrank ℝ H), ‖A (e i)‖ ^ p) ^ (1 / p) *
        (∑ i : Fin (Module.finrank ℝ H), ‖B (e i)‖ ^ q) ^ (1 / q) := hscalar
    _ ≤ _ := by
      rw [hA']
      exact mul_le_mul_of_nonneg_left (by simpa using hB)
        (hsSchattenNorm_nonneg b _ p)

end
end KernelSeq
