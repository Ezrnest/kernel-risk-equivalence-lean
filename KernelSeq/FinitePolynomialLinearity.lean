import KernelSeq.FinitePolynomialLpContinuity

/-!
# Actual coefficient linearity of finite matrix polynomials

The concrete finite HS polynomial is an actual linear map of its scalar
multiplier values. Finite sums and scalar modal weights are therefore exact
column identities, rather than reconstruction hypotheses.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ν ι H : Type*} [Fintype ν] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def weightedTrigColumnsLinearMap (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ)
    (X Y : ν → H →L[ℝ] H) (θ : ℝ × ℝ) : (ν → ℝ) →ₗ[ℝ] HilbertSchmidtColumns ι H :=
  ∑ i, (LinearMap.proj i : (ν → ℝ) →ₗ[ℝ] ℝ).smulRight
    (Real.cos (integerPlanePhase (k i) θ) • finiteOperatorColumns b (X i) +
      Real.sin (integerPlanePhase (k i) θ) • finiteOperatorColumns b (Y i))

@[simp]
theorem weightedTrigColumnsLinearMap_apply (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ)
    (X Y : ν → H →L[ℝ] H) (θ : ℝ × ℝ) (a : ν → ℝ) :
    weightedTrigColumnsLinearMap b k X Y θ a = weightedTrigColumns b k X Y a θ := by
  simp only [weightedTrigColumnsLinearMap, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, smul_add, smul_smul, weightedTrigColumns]

theorem weightedTrigColumns_smul (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ)
    (X Y : ν → H →L[ℝ] H) (θ : ℝ × ℝ) (a : ν → ℝ) (r : ℝ) :
    weightedTrigColumns b k X Y (fun i => r * a i) θ = r • weightedTrigColumns b k X Y a θ := by
  simp only [weightedTrigColumns, Finset.smul_sum, smul_add, smul_smul, mul_assoc]

theorem weightedTrigColumns_sum {J : Type*} (s : Finset J)
    (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ) (X Y : ν → H →L[ℝ] H)
    (θ : ℝ × ℝ) (a : J → ν → ℝ) :
    weightedTrigColumns b k X Y (fun i => ∑ j ∈ s, a j i) θ =
      ∑ j ∈ s, weightedTrigColumns b k X Y (a j) θ := by
  have hfun : (fun i => ∑ j ∈ s, a j i) = ∑ j ∈ s, a j := by
    funext i
    simp only [Finset.sum_apply]
  rw [hfun]
  have h := map_sum (weightedTrigColumnsLinearMap b k X Y θ) a s
  simpa only [weightedTrigColumnsLinearMap_apply] using h

theorem weightedTrigColumns_weighted_sum {J : Type*} (s : Finset J)
    (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ) (X Y : ν → H →L[ℝ] H)
    (θ : ℝ × ℝ) (a : J → ν → ℝ) (w : J → ℝ) :
    weightedTrigColumns b k X Y (fun i => ∑ j ∈ s, w j * a j i) θ =
      ∑ j ∈ s, w j • weightedTrigColumns b k X Y (a j) θ := by
  rw [weightedTrigColumns_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact weightedTrigColumns_smul b k X Y θ (a j) (w j)

end
end KernelSeq
