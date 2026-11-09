import KernelSeq.SphereInnerPower

/-!
# Actual differentiation of weighted spherical power integrals

A finite binomial expansion constructs the complete translation polynomial
with actual integral coefficients. Its genuine polynomial derivative proves
the needed differentiated moment identity. Differentiation under the integral
is a conclusion, never a supplied certificate.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def weightedSpherePowerMoment (g : KernelSphere (EuclideanSpace ℝ ι) → ℝ)
    (n : ℕ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫ y : KernelSphere (EuclideanSpace ℝ ι),
    g y * inner ℝ x (y : EuclideanSpace ℝ ι)^n ∂uniformSphere

def weightedSphereLinePolynomial (g : KernelSphere (EuclideanSpace ℝ ι) → ℝ)
    (n : ℕ) (x v : EuclideanSpace ℝ ι) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n+1), Polynomial.C ((n.choose k : ℝ) *
    (∫ y : KernelSphere (EuclideanSpace ℝ ι),
      g y * (inner ℝ x (y : EuclideanSpace ℝ ι)^(n-k) * inner ℝ v (y : EuclideanSpace ℝ ι)^k)
      ∂uniformSphere)) * Polynomial.X^k

omit [DecidableEq ι] in
theorem weightedSphereLinePolynomial_eval
    (g : KernelSphere (EuclideanSpace ℝ ι) → ℝ) (hg : Continuous g)
    (n : ℕ) (x v : EuclideanSpace ℝ ι) (c : ℝ) :
    (weightedSphereLinePolynomial g n x v).eval c = weightedSpherePowerMoment g n (x + c • v) := by
  have hint (k : ℕ) : Integrable (fun y : KernelSphere (EuclideanSpace ℝ ι) =>
      g y * (inner ℝ x (y : EuclideanSpace ℝ ι)^(n-k) * inner ℝ v (y : EuclideanSpace ℝ ι)^k))
      uniformSphere := integrable_continuous_uniformSphere (by fun_prop)
  have hpoint (y : KernelSphere (EuclideanSpace ℝ ι)) :
      g y * inner ℝ (x + c • v) (y : EuclideanSpace ℝ ι)^n =
      ∑ k ∈ Finset.range (n+1), ((n.choose k : ℝ) * c^k) *
        (g y * (inner ℝ x (y : EuclideanSpace ℝ ι)^(n-k) * inner ℝ v (y : EuclideanSpace ℝ ι)^k)) := by
    rw [inner_add_left, inner_smul_left, conj_trivial, add_comm, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    ring
  unfold weightedSphereLinePolynomial weightedSpherePowerMoment
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  calc
    _ = ∑ k ∈ Finset.range (n+1), ∫ y : KernelSphere (EuclideanSpace ℝ ι),
        ((n.choose k : ℝ) * c^k) *
          (g y * (inner ℝ x (y : EuclideanSpace ℝ ι)^(n-k) * inner ℝ v (y : EuclideanSpace ℝ ι)^k))
        ∂uniformSphere := by
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_const_mul]
      ring
    _ = ∫ y : KernelSphere (EuclideanSpace ℝ ι),
        ∑ k ∈ Finset.range (n+1), ((n.choose k : ℝ) * c^k) *
          (g y * (inner ℝ x (y : EuclideanSpace ℝ ι)^(n-k) * inner ℝ v (y : EuclideanSpace ℝ ι)^k))
        ∂uniformSphere :=
      (integral_finsetSum _ (fun k _ => (hint k).const_mul _)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun y => (hpoint y).symm)

omit [DecidableEq ι] [Nonempty ι] in
theorem weightedSphereLinePolynomial_coeff
    (g : KernelSphere (EuclideanSpace ℝ ι) → ℝ) {n k : ℕ} (hk : k ≤ n) (x v : EuclideanSpace ℝ ι) :
    (weightedSphereLinePolynomial g n x v).coeff k = (n.choose k : ℝ) *
      (∫ y : KernelSphere (EuclideanSpace ℝ ι),
        g y * (inner ℝ x (y : EuclideanSpace ℝ ι)^(n-k) * inner ℝ v (y : EuclideanSpace ℝ ι)^k)
        ∂uniformSphere) := by
  simp only [weightedSphereLinePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

omit [DecidableEq ι] in
/-- The actual weighted integral has the expected line derivative at zero,
proved from its constructed finite polynomial and genuine coefficients. -/
theorem hasDerivAt_weightedSpherePower_add_smul
    (g : KernelSphere (EuclideanSpace ℝ ι) → ℝ) (hg : Continuous g)
    (n : ℕ) (x v : EuclideanSpace ℝ ι) :
    HasDerivAt (fun c : ℝ => weightedSpherePowerMoment g (n+1) (x + c • v))
      (((n : ℝ)+1) * weightedSpherePowerMoment
        (fun y => g y * inner ℝ v (y : EuclideanSpace ℝ ι)) n x) 0 := by
  let P := weightedSphereLinePolynomial g (n+1) x v
  have hP := P.hasDerivAt 0
  have hfun : (fun c : ℝ => P.eval c) =
      (fun c : ℝ => weightedSpherePowerMoment g (n+1) (x + c • v)) :=
    funext fun c => weightedSphereLinePolynomial_eval g hg (n+1) x v c
  rw [hfun] at hP
  have hd : P.derivative.eval 0 = ((n : ℝ)+1) * weightedSpherePowerMoment
      (fun y => g y * inner ℝ v (y : EuclideanSpace ℝ ι)) n x := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp only [Nat.cast_zero, zero_add, mul_one]
    rw [weightedSphereLinePolynomial_coeff g (by omega : 1 ≤ n+1)]
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_one]
    apply congrArg (fun a : ℝ => ((n : ℝ)+1) * a)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only [weightedSpherePowerMoment]
      ring
  rwa [hd] at hP

end
end KernelSeq
