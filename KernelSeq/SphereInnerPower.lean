import KernelSeq.SphereHigherMoments
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Actual radial power moments on the sphere

These are integral identities under the genuine uniform surface probability.
They are a foundation for identifying exact polynomial and zonal eigenspaces;
no Funk--Hecke, harmonic block or eigenvalue identity is an input.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def sphereInnerPowerMoment (n : ℕ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫ y : KernelSphere (EuclideanSpace ℝ ι), inner ℝ x (y : EuclideanSpace ℝ ι)^n ∂uniformSphere

omit [DecidableEq ι] in
theorem integrable_sphereInnerPower (n : ℕ) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y : KernelSphere (EuclideanSpace ℝ ι) =>
      inner ℝ x (y : EuclideanSpace ℝ ι)^n) uniformSphere :=
  integrable_continuous_uniformSphere (by fun_prop)

omit [DecidableEq ι] in
theorem sphereInnerPowerMoment_zero_degree (x : EuclideanSpace ℝ ι) :
    sphereInnerPowerMoment 0 x = 1 := by simp [sphereInnerPowerMoment]

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereInnerPowerMoment_smul (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ ι) :
    sphereInnerPowerMoment n (c • x) = c^n * sphereInnerPowerMoment n x := by
  unfold sphereInnerPowerMoment
  simp only [inner_smul_left, conj_trivial, mul_pow]
  exact integral_const_mul _ _

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereInnerPowerMoment_rotation (n : ℕ)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) :
    sphereInnerPowerMoment n (U x) = sphereInnerPowerMoment n x := by
  have hh := (sphereRotation_measurePreserving U).integral_comp (sphereRotation U).measurableEmbedding
    (fun y : KernelSphere (EuclideanSpace ℝ ι) => inner ℝ (U x) (y : EuclideanSpace ℝ ι)^n)
  unfold sphereInnerPowerMoment
  calc
    _ = ∫ y : KernelSphere (EuclideanSpace ℝ ι),
        inner ℝ (U x) ((sphereRotation U y : KernelSphere (EuclideanSpace ℝ ι)) : EuclideanSpace ℝ ι)^n
        ∂uniformSphere := hh.symm
    _ = _ := by simp only [sphereRotation_coe, U.inner_map_map]

omit [DecidableEq ι] in
/-- Actual radiality follows from an explicitly constructed orthogonal map,
including x=0 and degree zero. -/
theorem sphereInnerPowerMoment_radial (n : ℕ) (x : EuclideanSpace ℝ ι)
    (pole : KernelSphere (EuclideanSpace ℝ ι)) :
    sphereInnerPowerMoment n x = ‖x‖^n * sphereInnerPowerMoment n (pole : EuclideanSpace ℝ ι) := by
  by_cases hx : x = 0
  · subst x
    cases n with
    | zero => simp [sphereInnerPowerMoment_zero_degree]
    | succ n => simp [sphereInnerPowerMoment]
  let u : KernelSphere (EuclideanSpace ℝ ι) :=
    ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx)⟩
  obtain ⟨U, hU⟩ := exists_sphereRotation_eq u pole
  have hrad : sphereInnerPowerMoment n (NormedSpace.normalize x) =
      sphereInnerPowerMoment n (pole : EuclideanSpace ℝ ι) := by
    have hh := sphereInnerPowerMoment_rotation n U (u : EuclideanSpace ℝ ι)
    have hu := congrArg Subtype.val hU
    change U (u : EuclideanSpace ℝ ι) = (pole : EuclideanSpace ℝ ι) at hu
    rw [hu] at hh
    exact hh.symm
  calc
    _ = sphereInnerPowerMoment n (‖x‖ • NormedSpace.normalize x) := by rw [NormedSpace.norm_smul_normalize]
    _ = _ := by rw [sphereInnerPowerMoment_smul, hrad]

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereInnerPowerMoment_odd (r : ℕ) (x : EuclideanSpace ℝ ι) :
    sphereInnerPowerMoment (2*r+1) x = 0 := by
  have hh := sphereInnerPowerMoment_rotation (2*r+1) (LinearIsometryEquiv.neg ℝ) x
  have hneg : (LinearIsometryEquiv.neg ℝ) x = (-1 : ℝ) • x := by simp
  rw [hneg, sphereInnerPowerMoment_smul] at hh
  have hsign : (-1 : ℝ)^(2*r+1) = -1 := by simp [pow_add, pow_mul]
  rw [hsign] at hh
  linarith

/-- Actual mixed moments used as coefficients of the line polynomial. -/
def sphereMixedPowerMoment (a b : ℕ) (x v : EuclideanSpace ℝ ι) : ℝ :=
  ∫ y : KernelSphere (EuclideanSpace ℝ ι),
    inner ℝ x (y : EuclideanSpace ℝ ι)^a * inner ℝ v (y : EuclideanSpace ℝ ι)^b ∂uniformSphere

omit [DecidableEq ι] in
theorem integrable_sphereMixedPower (a b : ℕ) (x v : EuclideanSpace ℝ ι) :
    Integrable (fun y : KernelSphere (EuclideanSpace ℝ ι) =>
      inner ℝ x (y : EuclideanSpace ℝ ι)^a * inner ℝ v (y : EuclideanSpace ℝ ι)^b) uniformSphere :=
  integrable_continuous_uniformSphere (by fun_prop)

omit [DecidableEq ι] in
/-- Binomial expansion is a genuine finite integral identity, giving a
polynomial in the translation parameter without a derivative-under-integral
certificate. -/
theorem sphereInnerPowerMoment_add_smul (n : ℕ) (x v : EuclideanSpace ℝ ι) (c : ℝ) :
    sphereInnerPowerMoment n (x + c • v) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * c^k * sphereMixedPowerMoment (n-k) k x v := by
  have hpoint (y : KernelSphere (EuclideanSpace ℝ ι)) :
      inner ℝ (x + c • v) (y : EuclideanSpace ℝ ι)^n =
        ∑ k ∈ Finset.range (n+1),
          ((n.choose k : ℝ) * c^k) *
            (inner ℝ x (y : EuclideanSpace ℝ ι)^(n-k) * inner ℝ v (y : EuclideanSpace ℝ ι)^k) := by
    rw [inner_add_left, inner_smul_left, conj_trivial, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    ring
  unfold sphereInnerPowerMoment sphereMixedPowerMoment
  calc
    _ = ∫ y : KernelSphere (EuclideanSpace ℝ ι),
        ∑ k ∈ Finset.range (n+1),
          ((n.choose k : ℝ) * c^k) *
            (inner ℝ x (y : EuclideanSpace ℝ ι)^(n-k) * inner ℝ v (y : EuclideanSpace ℝ ι)^k)
        ∂uniformSphere := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ k ∈ Finset.range (n+1),
        ∫ y : KernelSphere (EuclideanSpace ℝ ι),
          ((n.choose k : ℝ) * c^k) *
            (inner ℝ x (y : EuclideanSpace ℝ ι)^(n-k) * inner ℝ v (y : EuclideanSpace ℝ ι)^k)
        ∂uniformSphere := by
      exact integral_finsetSum _ (fun k _ => (integrable_sphereMixedPower (n-k) k x v).const_mul _)
    _ = _ := by simp only [integral_const_mul]


/-- A genuine real polynomial whose coefficients are actual integrals. -/
def sphereLineMomentPolynomial (n : ℕ) (x v : EuclideanSpace ℝ ι) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n+1),
    Polynomial.C ((n.choose k : ℝ) * sphereMixedPowerMoment (n-k) k x v) * Polynomial.X^k

omit [DecidableEq ι] in
theorem sphereLineMomentPolynomial_eval (n : ℕ) (x v : EuclideanSpace ℝ ι) (c : ℝ) :
    (sphereLineMomentPolynomial n x v).eval c = sphereInnerPowerMoment n (x + c • v) := by
  rw [sphereInnerPowerMoment_add_smul]
  simp only [sphereLineMomentPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereLineMomentPolynomial_coeff {n k : ℕ} (hk : k ≤ n) (x v : EuclideanSpace ℝ ι) :
    (sphereLineMomentPolynomial n x v).coeff k =
      (n.choose k : ℝ) * sphereMixedPowerMoment (n-k) k x v := by
  simp only [sphereLineMomentPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

omit [DecidableEq ι] in
/-- The entire actual even line-moment polynomial is radial. Extracting its
coefficients gives genuine coordinate moment recurrences, rather than a
spectral-block assumption. -/
theorem sphereLineMomentPolynomial_even (r : ℕ) (x v : EuclideanSpace ℝ ι)
    (pole : KernelSphere (EuclideanSpace ℝ ι)) :
    sphereLineMomentPolynomial (2*r) x v =
      Polynomial.C (sphereInnerPowerMoment (2*r) (pole : EuclideanSpace ℝ ι)) *
        (Polynomial.C (‖x‖^2) + Polynomial.C (2 * inner ℝ x v) * Polynomial.X +
          Polynomial.C (‖v‖^2) * Polynomial.X^2)^r := by
  apply Polynomial.funext
  intro c
  rw [sphereLineMomentPolynomial_eval, sphereInnerPowerMoment_radial (pole := pole)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X]
  have hn : ‖x + c • v‖^2 = ‖x‖^2 + (2 * inner ℝ x v) * c + ‖v‖^2 * c^2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs]
    nlinarith [sq_abs c]
  rw [pow_mul, hn]
  ring


end
end KernelSeq
