import KernelSeq.UniformSphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual coordinate moments on the uniform sphere

Coordinate sign changes and permutations are concrete orthogonal maps. Their
proved measure invariance yields parity cancellation and squarefree-monomial
orthogonality. These are building blocks for positive polynomial blocks of
the original infinite zonal kernel, not replacement finite-rank models.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def sphereCoordinateFlip (i : ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

omit [Nonempty ι] in
@[simp] theorem sphereCoordinateFlip_apply (i j : ι) (x : EuclideanSpace ℝ ι) :
    sphereCoordinateFlip i x j = if j = i then -x j else x j := by
  simp only [sphereCoordinateFlip, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> rfl

def sphereCoordinateProduct (s : Finset ι) (x : KernelSphere (EuclideanSpace ℝ ι)) : ℝ :=
  ∏ j ∈ s, (x : EuclideanSpace ℝ ι) j

omit [Nonempty ι] [DecidableEq ι] in
theorem sphereCoordinate_abs_le_one (x : KernelSphere (EuclideanSpace ℝ ι)) (i : ι) :
    |(x : EuclideanSpace ℝ ι) i| ≤ 1 := by
  have hh := abs_real_inner_le_norm (EuclideanSpace.basisFun ι ℝ i) (x : EuclideanSpace ℝ ι)
  have hx : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simpa only [EuclideanSpace.basisFun_inner,
    (EuclideanSpace.basisFun ι ℝ).orthonormal.norm_eq_one i, hx, one_mul] using hh

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereCoordinateProduct_continuous (s : Finset ι) :
    Continuous (sphereCoordinateProduct s) := by
  unfold sphereCoordinateProduct
  fun_prop

omit [Nonempty ι] [DecidableEq ι] in
theorem sphereCoordinateProduct_abs_le_one (s : Finset ι) (x : KernelSphere (EuclideanSpace ℝ ι)) :
    |sphereCoordinateProduct s x| ≤ 1 := by
  rw [sphereCoordinateProduct, Finset.abs_prod]
  exact Finset.prod_le_one (fun j _ => abs_nonneg _) (fun j _ => sphereCoordinate_abs_le_one x j)

omit [DecidableEq ι] in
theorem sphereCoordinateProduct_integrable (s : Finset ι) :
    Integrable (sphereCoordinateProduct s) (uniformSphere (E := EuclideanSpace ℝ ι)) := by
  apply (integrable_const (1 : ℝ)).mono' (sphereCoordinateProduct_continuous s).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using sphereCoordinateProduct_abs_le_one s x

omit [Nonempty ι] in
theorem sphereCoordinateProduct_flip (s : Finset ι) (i : ι)
    (x : KernelSphere (EuclideanSpace ℝ ι)) :
    sphereCoordinateProduct s (sphereRotation (sphereCoordinateFlip i) x) =
      (if i ∈ s then (-1 : ℝ) else 1) * sphereCoordinateProduct s x := by
  unfold sphereCoordinateProduct
  simp only [sphereRotation_coe, sphereCoordinateFlip_apply]
  have hh (j : ι) : (if j = i then -(x : EuclideanSpace ℝ ι) j else (x : EuclideanSpace ℝ ι) j) =
      (if j = i then (-1 : ℝ) else 1) * (x : EuclideanSpace ℝ ι) j := by
    split_ifs <;> simp
  simp_rw [hh]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [Finset.prod_ite_eq']

omit [Nonempty ι] in
/-- A truly antisymmetric integrand has zero integral under the actual
uniform sphere measure. No parity/invariance certificate is assumed. -/
theorem integral_sphere_eq_zero_of_flip (i : ι)
    (f : KernelSphere (EuclideanSpace ℝ ι) → ℝ)
    (hflip : ∀ x, f (sphereRotation (sphereCoordinateFlip i) x) = -f x) :
    (∫ x, f x ∂uniformSphere) = 0 := by
  have hh := (sphereRotation_measurePreserving (sphereCoordinateFlip i)).integral_comp
    (sphereRotation (sphereCoordinateFlip i)).measurableEmbedding f
  have heq : (fun x => f (sphereRotation (sphereCoordinateFlip i) x)) = -f :=
    funext hflip
  rw [heq] at hh
  change (∫ x, -f x ∂uniformSphere) = _ at hh
  rw [integral_neg] at hh
  linarith

omit [Nonempty ι] in
/-- Distinct squarefree monomials are genuinely orthogonal as spherical
functions, by a sign flip in their symmetric difference. -/
theorem integral_sphereCoordinateProduct_mul_eq_zero {s t : Finset ι} (hst : s ≠ t) :
    (∫ x, sphereCoordinateProduct s x * sphereCoordinateProduct t x ∂uniformSphere) = 0 := by
  have hh : ¬∀ i, i ∈ s ↔ i ∈ t := fun h => hst (Finset.ext h)
  obtain ⟨i, hi⟩ := not_forall.mp hh
  apply integral_sphere_eq_zero_of_flip i
  intro x
  simp only [sphereCoordinateProduct_flip]
  by_cases his : i ∈ s
  · have hit : i ∉ t := by tauto
    simp [his, hit]
  · have hit : i ∈ t := by tauto
    simp [his, hit]

omit [Nonempty ι] in
theorem integral_sphere_coordinate_mul_eq_zero {i j : ι} (hij : i ≠ j) :
    (∫ x : KernelSphere (EuclideanSpace ℝ ι),
      (x : EuclideanSpace ℝ ι) i * (x : EuclideanSpace ℝ ι) j ∂uniformSphere) = 0 := by
  simpa only [sphereCoordinateProduct, Finset.prod_singleton] using
    integral_sphereCoordinateProduct_mul_eq_zero (s := {i}) (t := {j}) (by simpa using hij)

omit [DecidableEq ι] in
theorem sphereCoordinateProduct_memLp (s : Finset ι) :
    MemLp (sphereCoordinateProduct s) 2 (uniformSphere (E := EuclideanSpace ℝ ι)) := by
  apply MemLp.of_bound (sphereCoordinateProduct_continuous s).aestronglyMeasurable (1 : ℝ)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using sphereCoordinateProduct_abs_le_one s x

omit [DecidableEq ι] in
theorem integrable_sphereCoordinateProduct_mul (s t : Finset ι) :
    Integrable (fun x => sphereCoordinateProduct s x * sphereCoordinateProduct t x)
      (uniformSphere (E := EuclideanSpace ℝ ι)) := by
  have hh : MemLp (sphereCoordinateProduct t * sphereCoordinateProduct s) 1 uniformSphere :=
    (sphereCoordinateProduct_memLp s).mul (sphereCoordinateProduct_memLp t)
  apply (memLp_one_iff_integrable.mp hh).congr
  exact Filter.Eventually.of_forall fun x => by
    change sphereCoordinateProduct t x * sphereCoordinateProduct s x =
      sphereCoordinateProduct s x * sphereCoordinateProduct t x
    ring

omit [DecidableEq ι] in
theorem integrable_sphere_coordinate_sq (i : ι) :
    Integrable (fun x : KernelSphere (EuclideanSpace ℝ ι) => (x : EuclideanSpace ℝ ι) i ^ 2)
      uniformSphere := by
  simpa only [sphereCoordinateProduct, Finset.prod_singleton, ← pow_two] using
    integrable_sphereCoordinateProduct_mul ({i} : Finset ι) {i}

def sphereCoordinatePermutation (e : ι ≃ ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

omit [Nonempty ι] [DecidableEq ι] in
@[simp] theorem sphereCoordinatePermutation_apply (e : ι ≃ ι) (x : EuclideanSpace ℝ ι) (i : ι) :
    sphereCoordinatePermutation e x i = x (e.symm i) := rfl

omit [Nonempty ι] in
theorem integral_sphere_coordinate_sq_eq (i j : ι) :
    (∫ x : KernelSphere (EuclideanSpace ℝ ι), (x : EuclideanSpace ℝ ι) i ^ 2 ∂uniformSphere) =
      ∫ x : KernelSphere (EuclideanSpace ℝ ι), (x : EuclideanSpace ℝ ι) j ^ 2 ∂uniformSphere := by
  have hh := (sphereRotation_measurePreserving (sphereCoordinatePermutation (Equiv.swap i j))).integral_comp
    (sphereRotation (sphereCoordinatePermutation (Equiv.swap i j))).measurableEmbedding
    (fun x : KernelSphere (EuclideanSpace ℝ ι) => (x : EuclideanSpace ℝ ι) i ^ 2)
  simpa only [sphereRotation_coe, sphereCoordinatePermutation_apply, Equiv.symm_swap, Equiv.swap_apply_left] using hh.symm

/-- The exact second moment is proved from permutation invariance and the
pointwise sphere equation, not imposed as a spherical moment certificate. -/
theorem integral_sphere_coordinate_sq (i : ι) :
    (∫ x : KernelSphere (EuclideanSpace ℝ ι), (x : EuclideanSpace ℝ ι) i ^ 2 ∂uniformSphere) =
      1 / (Fintype.card ι : ℝ) := by
  have hsum (x : KernelSphere (EuclideanSpace ℝ ι)) :
      (∑ j, (x : EuclideanSpace ℝ ι) j ^ 2) = 1 := by
    have hi := real_inner_self_eq_norm_sq (x : EuclideanSpace ℝ ι)
    have hx : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    simpa only [PiLp.inner_apply, Real.inner_apply, ← pow_two, hx, one_pow] using hi
  have htotal : (∑ j, ∫ x : KernelSphere (EuclideanSpace ℝ ι),
      (x : EuclideanSpace ℝ ι) j ^ 2 ∂uniformSphere) = 1 := by
    rw [← integral_finsetSum _ (fun j _ => integrable_sphere_coordinate_sq j)]
    simp only [hsum, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hh : (Fintype.card ι : ℝ) * (∫ x : KernelSphere (EuclideanSpace ℝ ι),
      (x : EuclideanSpace ℝ ι) i ^ 2 ∂uniformSphere) = 1 := by
    simpa only [← integral_sphere_coordinate_sq_eq i, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] using htotal
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))).2
  simpa only [mul_comm] using hh

end
end KernelSeq
