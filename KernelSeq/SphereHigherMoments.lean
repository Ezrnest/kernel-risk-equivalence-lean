import KernelSeq.SphereCoordinateRotation
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The true mixed fourth-moment identity on the uniform sphere

A concrete 45-degree orthogonal map, coordinate sign changes and permutations
give the factor three relating a repeated squared coordinate to two distinct
squared coordinates. Every integrability claim follows from continuity on
the compact sphere. No spherical-moment value is assumed.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
theorem integrable_continuous_uniformSphere {f : KernelSphere (EuclideanSpace ℝ ι) → ℝ}
    (hf : Continuous f) : Integrable f uniformSphere := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact
    (μ := uniformSphere (E := EuclideanSpace ℝ ι)) (isCompact_univ : IsCompact (Set.univ : Set (KernelSphere (EuclideanSpace ℝ ι))))

omit [Nonempty ι] in
theorem sphereCoordinateProduct_hadamard_fixed (s : Finset ι) {i j : ι} (hij : i ≠ j)
    (hi : i ∉ s) (hj : j ∉ s) (x : KernelSphere (EuclideanSpace ℝ ι)) :
    sphereCoordinateProduct s (sphereRotation (sphereCoordinateHadamard i j hij) x) =
      sphereCoordinateProduct s x := by
  unfold sphereCoordinateProduct
  apply Finset.prod_congr rfl
  intro k hk
  have hki : k ≠ i := fun h => hi (h ▸ hk)
  have hkj : k ≠ j := fun h => hj (h ▸ hk)
  simp only [sphereRotation_coe, sphereCoordinateHadamard_apply, if_neg hki, if_neg hkj]

omit [Nonempty ι] in
theorem sphereCoordinateProduct_swap_fixed (s : Finset ι) {i j : ι} (hi : i ∉ s) (hj : j ∉ s)
    (x : KernelSphere (EuclideanSpace ℝ ι)) :
    sphereCoordinateProduct s (sphereRotation (sphereCoordinatePermutation (Equiv.swap i j)) x) =
      sphereCoordinateProduct s x := by
  unfold sphereCoordinateProduct
  apply Finset.prod_congr rfl
  intro k hk
  have hki : k ≠ i := fun h => hi (h ▸ hk)
  have hkj : k ≠ j := fun h => hj (h ▸ hk)
  simp only [sphereRotation_coe, sphereCoordinatePermutation_apply, Equiv.symm_swap,
    Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- The exact mixed fourth-moment identity, with any additional squarefree
even-coordinate weight outside the two rotated coordinates. -/
theorem integral_sphere_fourth_mul_product_sq_eq_three (s : Finset ι) {i j : ι}
    (hij : i ≠ j) (hi : i ∉ s) (hj : j ∉ s) :
    (∫ x : KernelSphere (EuclideanSpace ℝ ι),
      (x : EuclideanSpace ℝ ι) i ^ 4 * sphereCoordinateProduct s x ^ 2 ∂uniformSphere) =
      3 * ∫ x : KernelSphere (EuclideanSpace ℝ ι),
        (x : EuclideanSpace ℝ ι) i ^ 2 * (x : EuclideanSpace ℝ ι) j ^ 2 *
          sphereCoordinateProduct s x ^ 2 ∂uniformSphere := by
  let A : KernelSphere (EuclideanSpace ℝ ι) → ℝ := fun x =>
    (x : EuclideanSpace ℝ ι) i ^ 4 * sphereCoordinateProduct s x ^ 2
  let B : KernelSphere (EuclideanSpace ℝ ι) → ℝ := fun x =>
    (x : EuclideanSpace ℝ ι) j ^ 4 * sphereCoordinateProduct s x ^ 2
  let C : KernelSphere (EuclideanSpace ℝ ι) → ℝ := fun x =>
    (x : EuclideanSpace ℝ ι) i ^ 3 * (x : EuclideanSpace ℝ ι) j * sphereCoordinateProduct s x ^ 2
  let D : KernelSphere (EuclideanSpace ℝ ι) → ℝ := fun x =>
    (x : EuclideanSpace ℝ ι) i ^ 2 * (x : EuclideanSpace ℝ ι) j ^ 2 * sphereCoordinateProduct s x ^ 2
  let F : KernelSphere (EuclideanSpace ℝ ι) → ℝ := fun x =>
    (x : EuclideanSpace ℝ ι) i * (x : EuclideanSpace ℝ ι) j ^ 3 * sphereCoordinateProduct s x ^ 2
  have hA : Integrable A uniformSphere := integrable_continuous_uniformSphere (by dsimp [A, sphereCoordinateProduct]; fun_prop)
  have hB : Integrable B uniformSphere := integrable_continuous_uniformSphere (by dsimp [B, sphereCoordinateProduct]; fun_prop)
  have hC : Integrable C uniformSphere := integrable_continuous_uniformSphere (by dsimp [C, sphereCoordinateProduct]; fun_prop)
  have hD : Integrable D uniformSphere := integrable_continuous_uniformSphere (by dsimp [D, sphereCoordinateProduct]; fun_prop)
  have hF : Integrable F uniformSphere := integrable_continuous_uniformSphere (by dsimp [F, sphereCoordinateProduct]; fun_prop)
  have hC0 : (∫ x, C x ∂uniformSphere) = 0 := by
    apply integral_sphere_eq_zero_of_flip i
    intro x
    dsimp only [C]
    simp only [sphereRotation_coe, sphereCoordinateFlip_apply, ite_true, if_neg hij.symm,
      sphereCoordinateProduct_flip, if_neg hi, one_mul]
    ring
  have hF0 : (∫ x, F x ∂uniformSphere) = 0 := by
    apply integral_sphere_eq_zero_of_flip i
    intro x
    dsimp only [F]
    simp only [sphereRotation_coe, sphereCoordinateFlip_apply, ite_true, if_neg hij.symm,
      sphereCoordinateProduct_flip, if_neg hi, one_mul]
    ring
  have hBA : (∫ x, B x ∂uniformSphere) = ∫ x, A x ∂uniformSphere := by
    have hh := (sphereRotation_measurePreserving (sphereCoordinatePermutation (Equiv.swap i j))).integral_comp
      (sphereRotation (sphereCoordinatePermutation (Equiv.swap i j))).measurableEmbedding A
    apply Eq.trans ?_ hh
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [A, B]
      rw [sphereCoordinateProduct_swap_fixed s hi hj]
      simp only [sphereRotation_coe, sphereCoordinatePermutation_apply, Equiv.symm_swap, Equiv.swap_apply_left]
  have hrot := (sphereRotation_measurePreserving (sphereCoordinateHadamard i j hij)).integral_comp
    (sphereRotation (sphereCoordinateHadamard i j hij)).measurableEmbedding A
  have hcoef : (Real.sqrt (1 / 2)) ^ 4 = (1 / 4 : ℝ) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  have hpoly : (fun x => A (sphereRotation (sphereCoordinateHadamard i j hij) x)) =
      (fun x => (1 / 4 : ℝ) * (A x + 4 * C x + 6 * D x + 4 * F x + B x)) := by
    funext x
    dsimp only [A]
    rw [sphereCoordinateProduct_hadamard_fixed s hij hi hj]
    simp only [sphereRotation_coe, sphereCoordinateHadamard_apply, ite_true, mul_pow, hcoef]
    dsimp only [B, C, D, F]
    ring
  rw [hpoly, integral_const_mul] at hrot
  have hAC : Integrable (fun x => A x + 4 * C x) uniformSphere := hA.add (hC.const_mul 4)
  have hACD : Integrable (fun x => A x + 4 * C x + 6 * D x) uniformSphere := hAC.add (hD.const_mul 6)
  have hACDF : Integrable (fun x => A x + 4 * C x + 6 * D x + 4 * F x) uniformSphere := hACD.add (hF.const_mul 4)
  rw [integral_add hACDF hB,
    integral_add hACD (hF.const_mul 4),
    integral_add hAC (hD.const_mul 6),
    integral_add hA (hC.const_mul 4), integral_const_mul, integral_const_mul, integral_const_mul,
    hC0, hF0, hBA] at hrot
  change (∫ x, A x ∂uniformSphere) = 3 * ∫ x, D x ∂uniformSphere
  linarith

end
end KernelSeq
