import KernelSeq.SphereHigherMoments

/-!
# Exact squarefree moments of the actual uniform sphere

The recurrence is proved from the sphere equation, coordinate permutations,
and the genuine mixed fourth-moment identity. It gives the actual moment
`1/[d(d+2)...(d+2m-2)]` for every m-element coordinate set, without a moment
or spherical-spectrum certificate.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def squarefreeSphereMoment (s : Finset ι) : ℝ :=
  ∫ x : KernelSphere (EuclideanSpace ℝ ι), sphereCoordinateProduct s x ^ 2 ∂uniformSphere

omit [DecidableEq ι] in
theorem squarefreeSphereMoment_empty : squarefreeSphereMoment (∅ : Finset ι) = 1 := by
  simp [squarefreeSphereMoment, sphereCoordinateProduct]

omit [Nonempty ι] in
theorem squarefreeSphereMoment_insert {s : Finset ι} {i : ι} (hi : i ∉ s) :
    squarefreeSphereMoment (insert i s) =
      ∫ x : KernelSphere (EuclideanSpace ℝ ι),
        (x : EuclideanSpace ℝ ι) i ^ 2 * sphereCoordinateProduct s x ^ 2 ∂uniformSphere := by
  unfold squarefreeSphereMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [sphereCoordinateProduct, Finset.prod_insert hi, mul_pow]

omit [DecidableEq ι] in
private theorem sphere_coordinate_sq_product_integrable (s : Finset ι) (j : ι) :
    Integrable (fun x : KernelSphere (EuclideanSpace ℝ ι) =>
      (x : EuclideanSpace ℝ ι) j ^ 2 * sphereCoordinateProduct s x ^ 2) uniformSphere :=
  integrable_continuous_uniformSphere (by unfold sphereCoordinateProduct; fun_prop)

omit [Nonempty ι] in
private theorem moment_new_coordinate_eq (s : Finset ι) {i j : ι} (hi : i ∉ s) (hj : j ∉ s) :
    (∫ x : KernelSphere (EuclideanSpace ℝ ι),
      (x : EuclideanSpace ℝ ι) j ^ 2 * sphereCoordinateProduct s x ^ 2 ∂uniformSphere) =
      squarefreeSphereMoment (insert i s) := by
  rw [squarefreeSphereMoment_insert hi]
  have hh := (sphereRotation_measurePreserving (sphereCoordinatePermutation (Equiv.swap i j))).integral_comp
    (sphereRotation (sphereCoordinatePermutation (Equiv.swap i j))).measurableEmbedding
    (fun x : KernelSphere (EuclideanSpace ℝ ι) =>
      (x : EuclideanSpace ℝ ι) i ^ 2 * sphereCoordinateProduct s x ^ 2)
  apply Eq.trans ?_ hh
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [sphereCoordinateProduct_swap_fixed s hi hj]
    simp only [sphereRotation_coe, sphereCoordinatePermutation_apply, Equiv.symm_swap, Equiv.swap_apply_left]

private theorem moment_repeated_coordinate_eq (s : Finset ι) {i j : ι} (hi : i ∉ s) (hj : j ∈ s) :
    (∫ x : KernelSphere (EuclideanSpace ℝ ι),
      (x : EuclideanSpace ℝ ι) j ^ 2 * sphereCoordinateProduct s x ^ 2 ∂uniformSphere) =
      3 * squarefreeSphereMoment (insert i s) := by
  have hij : j ≠ i := fun h => hi (h ▸ hj)
  have hi' : i ∉ s.erase j := fun h => hi (Finset.mem_of_mem_erase h)
  have hj' : j ∉ s.erase j := Finset.notMem_erase _ _
  have heq (x : KernelSphere (EuclideanSpace ℝ ι)) :
      sphereCoordinateProduct s x =
        (x : EuclideanSpace ℝ ι) j * sphereCoordinateProduct (s.erase j) x := by
    conv_lhs => rw [← Finset.insert_erase hj]
    simp only [sphereCoordinateProduct, Finset.prod_insert hj']
  calc
    _ = ∫ x : KernelSphere (EuclideanSpace ℝ ι),
        (x : EuclideanSpace ℝ ι) j ^ 4 * sphereCoordinateProduct (s.erase j) x ^ 2 ∂uniformSphere := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by dsimp only; rw [heq]; ring
    _ = 3 * ∫ x : KernelSphere (EuclideanSpace ℝ ι),
        (x : EuclideanSpace ℝ ι) j ^ 2 * (x : EuclideanSpace ℝ ι) i ^ 2 *
          sphereCoordinateProduct (s.erase j) x ^ 2 ∂uniformSphere :=
      integral_sphere_fourth_mul_product_sq_eq_three (s.erase j) hij hj' hi'
    _ = _ := by
      rw [squarefreeSphereMoment_insert hi]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by dsimp only; rw [heq]; ring

/-- The true moment recurrence `M_s=(d+2|s|)M_(s∪{i})`. -/
theorem squarefreeSphereMoment_recurrence (s : Finset ι) {i : ι} (hi : i ∉ s) :
    squarefreeSphereMoment s =
      ((Fintype.card ι : ℝ) + 2 * (s.card : ℝ)) * squarefreeSphereMoment (insert i s) := by
  have hsphere (x : KernelSphere (EuclideanSpace ℝ ι)) : (∑ j, (x : EuclideanSpace ℝ ι) j ^ 2) = 1 := by
    have hh := real_inner_self_eq_norm_sq (x : EuclideanSpace ℝ ι)
    have hx : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    simpa only [PiLp.inner_apply, Real.inner_apply, ← pow_two, hx, one_pow] using hh
  have hpoint (x : KernelSphere (EuclideanSpace ℝ ι)) : sphereCoordinateProduct s x ^ 2 =
      ∑ j, (x : EuclideanSpace ℝ ι) j ^ 2 * sphereCoordinateProduct s x ^ 2 := by
    rw [← Finset.sum_mul, hsphere, one_mul]
  have hterm (j : ι) :
      (∫ x : KernelSphere (EuclideanSpace ℝ ι),
        (x : EuclideanSpace ℝ ι) j ^ 2 * sphereCoordinateProduct s x ^ 2 ∂uniformSphere) =
      (if j ∈ s then (3 : ℝ) else 1) * squarefreeSphereMoment (insert i s) := by
    by_cases hj : j ∈ s
    · simpa only [if_pos hj] using moment_repeated_coordinate_eq s hi hj
    · simpa only [if_neg hj, one_mul] using moment_new_coordinate_eq s hi hj
  have hcoef : (∑ j : ι, if j ∈ s then (3 : ℝ) else 1) =
      (Fintype.card ι : ℝ) + 2 * (s.card : ℝ) := by
    calc
      _ = ∑ j : ι, (1 + 2 * (if j ∈ s then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> norm_num
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
  unfold squarefreeSphereMoment at hpoint ⊢
  calc
    _ = ∫ x : KernelSphere (EuclideanSpace ℝ ι),
        ∑ j, (x : EuclideanSpace ℝ ι) j ^ 2 * sphereCoordinateProduct s x ^ 2 ∂uniformSphere :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ j : ι, ∫ x : KernelSphere (EuclideanSpace ℝ ι),
        (x : EuclideanSpace ℝ ι) j ^ 2 * sphereCoordinateProduct s x ^ 2 ∂uniformSphere :=
      integral_finsetSum _ (fun j _ => sphere_coordinate_sq_product_integrable s j)
    _ = ∑ j : ι, (if j ∈ s then (3 : ℝ) else 1) * squarefreeSphereMoment (insert i s) := by
      simp only [hterm]
    _ = _ := by rw [← Finset.sum_mul, hcoef]; rfl

/-- Exact all-degree squarefree moments, derived recursively from the actual
uniform sphere measure. No asymptotic or Gaussian representation is assumed. -/
theorem squarefreeSphereMoment_eq_inverse_product (s : Finset ι) :
    squarefreeSphereMoment s =
      (∏ k ∈ Finset.range s.card, ((Fintype.card ι : ℝ) + 2 * (k : ℝ)))⁻¹ := by
  induction s using Finset.induction_on with
  | empty => simp [squarefreeSphereMoment_empty]
  | @insert i s hi ih =>
    have hden : 0 < (Fintype.card ι : ℝ) + 2 * (s.card : ℝ) := by
      have hd : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
      positivity
    have hrec := squarefreeSphereMoment_recurrence s hi
    rw [Finset.card_insert_of_notMem hi, Finset.prod_range_succ]
    calc
      _ = squarefreeSphereMoment s / ((Fintype.card ι : ℝ) + 2 * (s.card : ℝ)) := by
        apply (eq_div_iff hden.ne').2
        simpa only [mul_comm] using hrec.symm
      _ = _ := by rw [ih, mul_inv, div_eq_mul_inv]

theorem squarefreeSphereMoment_pos (s : Finset ι) : 0 < squarefreeSphereMoment s := by
  rw [squarefreeSphereMoment_eq_inverse_product]
  apply inv_pos.mpr
  apply Finset.prod_pos
  intro k _
  have hd : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  positivity

/-- A fixed-degree lower bound with an explicit positive constant independent
of the ambient dimension. The exact moment formula supplies the estimate. -/
theorem squarefreeSphereMoment_ge_dimension_power (s : Finset ι) :
    ((1 + 2 * (s.card : ℝ)) ^ s.card)⁻¹ *
        (Fintype.card ι : ℝ) ^ (-(s.card : ℝ)) ≤ squarefreeSphereMoment s := by
  have hd : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hd1 : 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hprod : 0 < ∏ k ∈ Finset.range s.card, ((Fintype.card ι : ℝ) + 2 * (k : ℝ)) := by
    apply Finset.prod_pos
    intro k _
    positivity
  have hupper : (∏ k ∈ Finset.range s.card, ((Fintype.card ι : ℝ) + 2 * (k : ℝ))) ≤
      ((1 + 2 * (s.card : ℝ)) * (Fintype.card ι : ℝ)) ^ s.card := by
    calc
      _ ≤ ∏ _k ∈ Finset.range s.card, ((1 + 2 * (s.card : ℝ)) * (Fintype.card ι : ℝ)) := by
        apply Finset.prod_le_prod
        · intro k _
          positivity
        · intro k hk
          have hk' : (k : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast (Finset.mem_range.mp hk).le
          nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (by positivity : 0 ≤ 2 * (s.card : ℝ))]
      _ = _ := by simp
  have hh := one_div_le_one_div_of_le hprod hupper
  rw [squarefreeSphereMoment_eq_inverse_product]
  simpa only [one_div, mul_pow, mul_inv, Real.rpow_neg hd.le, Real.rpow_natCast] using hh

end
end KernelSeq
