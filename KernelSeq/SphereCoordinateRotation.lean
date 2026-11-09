import KernelSeq.SphereCoordinateMoments

/-!
# A genuine two-coordinate 45-degree orthogonal transformation

The map sends `(x_i,x_j)` to `((x_i+x_j)/√2,(x_i-x_j)/√2)` and fixes every
other coordinate. Linearity, involutivity and preservation of the actual
Euclidean norm are proved directly. This supplies the geometric identity
needed for the mixed spherical-moment recurrence.
-/

namespace KernelSeq
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def halfRoot : ℝ := Real.sqrt (1 / 2)

private theorem halfRoot_sq : halfRoot ^ 2 = 1 / 2 := by
  exact Real.sq_sqrt (by norm_num)

private def coordinateHadamardLinear (i j : ι) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 fun k =>
    if k = i then halfRoot * (x i + x j)
    else if k = j then halfRoot * (x i - x j) else x k
  map_add' x y := by
    ext k
    simp only [PiLp.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext k
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

omit [Fintype ι] in
private theorem coordinateHadamardLinear_apply (i j : ι) (x : EuclideanSpace ℝ ι) (k : ι) :
    coordinateHadamardLinear i j x k = if k = i then halfRoot * (x i + x j)
      else if k = j then halfRoot * (x i - x j) else x k := rfl

omit [Fintype ι] in
private theorem coordinateHadamardLinear_involutive {i j : ι} (hij : i ≠ j) :
    Function.Involutive (coordinateHadamardLinear i j) := by
  intro x
  ext k
  by_cases hki : k = i
  · subst k
    simp only [coordinateHadamardLinear_apply, ite_true, if_neg hij, if_neg hij.symm]
    calc
      _ = (2 * halfRoot ^ 2) * x i := by ring
      _ = x i := by rw [halfRoot_sq]; ring
  · by_cases hkj : k = j
    · subst k
      simp only [coordinateHadamardLinear_apply, if_neg hij.symm, ite_true, if_neg hij]
      calc
        _ = (2 * halfRoot ^ 2) * x j := by ring
        _ = x j := by rw [halfRoot_sq]; ring
    · simp only [coordinateHadamardLinear_apply, if_neg hki, if_neg hkj]

private theorem sum_split_two (f : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  have h1 := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ i)
  have h2 := Finset.sum_erase_add (s := Finset.univ.erase i) f
    (by simp only [Finset.mem_erase, Finset.mem_univ, and_true]; exact hij.symm)
  linarith

private theorem coordinateHadamardLinear_norm {i j : ι} (hij : i ≠ j) (x : EuclideanSpace ℝ ι) :
    ‖coordinateHadamardLinear i j x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, Real.inner_apply, ← pow_two]
  rw [sum_split_two _ hij, sum_split_two _ hij]
  have hrest :
      (∑ k ∈ (Finset.univ.erase i).erase j, coordinateHadamardLinear i j x k ^ 2) =
        ∑ k ∈ (Finset.univ.erase i).erase j, x k ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := (Finset.mem_erase.mp hk).1
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    simp only [coordinateHadamardLinear_apply, if_neg hki, if_neg hkj]
  rw [hrest]
  simp only [coordinateHadamardLinear_apply, ite_true, if_neg hij.symm]
  have hh : (halfRoot * (x i + x j)) ^ 2 + (halfRoot * (x i - x j)) ^ 2 = x i ^ 2 + x j ^ 2 := by
    rw [mul_pow, mul_pow, halfRoot_sq]
    ring
  linarith

/-- The fully constructed orthogonal map, valid with arbitrary repeated
ambient dimension and any two distinct coordinate labels. -/
def sphereCoordinateHadamard (i j : ι) (hij : i ≠ j) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toLinearEquiv := LinearEquiv.ofInvolutive (coordinateHadamardLinear i j)
    (coordinateHadamardLinear_involutive hij)
  norm_map' := coordinateHadamardLinear_norm hij

@[simp] theorem sphereCoordinateHadamard_apply (i j : ι) (hij : i ≠ j)
    (x : EuclideanSpace ℝ ι) (k : ι) :
    sphereCoordinateHadamard i j hij x k =
      if k = i then Real.sqrt (1 / 2) * (x i + x j)
      else if k = j then Real.sqrt (1 / 2) * (x i - x j) else x k := rfl

end
end KernelSeq
