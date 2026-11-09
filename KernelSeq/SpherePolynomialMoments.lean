import KernelSeq.SphereEvenMoments
import KernelSeq.SphereWeightedPower

/-!
# Actual mixed polynomial moments on the sphere

The coefficients below arise by genuine differentiation of the weighted
sphere integral. Coordinate products are ambient polynomials. This is a
constructive route to the actual zonal polynomial eigenspaces, without an
assumed harmonic decomposition.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def ambientCoordinateProduct (s : Finset ι) (x : EuclideanSpace ℝ ι) : ℝ := ∏ i ∈ s, x i

omit [Nonempty ι] [Fintype ι] in
theorem ambientCoordinateProduct_insert (s : Finset ι) {i : ι} (hi : i ∉ s) (x : EuclideanSpace ℝ ι) :
    ambientCoordinateProduct (insert i s) x = x i * ambientCoordinateProduct s x := by
  simp only [ambientCoordinateProduct, Finset.prod_insert hi]

omit [Nonempty ι] in
theorem euclidean_basis_coordinate (i j : ι) :
    (EuclideanSpace.basisFun ι ℝ i) j = if j=i then 1 else 0 := by
  simpa only [EuclideanSpace.basisFun_inner] using
    (orthonormal_iff_ite.mp (EuclideanSpace.basisFun ι ℝ).orthonormal) j i

omit [Nonempty ι] in
theorem ambientCoordinateProduct_add_basis {i : ι} (s : Finset ι) (hi : i ∉ s)
    (x : EuclideanSpace ℝ ι) (c : ℝ) :
    ambientCoordinateProduct s (x+c • EuclideanSpace.basisFun ι ℝ i) = ambientCoordinateProduct s x := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, euclidean_basis_coordinate, if_neg hji,
    mul_zero, add_zero]

omit [Nonempty ι] [DecidableEq ι] in
theorem hasDerivAt_norm_sq_add_smul (x v : EuclideanSpace ℝ ι) :
    HasDerivAt (fun c : ℝ => ‖x+c • v‖^2) (2*inner ℝ x v) 0 := by
  have heq (c : ℝ) : ‖x+c • v‖^2 = ‖x‖^2 + (2*inner ℝ x v)*c + ‖v‖^2*c^2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs]
    nlinarith [sq_abs c]
  have hp := ((hasDerivAt_const (0 : ℝ) (‖x‖^2)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul (2*inner ℝ x v))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (‖v‖^2))
  have hp' : HasDerivAt (fun c : ℝ => ‖x‖^2 + (2*inner ℝ x v)*c + ‖v‖^2*c^2)
      (2*inner ℝ x v) 0 := by
    convert! hp using 1
    norm_num
  exact hp'.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)

/-- The actual radial coefficient, written without a chosen pole. -/
def spherePowerBaseCoefficient (ι : Type*) [Fintype ι] (N : ℕ) : ℝ :=
  if Even N then ∏ k ∈ Finset.range (N/2),
    (2*(k : ℝ)+1) / ((Fintype.card ι : ℝ)+2*(k : ℝ)) else 0

/-- Successive genuine coordinate derivatives of the radial polynomial. -/
def sphereMixedPowerCoefficient (ι : Type*) [Fintype ι] (N : ℕ) : ℕ → ℝ
  | 0 => spherePowerBaseCoefficient ι N
  | k+1 => sphereMixedPowerCoefficient ι N k * (2*((N/2-k : ℕ) : ℝ)) / ((N-k : ℕ) : ℝ)

theorem sphereInnerPowerMoment_eq_baseCoefficient (N : ℕ) (x : EuclideanSpace ℝ ι) :
    sphereInnerPowerMoment N x = spherePowerBaseCoefficient ι N * (‖x‖^2)^(N/2) := by
  rcases Nat.even_or_odd N with hEven | hOdd
  · obtain ⟨r, hr⟩ := hEven
    have he : N=2*r := by omega
    rw [he]
    have hE : Even (2*r) := ⟨r, by omega⟩
    have hdiv : (2*r)/2 = r := by omega
    rw [spherePowerBaseCoefficient, if_pos hE, hdiv,
      sphereInnerPowerMoment_even_eq_product r x (Classical.arbitrary ι), pow_mul]
    ring
  · obtain ⟨r, hr⟩ := hOdd
    have he : N=2*r+1 := by omega
    rw [he, sphereInnerPowerMoment_odd]
    have hnot : ¬Even (2*r+1) := by rintro ⟨k, hk⟩; omega
    simp only [spherePowerBaseCoefficient, if_neg hnot, zero_mul]

omit [DecidableEq ι] in
theorem sphereMixedPowerCoefficient_nonneg (N k : ℕ) : 0 ≤ sphereMixedPowerCoefficient ι N k := by
  induction k with
  | zero =>
    unfold sphereMixedPowerCoefficient spherePowerBaseCoefficient
    split_ifs
    · exact Finset.prod_nonneg fun _ _ => div_nonneg (by positivity) (by positivity)
    · exact le_rfl
  | succ k ih =>
    rw [sphereMixedPowerCoefficient]
    exact div_nonneg (mul_nonneg ih (by positivity)) (Nat.cast_nonneg _)

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereMixedPowerCoefficient_eq_product (N k : ℕ) :
    sphereMixedPowerCoefficient ι N k = spherePowerBaseCoefficient ι N *
      ∏ a ∈ Finset.range k, (2*((N/2-a : ℕ) : ℝ)) / ((N-a : ℕ) : ℝ) := by
  induction k with
  | zero => simp [sphereMixedPowerCoefficient]
  | succ k ih =>
    rw [sphereMixedPowerCoefficient, ih, Finset.prod_range_succ]
    ring

omit [DecidableEq ι] in
theorem sphereMixedPowerCoefficient_even_pos (r k : ℕ) (hk : k ≤ r) :
    0 < sphereMixedPowerCoefficient ι (2*r) k := by
  have hEven : Even (2*r) := ⟨r, by omega⟩
  have hdiv : (2*r)/2 = r := by omega
  rw [sphereMixedPowerCoefficient_eq_product, spherePowerBaseCoefficient, if_pos hEven, hdiv]
  apply mul_pos
  · apply Finset.prod_pos
    intro j _
    have hd : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    positivity
  · apply Finset.prod_pos
    intro j hj
    have hjk := Finset.mem_range.mp hj
    have hnum : 0 < r-j := by omega
    have hden : 0 < 2*r-j := by omega
    exact div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hnum)) (Nat.cast_pos.mpr hden)

/-- Exact mixed moment identity for every squarefree product. The proof
successively differentiates the actual weighted integral in previously
unused coordinate directions; no harmonic/eigenvalue formula is supplied. -/
theorem weightedSpherePowerMoment_squarefree (N : ℕ) (s : Finset ι) (hS : s.card ≤ N)
    (x : EuclideanSpace ℝ ι) :
    weightedSpherePowerMoment (sphereCoordinateProduct s) (N-s.card) x =
      sphereMixedPowerCoefficient ι N s.card * ambientCoordinateProduct s x * (‖x‖^2)^(N/2-s.card) := by
  have hmain : ∀ s : Finset ι, s.card ≤ N → ∀ x : EuclideanSpace ℝ ι,
      weightedSpherePowerMoment (sphereCoordinateProduct s) (N-s.card) x =
        sphereMixedPowerCoefficient ι N s.card * ambientCoordinateProduct s x * (‖x‖^2)^(N/2-s.card) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ x
      simpa only [weightedSpherePowerMoment, sphereCoordinateProduct, Finset.prod_empty, one_mul,
        Finset.card_empty, Nat.sub_zero, sphereMixedPowerCoefficient, ambientCoordinateProduct, mul_one,
        sphereInnerPowerMoment] using sphereInnerPowerMoment_eq_baseCoefficient N x
    | @insert i s hi ih =>
      intro hS x
      have hkN : s.card < N := by rw [Finset.card_insert_of_notMem hi] at hS; omega
      have ihfun := ih (by omega : s.card ≤ N)
      have hN : N-s.card-1+1 = N-s.card := by omega
      have hncast : ((N-s.card-1 : ℕ) : ℝ)+1 = ((N-s.card : ℕ) : ℝ) := by exact_mod_cast hN
      have hnexp : N-s.card-1 = N-(s.card+1) := by omega
      have hweight : (fun y : KernelSphere (EuclideanSpace ℝ ι) =>
          sphereCoordinateProduct s y * inner ℝ (EuclideanSpace.basisFun ι ℝ i) (y : EuclideanSpace ℝ ι)) =
          sphereCoordinateProduct (insert i s) := by
        funext y
        simp only [EuclideanSpace.basisFun_inner, sphereCoordinateProduct, Finset.prod_insert hi]
        ring
      have hleft := hasDerivAt_weightedSpherePower_add_smul (sphereCoordinateProduct s)
        (sphereCoordinateProduct_continuous s) (N-s.card-1) x (EuclideanSpace.basisFun ι ℝ i)
      rw [hN, hncast, hweight, hnexp] at hleft
      have hnorm := hasDerivAt_norm_sq_add_smul x (EuclideanSpace.basisFun ι ℝ i)
      have hinner : inner ℝ x (EuclideanSpace.basisFun ι ℝ i) = x i := by
        rw [real_inner_comm, EuclideanSpace.basisFun_inner]
      rw [hinner] at hnorm
      have hp := (hnorm.pow (N/2-s.card)).const_mul
        (sphereMixedPowerCoefficient ι N s.card * ambientCoordinateProduct s x)
      have hright : HasDerivAt (fun c : ℝ =>
          sphereMixedPowerCoefficient ι N s.card *
            ambientCoordinateProduct s (x+c • EuclideanSpace.basisFun ι ℝ i) *
            (‖x+c • EuclideanSpace.basisFun ι ℝ i‖^2)^(N/2-s.card))
          ((sphereMixedPowerCoefficient ι N s.card * ambientCoordinateProduct s x) *
            (((N/2-s.card : ℕ) : ℝ) * (‖x‖^2)^(N/2-s.card-1) * (2*x i))) 0 := by
        convert! hp using 1
        · funext c
          rw [ambientCoordinateProduct_add_basis s hi]
          rfl
        · simp only [zero_smul, add_zero]
      have hright' := hright.congr_of_eventuallyEq (Filter.Eventually.of_forall fun c =>
        ihfun (x+c • EuclideanSpace.basisFun ι ℝ i))
      have he := hleft.unique hright'
      have hpExp : N/2-s.card-1 = N/2-(s.card+1) := by omega
      rw [Finset.card_insert_of_notMem hi, sphereMixedPowerCoefficient,
        ambientCoordinateProduct_insert s hi, ← hpExp]
      have hd : (0 : ℝ) < ((N-s.card : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      apply mul_left_cancel₀ hd.ne'
      calc
        _ = (sphereMixedPowerCoefficient ι N s.card * ambientCoordinateProduct s x) *
            (((N/2-s.card : ℕ) : ℝ) * (‖x‖^2)^(N/2-s.card-1) * (2*x i)) := he
        _ = _ := by field_simp
  exact hmain s hS x


/-- Every homogeneous monomial kernel acts by a genuine scalar on each
squarefree degree-m coordinate function. This includes j<m and parity cases
through the explicitly constructed coefficient. -/
theorem integral_sphere_inner_power_mul_squarefree
    (j : ℕ) (s : Finset ι) (x : KernelSphere (EuclideanSpace ℝ ι)) :
    (∫ y : KernelSphere (EuclideanSpace ℝ ι),
      sphereCoordinateProduct s y * inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)^j
      ∂uniformSphere) =
      sphereMixedPowerCoefficient ι (j+s.card) s.card * sphereCoordinateProduct s x := by
  have hh := weightedSpherePowerMoment_squarefree (j+s.card) s (by omega) (x : EuclideanSpace ℝ ι)
  have hx : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simpa only [Nat.add_sub_cancel, hx, one_pow, mul_one, weightedSpherePowerMoment,
    ambientCoordinateProduct, sphereCoordinateProduct] using hh


end
end KernelSeq
