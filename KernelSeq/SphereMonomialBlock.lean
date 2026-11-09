import KernelSeq.SphereMomentRecurrence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Actual squarefree polynomial subspaces in spherical L²

The vectors are equivalence classes of the real coordinate monomials under
the actual uniform sphere probability. Their Gram matrix, normalization,
dimension and finite-span Parseval identity are proved from actual moments.
No harmonic basis or polynomial-block coercivity is an input.
-/

namespace KernelSeq
open MeasureTheory Set Submodule
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev SquarefreeSphereIndex (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) :=
  ↥((Finset.univ : Finset ι).powersetCard m)

omit [Nonempty ι] in
theorem squarefreeSphereIndex_card {m : ℕ} (s : SquarefreeSphereIndex ι m) : s.val.card = m :=
  (Finset.mem_powersetCard.mp s.property).2

omit [Nonempty ι] in
theorem card_squarefreeSphereIndex (m : ℕ) :
    Fintype.card (SquarefreeSphereIndex ι m) = (Fintype.card ι).choose m := by
  simp only [SquarefreeSphereIndex, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ]

def degreeSphereMoment (ι : Type*) [Fintype ι] (m : ℕ) : ℝ :=
  (∏ k ∈ Finset.range m, ((Fintype.card ι : ℝ) + 2 * (k : ℝ)))⁻¹

omit [DecidableEq ι] in
theorem degreeSphereMoment_pos (m : ℕ) : 0 < degreeSphereMoment ι m := by
  unfold degreeSphereMoment
  apply inv_pos.mpr
  apply Finset.prod_pos
  intro k _
  have hd : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  positivity

omit [DecidableEq ι] in
/-- Fixed-degree constants here are independent of the ambient dimension,
including degrees exceeding it (where the squarefree block is empty). -/
theorem degreeSphereMoment_ge_dimension_power (m : ℕ) :
    ((1 + 2 * (m : ℝ)) ^ m)⁻¹ *
        (Fintype.card ι : ℝ) ^ (-(m : ℝ)) ≤ degreeSphereMoment ι m := by
  have hd : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hd1 : 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hprod : 0 < ∏ k ∈ Finset.range m, ((Fintype.card ι : ℝ) + 2 * (k : ℝ)) := by
    apply Finset.prod_pos
    intro k _
    positivity
  have hupper : (∏ k ∈ Finset.range m, ((Fintype.card ι : ℝ) + 2 * (k : ℝ))) ≤
      ((1 + 2 * (m : ℝ)) * (Fintype.card ι : ℝ)) ^ m := by
    calc
      _ ≤ ∏ _k ∈ Finset.range m, ((1 + 2 * (m : ℝ)) * (Fintype.card ι : ℝ)) := by
        apply Finset.prod_le_prod
        · intro k _
          positivity
        · intro k hk
          have hk' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_range.mp hk).le
          nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (by positivity : 0 ≤ 2 * (m : ℝ))]
      _ = _ := by simp
  have hh := one_div_le_one_div_of_le hprod hupper
  simpa only [degreeSphereMoment, one_div, mul_pow, mul_inv, Real.rpow_neg hd.le,
    Real.rpow_natCast] using hh

theorem squarefreeSphereMoment_eq_degreeMoment {m : ℕ} (s : SquarefreeSphereIndex ι m) :
    squarefreeSphereMoment s.val = degreeSphereMoment ι m := by
  rw [squarefreeSphereMoment_eq_inverse_product, squarefreeSphereIndex_card]
  rfl

def squarefreeSphereLp {m : ℕ} (s : SquarefreeSphereIndex ι m) :
    Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)) :=
  (sphereCoordinateProduct_memLp s.val).toLp (sphereCoordinateProduct s.val)

theorem inner_squarefreeSphereLp {m : ℕ} (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))
    (s : SquarefreeSphereIndex ι m) :
    inner ℝ f (squarefreeSphereLp s) =
      ∫ x : KernelSphere (EuclideanSpace ℝ ι), f x * sphereCoordinateProduct s.val x ∂uniformSphere := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(sphereCoordinateProduct_memLp s.val).coeFn_toLp] with x hx
  change inner ℝ (f x) (((sphereCoordinateProduct_memLp s.val).toLp (sphereCoordinateProduct s.val)) x) = _
  rw [hx, Real.inner_apply]

theorem squarefreeSphereLp_inner {m : ℕ} (s t : SquarefreeSphereIndex ι m) :
    inner ℝ (squarefreeSphereLp s) (squarefreeSphereLp t) =
      if s = t then degreeSphereMoment ι m else 0 := by
  rw [inner_squarefreeSphereLp]
  have hh : (∫ x : KernelSphere (EuclideanSpace ℝ ι),
      (squarefreeSphereLp s) x * sphereCoordinateProduct t.val x ∂uniformSphere) =
      ∫ x : KernelSphere (EuclideanSpace ℝ ι),
        sphereCoordinateProduct s.val x * sphereCoordinateProduct t.val x ∂uniformSphere := by
    apply integral_congr_ae
    filter_upwards [(sphereCoordinateProduct_memLp s.val).coeFn_toLp] with x hx
    change (((sphereCoordinateProduct_memLp s.val).toLp (sphereCoordinateProduct s.val)) x) * _ = _
    rw [hx]
  rw [hh]
  split_ifs with hst
  · subst t
    simpa only [← pow_two, squarefreeSphereMoment] using squarefreeSphereMoment_eq_degreeMoment s
  · exact integral_sphereCoordinateProduct_mul_eq_zero (fun h => hst (Subtype.ext h))

def normalizedSquarefreeSphereLp {m : ℕ} (s : SquarefreeSphereIndex ι m) :
    Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)) :=
  (Real.sqrt (degreeSphereMoment ι m))⁻¹ • squarefreeSphereLp s

theorem normalizedSquarefreeSphereLp_orthonormal (m : ℕ) :
    Orthonormal ℝ (normalizedSquarefreeSphereLp (ι := ι) (m := m)) := by
  rw [orthonormal_iff_ite]
  intro s t
  unfold normalizedSquarefreeSphereLp
  rw [inner_smul_left, inner_smul_right, squarefreeSphereLp_inner]
  simp only [map_inv₀, RCLike.conj_to_real]
  split_ifs with hst
  · have hs := Real.sqrt_pos.mpr (degreeSphereMoment_pos (ι := ι) m)
    have hh := Real.sq_sqrt (degreeSphereMoment_pos (ι := ι) m).le
    field_simp
    nlinarith
  · simp

def squarefreeSphereBlock (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (m : ℕ) :
    Submodule ℝ (Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) :=
  span ℝ (Set.range (normalizedSquarefreeSphereLp (ι := ι) (m := m)))

instance squarefreeSphereBlock_finiteDimensional (m : ℕ) :
    FiniteDimensional ℝ (squarefreeSphereBlock ι m) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem squarefreeSphereBlock_finrank (m : ℕ) :
    Module.finrank ℝ (squarefreeSphereBlock ι m) = (Fintype.card ι).choose m := by
  rw [squarefreeSphereBlock, finrank_span_eq_card (normalizedSquarefreeSphereLp_orthonormal (ι := ι) m).linearIndependent,
    card_squarefreeSphereIndex]

/-- Finite-span Parseval holds in the actual ambient L² space, without a
separability assumption on that ambient space. -/
theorem squarefreeSphereBlock_parseval {m : ℕ}
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) (hf : f ∈ squarefreeSphereBlock ι m) :
    (∑ s : SquarefreeSphereIndex ι m, inner ℝ f (normalizedSquarefreeSphereLp s) ^ 2) = ‖f‖ ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
  rw [← hc]
  have hon := normalizedSquarefreeSphereLp_orthonormal (ι := ι) m
  simp only [hon.inner_left_fintype, RCLike.conj_to_real]
  rw [← real_inner_self_eq_norm_sq, hon.inner_sum]
  simp only [RCLike.conj_to_real, pow_two]


/-- The block dimension has a fixed-degree polynomial lower bound once
`d ≥ 2m`; this is a finite combinatorial estimate, not a spectral assumption. -/
theorem squarefreeSphereBlock_dimension_lower (m : ℕ) (hd : 2 * m ≤ Fintype.card ι) :
    (Fintype.card ι : ℝ)^m / (2^m * (m.factorial : ℝ)) ≤
      (Module.finrank ℝ (squarefreeSphereBlock ι m) : ℝ) := by
  rw [squarefreeSphereBlock_finrank]
  have hnat : m ≤ Fintype.card ι + 1 := by omega
  have hh : (Fintype.card ι : ℝ) / 2 ≤ ((Fintype.card ι + 1 - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hnat]
    push_cast
    have hd' : 2 * (m : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hd
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Fintype.card ι : ℝ) / 2) hh m
  have hfact : (0 : ℝ) < m.factorial := Nat.cast_pos.mpr m.factorial_pos
  have hdiv := div_le_div_of_nonneg_right hpow hfact.le
  calc
    _ = ((Fintype.card ι : ℝ) / 2)^m / (m.factorial : ℝ) := by rw [div_pow]; ring
    _ ≤ _ := hdiv.trans (Nat.pow_le_choose (α := ℝ) m (Fintype.card ι))

/-- One genuine tensor word for each squarefree subset. Only one ordering is
needed for the frame lower bound, so no factorial multiplicity is assumed. -/
def squarefreeSphereWord {m : ℕ} (s : SquarefreeSphereIndex ι m) : Fin m → ι :=
  fun r => ((Finset.equivFinOfCardEq (squarefreeSphereIndex_card s)).symm r : ι)

omit [Nonempty ι] in
theorem range_squarefreeSphereWord {m : ℕ} (s : SquarefreeSphereIndex ι m) :
    Set.range (squarefreeSphereWord s) = (s.val : Set ι) := by
  ext i
  constructor
  · rintro ⟨r, rfl⟩
    exact ((Finset.equivFinOfCardEq (squarefreeSphereIndex_card s)).symm r).property
  · intro hi
    let e := Finset.equivFinOfCardEq (squarefreeSphereIndex_card s)
    refine ⟨e ⟨i, hi⟩, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨i, hi⟩)

omit [Nonempty ι] in
theorem squarefreeSphereWord_injective (m : ℕ) :
    Function.Injective (squarefreeSphereWord (ι := ι) (m := m)) := by
  intro s t h
  apply Subtype.ext
  apply Finset.coe_injective
  rw [← range_squarefreeSphereWord s, ← range_squarefreeSphereWord t, h]

omit [Nonempty ι] in
theorem prod_squarefreeSphereWord {m : ℕ} (s : SquarefreeSphereIndex ι m)
    (x : KernelSphere (EuclideanSpace ℝ ι)) :
    (∏ r : Fin m, (x : EuclideanSpace ℝ ι) (squarefreeSphereWord s r)) =
      sphereCoordinateProduct s.val x := by
  let e := Finset.equivFinOfCardEq (squarefreeSphereIndex_card s)
  change (∏ r : Fin m, (x : EuclideanSpace ℝ ι) (e.symm r : ι)) = _
  calc
    _ = ∏ j : s.val, (x : EuclideanSpace ℝ ι) (j : ι) :=
      Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
    _ = _ := by
      change (∏ j ∈ s.val.attach, (x : EuclideanSpace ℝ ι) (j : ι)) = _
      exact Finset.prod_attach s.val (fun j => (x : EuclideanSpace ℝ ι) j)

/-- Actual coefficient energy on the squarefree block. -/
theorem squarefreeSphereBlock_coefficient_energy {m : ℕ}
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) (hf : f ∈ squarefreeSphereBlock ι m) :
    (∑ s : SquarefreeSphereIndex ι m,
      (∫ x : KernelSphere (EuclideanSpace ℝ ι), f x * sphereCoordinateProduct s.val x ∂uniformSphere)^2) =
      degreeSphereMoment ι m * ‖f‖ ^ 2 := by
  have hs0 := Real.sqrt_pos.mpr (degreeSphereMoment_pos (ι := ι) m)
  have hsq := Real.sq_sqrt (degreeSphereMoment_pos (ι := ι) m).le
  have hcoeff (s : SquarefreeSphereIndex ι m) :
      (∫ x : KernelSphere (EuclideanSpace ℝ ι), f x * sphereCoordinateProduct s.val x ∂uniformSphere)^2 =
      degreeSphereMoment ι m * (inner ℝ f (normalizedSquarefreeSphereLp s))^2 := by
    rw [← inner_squarefreeSphereLp]
    unfold normalizedSquarefreeSphereLp
    rw [inner_smul_right]
    field_simp
    nlinarith
  simp_rw [hcoeff]
  rw [← Finset.mul_sum, squarefreeSphereBlock_parseval f hf]

/-- The genuine degree-m tensor coordinates dominate the block energy.
This is a finite-frame statement in actual uniform-sphere L², without an
assumed polynomial eigenvalue or harmonic decomposition. -/
theorem squarefreeSphereBlock_tensor_energy_lower {m : ℕ}
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) (hf : f ∈ squarefreeSphereBlock ι m) :
    degreeSphereMoment ι m * ‖f‖ ^ 2 ≤
      ∑ α : Fin m → ι,
        (∫ x : KernelSphere (EuclideanSpace ℝ ι),
          f x * ∏ r : Fin m, (x : EuclideanSpace ℝ ι) (α r) ∂uniformSphere)^2 := by
  classical
  let F : (Fin m → ι) → ℝ := fun α =>
    (∫ x : KernelSphere (EuclideanSpace ℝ ι),
      f x * ∏ r : Fin m, (x : EuclideanSpace ℝ ι) (α r) ∂uniformSphere)^2
  have heq : (∑ s : SquarefreeSphereIndex ι m, F (squarefreeSphereWord s)) =
      degreeSphereMoment ι m * ‖f‖ ^ 2 := by
    simpa only [F, prod_squarefreeSphereWord] using squarefreeSphereBlock_coefficient_energy f hf
  rw [← heq]
  have himage : (∑ s : SquarefreeSphereIndex ι m, F (squarefreeSphereWord s)) =
      ∑ α ∈ Finset.univ.image (squarefreeSphereWord (ι := ι) (m := m)), F α := by
    rw [Finset.sum_image]
    exact fun a _ b _ h => squarefreeSphereWord_injective m h
  rw [himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun α _ _ => sq_nonneg _)

end
end KernelSeq
