import KernelSeq.SpherePolynomialFiltration

/-!
# Genuine orthogonality of the squarefree block to lower degrees

A lower-degree tensor word misses a coordinate of any squarefree degree-m
product. Flipping that actual coordinate preserves the word and reverses
the product, so its genuine sphere integral is zero. The L² and finite-span
orthogonality conclusions are derived from these actual functions.
-/

namespace KernelSeq
open MeasureTheory Set Submodule
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem sphereMultisetMonomial_flip_of_notMem (a : Multiset ι) (i : ι) (hi : i ∉ a)
    (x : KernelSphere (EuclideanSpace ℝ ι)) :
    sphereMultisetMonomial a (sphereRotation (sphereCoordinateFlip i) x) = sphereMultisetMonomial a x := by
  induction a using Multiset.induction_on with
  | empty => rfl
  | @cons j a ih =>
    have hji : j ≠ i := by intro h; exact hi (by simp [h])
    have hia : i ∉ a := fun h => hi (Multiset.mem_cons_of_mem h)
    simp only [sphereMultisetMonomial, Multiset.map_cons, Multiset.prod_cons]
    rw [sphereRotation_coe, sphereCoordinateFlip_apply, if_neg hji]
    exact congrArg (fun v : ℝ => (x : EuclideanSpace ℝ ι) j*v) (ih hia)

omit [Nonempty ι] in
/-- The true sphere integral vanishes for every word of strictly lower degree. -/
theorem integral_squarefree_mul_sphereMultisetMonomial_eq_zero
    (s : Finset ι) (a : Multiset ι) (hdegree : a.card < s.card) :
    (∫ x : KernelSphere (EuclideanSpace ℝ ι),
      sphereCoordinateProduct s x * sphereMultisetMonomial a x ∂uniformSphere) = 0 := by
  have hsub : ¬s ⊆ a.toFinset := by
    intro h
    exact (Nat.not_lt_of_ge ((Finset.card_le_card h).trans a.toFinset_card_le)) hdegree
  obtain ⟨i, his, hia⟩ := Finset.not_subset.mp hsub
  have hia' : i ∉ a := by simpa only [Multiset.mem_toFinset] using hia
  apply integral_sphere_eq_zero_of_flip i
  intro x
  rw [sphereCoordinateProduct_flip, if_pos his, sphereMultisetMonomial_flip_of_notMem a i hia']
  ring

/-- The L² identity is proved using the actual representatives and integrals,
not by assuming orthogonality of polynomial or harmonic spaces. -/
theorem inner_normalizedSquarefreeSphereLp_sphereSymLp_eq_zero
    {m j : ℕ} (s : SquarefreeSphereIndex ι m) (a : Sym ι j) (hj : j < m) :
    inner ℝ (normalizedSquarefreeSphereLp s) (sphereSymLp a) = 0 := by
  unfold normalizedSquarefreeSphereLp
  rw [inner_smul_left, conj_trivial]
  have hcomm : inner ℝ (squarefreeSphereLp s) (sphereSymLp a) =
      inner ℝ (sphereSymLp a) (squarefreeSphereLp s) := real_inner_comm _ _
  rw [hcomm, inner_squarefreeSphereLp]
  have heq : (∫ x : KernelSphere (EuclideanSpace ℝ ι),
      (sphereSymLp a) x * sphereCoordinateProduct s.val x ∂uniformSphere) =
      ∫ x : KernelSphere (EuclideanSpace ℝ ι),
        sphereCoordinateProduct s.val x * sphereMultisetMonomial a.val x ∂uniformSphere := by
    apply integral_congr_ae
    filter_upwards [(sphereMultisetMonomial_memLp a.val).coeFn_toLp] with x hx
    change (sphereSymLp a) x = sphereMultisetMonomial a.val x at hx
    rw [hx]
    ring
  rw [heq, integral_squarefree_mul_sphereMultisetMonomial_eq_zero]
  · exact mul_zero _
  · have hc : a.val.card = j := a.property
    rw [hc, squarefreeSphereIndex_card]
    exact hj

/-- Every lower homogeneous polynomial space is genuinely orthogonal to the
entire actual squarefree degree-m block. -/
theorem squarefreeSphereBlock_le_orthogonal_homogeneous {m j : ℕ} (hj : j < m) :
    squarefreeSphereBlock ι m ≤ Submodule.orthogonal (homogeneousSpherePolynomialSpace ι j) := by
  apply Submodule.span_le.mpr
  rintro f ⟨s, rfl⟩
  change ∀ g ∈ homogeneousSpherePolynomialSpace ι j, inner ℝ g (normalizedSquarefreeSphereLp s) = 0
  intro g hg
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
  rw [← hc, sum_inner]
  apply Finset.sum_eq_zero
  intro a _
  rw [inner_smul_left, conj_trivial]
  have hh : inner ℝ (sphereSymLp a) (normalizedSquarefreeSphereLp s) = 0 := by
    rw [real_inner_comm]
    exact inner_normalizedSquarefreeSphereLp_sphereSymLp_eq_zero s a hj
  rw [hh, mul_zero]

/-- The orthogonality is simultaneous over every strictly lower degree in
the actual degree-at-most filtration. -/
theorem squarefreeSphereBlock_le_orthogonal_filtration {m k : ℕ} (hkm : k < m) :
    squarefreeSphereBlock ι m ≤ Submodule.orthogonal (spherePolynomialSpace ι k) := by
  apply Submodule.span_le.mpr
  rintro f ⟨s, rfl⟩
  change ∀ g ∈ spherePolynomialSpace ι k, inner ℝ g (normalizedSquarefreeSphereLp s) = 0
  intro g hg
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
  rw [← hc, sum_inner]
  apply Finset.sum_eq_zero
  intro a _
  rw [inner_smul_left, conj_trivial]
  have hh : inner ℝ (spherePolynomialGenerator a) (normalizedSquarefreeSphereLp s) = 0 := by
    rw [real_inner_comm]
    exact inner_normalizedSquarefreeSphereLp_sphereSymLp_eq_zero s a.2 (by have := a.1.isLt; omega)
  rw [hh, mul_zero]

/-- A true squarefree subspace lies in the actual orthogonal degree layer;
its already-proved dimension supplies the sharp leading lower count. -/
theorem squarefreeSphereBlock_le_degree_layer (m : ℕ) :
    squarefreeSphereBlock ι (m+1) ≤ spherePolynomialSpace ι (m+1) ⊓
      Submodule.orthogonal (spherePolynomialSpace ι m) :=
  le_inf ((squarefreeSphereBlock_le_homogeneous (m+1)).trans
    (homogeneousSpherePolynomialSpace_le_filtration le_rfl))
    (squarefreeSphereBlock_le_orthogonal_filtration (by omega))

end
end KernelSeq
