import KernelSeq.SpherePolynomialSpace

/-!
# The genuine increasing spherical polynomial filtration

The degree-at-most spaces are actual finite spans in uniform-sphere L2.
The sphere equation also supplies the homogeneous degree-two inclusion.
No harmonic decomposition or spectral completeness is assumed here.
-/

namespace KernelSeq
open MeasureTheory Submodule Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def sphereSymSquare {m : ℕ} (a : Sym ι m) (i : ι) : Sym ι (m+2) :=
  ⟨i ::ₘ i ::ₘ a.val, by simp only [Multiset.card_cons, a.property]⟩

omit [DecidableEq ι] in
theorem sphereSymLp_eq_sum_square {m : ℕ} (a : Sym ι m) :
    sphereSymLp a = ∑ i : ι, sphereSymLp (sphereSymSquare a i) := by
  have hterm (i : ι) : sphereSymLp (sphereSymSquare a i) =ᵐ[uniformSphere]
      sphereMultisetMonomial (sphereSymSquare a i).val :=
    (sphereMultisetMonomial_memLp (sphereSymSquare a i).val).coeFn_toLp
  have hbase : sphereSymLp a =ᵐ[uniformSphere] sphereMultisetMonomial a.val :=
    (sphereMultisetMonomial_memLp a.val).coeFn_toLp
  apply Lp.ext
  filter_upwards [hbase,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : ι => sphereSymLp (sphereSymSquare a i)),
    ae_all_iff.mpr hterm] with x hx hsum ht
  rw [hx, hsum]
  have hnorm : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hs : (∑ i : ι, (x : EuclideanSpace ℝ ι) i^2) = 1 := by
    simpa only [hnorm, one_pow] using (EuclideanSpace.real_norm_sq_eq (x : EuclideanSpace ℝ ι)).symm
  calc
    _ = sphereMultisetMonomial a.val x * (∑ i : ι, (x : EuclideanSpace ℝ ι) i^2) := by rw [hs, mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [ht i]
      simp only [sphereMultisetMonomial, sphereSymSquare, Multiset.map_cons, Multiset.prod_cons]
      ring

theorem homogeneousSpherePolynomialSpace_le_add_two (m : ℕ) :
    homogeneousSpherePolynomialSpace ι m ≤ homogeneousSpherePolynomialSpace ι (m+2) := by
  apply Submodule.span_le.mpr
  rintro f ⟨a,rfl⟩
  rw [sphereSymLp_eq_sum_square]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span (Set.mem_range_self (sphereSymSquare a i))

abbrev SpherePolynomialIndex (ι : Type*) [Fintype ι] (m : ℕ) := Σ j : Fin (m+1), Sym ι j.val

def spherePolynomialGenerator {m : ℕ} (a : SpherePolynomialIndex ι m) :
    Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)) := sphereSymLp a.2

def spherePolynomialSpace (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (m : ℕ) : Submodule ℝ (Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) :=
  span ℝ (Set.range (spherePolynomialGenerator (ι := ι) (m := m)))

instance spherePolynomialSpace_finiteDimensional (m : ℕ) :
    FiniteDimensional ℝ (spherePolynomialSpace ι m) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem homogeneousSpherePolynomialSpace_le_filtration {j m : ℕ} (hjm : j ≤ m) :
    homogeneousSpherePolynomialSpace ι j ≤ spherePolynomialSpace ι m := by
  apply Submodule.span_le.mpr
  rintro f ⟨a,rfl⟩
  exact Submodule.subset_span ⟨⟨⟨j,by omega⟩,a⟩,rfl⟩

theorem spherePolynomialSpace_mono {m n : ℕ} (hmn : m ≤ n) :
    spherePolynomialSpace ι m ≤ spherePolynomialSpace ι n := by
  apply Submodule.span_le.mpr
  rintro f ⟨a,rfl⟩
  exact homogeneousSpherePolynomialSpace_le_filtration (by omega : a.1.val ≤ n)
    (Submodule.subset_span (Set.mem_range_self a.2))

theorem spherePolynomialSpace_finrank_upper (m : ℕ) :
    Module.finrank ℝ (spherePolynomialSpace ι m) ≤
      ∑ j : Fin (m+1), (Fintype.card ι+j.val-1).choose j.val := by
  have h := finrank_range_le_card (R := ℝ) (spherePolynomialGenerator (ι := ι) (m := m))
  have hcard : Fintype.card (SpherePolynomialIndex ι m) =
      ∑ j : Fin (m+1), (Fintype.card ι+j.val-1).choose j.val := by
    unfold SpherePolynomialIndex
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl fun j _ => Sym.card_sym_eq_choose j.val
  exact h.trans_eq hcard

theorem spherePolynomialSpace_eq_sup_predecessor (m : ℕ) :
    spherePolynomialSpace ι (m+1) = spherePolynomialSpace ι m ⊔ homogeneousSpherePolynomialSpace ι (m+1) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨a,rfl⟩
    by_cases ha : a.1.val ≤ m
    · exact (show spherePolynomialSpace ι m ≤ spherePolynomialSpace ι m ⊔
        homogeneousSpherePolynomialSpace ι (m+1) from le_sup_left)
        (homogeneousSpherePolynomialSpace_le_filtration ha
          (Submodule.subset_span (Set.mem_range_self a.2)))
    · have heq : a.1.val = m+1 := by omega
      apply (show homogeneousSpherePolynomialSpace ι (m+1) ≤ spherePolynomialSpace ι m ⊔
        homogeneousSpherePolynomialSpace ι (m+1) from le_sup_right)
      have haMem : sphereSymLp a.2 ∈ homogeneousSpherePolynomialSpace ι a.1.val :=
        Submodule.subset_span (Set.mem_range_self a.2)
      simpa only [spherePolynomialGenerator, heq] using haMem
  · exact sup_le (spherePolynomialSpace_mono (Nat.le_succ m))
      (homogeneousSpherePolynomialSpace_le_filtration le_rfl)

end
end KernelSeq
