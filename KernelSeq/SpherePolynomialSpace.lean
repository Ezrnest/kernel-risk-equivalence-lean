import KernelSeq.SphereMonomialBlock
import Mathlib.Data.Sym.Card
import Mathlib.Data.Multiset.Pi

/-!
# Actual finite polynomial subspaces on the uniform sphere

Unordered tensor words retain the exact stars-and-bars dimension bound.
The actual squarefree L2 block supplies the matching leading lower bound;
no harmonic dimension or spectral multiplicity is assumed.
-/

namespace KernelSeq
open MeasureTheory Submodule Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def sphereMultisetMonomial (a : Multiset ι) (x : KernelSphere (EuclideanSpace ℝ ι)) : ℝ :=
  (a.map (fun i => (x : EuclideanSpace ℝ ι) i)).prod

omit [Nonempty ι] [DecidableEq ι] in
theorem sphereMultisetMonomial_continuous (a : Multiset ι) : Continuous (sphereMultisetMonomial a) := by
  induction a using Multiset.induction_on with
  | empty =>
    have he : sphereMultisetMonomial (0 : Multiset ι) =
        (fun _ : KernelSphere (EuclideanSpace ℝ ι) => (1 : ℝ)) := by funext x; rfl
    rw [he]
    exact continuous_const
  | @cons i a ih =>
    have he : sphereMultisetMonomial (i ::ₘ a) =
        fun x : KernelSphere (EuclideanSpace ℝ ι) => (x : EuclideanSpace ℝ ι) i * sphereMultisetMonomial a x := by
      funext x
      simp only [sphereMultisetMonomial, Multiset.map_cons, Multiset.prod_cons]
    rw [he]
    exact (show Continuous (fun x : KernelSphere (EuclideanSpace ℝ ι) =>
      (x : EuclideanSpace ℝ ι) i) by fun_prop).mul ih

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereMultisetMonomial_abs_le_one (a : Multiset ι) (x : KernelSphere (EuclideanSpace ℝ ι)) :
    |sphereMultisetMonomial a x| ≤ 1 := by
  induction a using Multiset.induction_on with
  | empty => simp [sphereMultisetMonomial]
  | @cons i a ih =>
    simp only [sphereMultisetMonomial, Multiset.map_cons, Multiset.prod_cons, abs_mul] at *
    exact mul_le_one₀ (sphereCoordinate_abs_le_one x i) (abs_nonneg _) ih

omit [DecidableEq ι] in
theorem sphereMultisetMonomial_memLp (a : Multiset ι) :
    MemLp (sphereMultisetMonomial a) 2 (uniformSphere (E := EuclideanSpace ℝ ι)) :=
  MemLp.of_bound (sphereMultisetMonomial_continuous a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using sphereMultisetMonomial_abs_le_one a x)

def sphereSymLp {m : ℕ} (a : Sym ι m) : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)) :=
  (sphereMultisetMonomial_memLp a.val).toLp (sphereMultisetMonomial a.val)

def homogeneousSpherePolynomialSpace (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (m : ℕ) : Submodule ℝ (Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) :=
  span ℝ (Set.range (sphereSymLp (ι := ι) (m := m)))

instance homogeneousSpherePolynomialSpace_finiteDimensional (m : ℕ) :
    FiniteDimensional ℝ (homogeneousSpherePolynomialSpace ι m) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem homogeneousSpherePolynomialSpace_finrank_upper (m : ℕ) :
    Module.finrank ℝ (homogeneousSpherePolynomialSpace ι m) ≤ (Fintype.card ι+m-1).choose m := by
  exact (finrank_range_le_card (R := ℝ) (sphereSymLp (ι := ι) (m := m))).trans_eq (Sym.card_sym_eq_choose m)

theorem squarefreeSphereLp_eq_symLp {m : ℕ} (s : SquarefreeSphereIndex ι m) :
    squarefreeSphereLp s = sphereSymLp (Sym.mk s.val.val (squarefreeSphereIndex_card s)) := by
  unfold squarefreeSphereLp sphereSymLp
  apply Lp.ext
  filter_upwards [(sphereCoordinateProduct_memLp s.val).coeFn_toLp,
    (sphereMultisetMonomial_memLp s.val.val).coeFn_toLp] with x hx hy
  exact hx.trans (by exact hy.symm)

theorem squarefreeSphereBlock_le_homogeneous (m : ℕ) :
    squarefreeSphereBlock ι m ≤ homogeneousSpherePolynomialSpace ι m := by
  apply Submodule.span_le.mpr
  rintro f ⟨s,rfl⟩
  apply Submodule.smul_mem
  rw [squarefreeSphereLp_eq_symLp]
  exact Submodule.subset_span (Set.mem_range_self _)

theorem homogeneousSpherePolynomialSpace_finrank_lower (m : ℕ) :
    (Fintype.card ι).choose m ≤ Module.finrank ℝ (homogeneousSpherePolynomialSpace ι m) := by
  rw [← squarefreeSphereBlock_finrank (ι := ι) m]
  exact Submodule.finrank_mono (squarefreeSphereBlock_le_homogeneous m)

end
end KernelSeq
