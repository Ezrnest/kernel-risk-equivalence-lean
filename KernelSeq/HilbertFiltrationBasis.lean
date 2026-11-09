import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# An actual Hilbert basis from a dense finite-dimensional filtration

The orthogonal difference layers, their splitting and orthogonality are
derived from nestedness. Finite-dimensional orthonormal bases on these
layers are combined into a genuine Hilbert basis by proving dense span.
Neither a basis nor a decomposition certificate is an input.
-/

namespace KernelSeq
open Submodule Set
open scoped BigOperators
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hilbertFiltrationLayer (F : ℕ → Submodule ℝ E) : ℕ → Submodule ℝ E
  | 0 => F 0
  | m+1 => F (m+1) ⊓ (F m)ᗮ

theorem hilbertFiltrationLayer_le (F : ℕ → Submodule ℝ E) (m : ℕ) :
    hilbertFiltrationLayer F m ≤ F m := by
  cases m with
  | zero => exact le_rfl
  | succ m => exact inf_le_left

instance hilbertFiltrationLayer_finiteDimensional (F : ℕ → Submodule ℝ E)
    [∀ m, FiniteDimensional ℝ (F m)] (m : ℕ) :
    FiniteDimensional ℝ (hilbertFiltrationLayer F m) :=
  Submodule.finiteDimensional_of_le (hilbertFiltrationLayer_le F m)

theorem hilbertFiltration_succ_split (F : ℕ → Submodule ℝ E)
    [∀ m, FiniteDimensional ℝ (F m)] (hmono : Monotone F) (m : ℕ) :
    F m ⊔ hilbertFiltrationLayer F (m+1) = F (m+1) := by
  simpa only [hilbertFiltrationLayer, inf_comm] using
    (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hmono (Nat.le_succ m)))

theorem hilbertFiltrationLayer_iSup_eq (F : ℕ → Submodule ℝ E)
    [∀ m, FiniteDimensional ℝ (F m)] (hmono : Monotone F) :
    (⨆ m, hilbertFiltrationLayer F m) = ⨆ m, F m := by
  apply le_antisymm
  · exact iSup_le fun m => (hilbertFiltrationLayer_le F m).trans (le_iSup F m)
  · apply iSup_le
    intro m
    induction m with
    | zero => exact le_iSup (hilbertFiltrationLayer F) 0
    | succ m ih =>
      rw [← hilbertFiltration_succ_split F hmono m]
      exact sup_le ih (le_iSup (hilbertFiltrationLayer F) (m+1))

theorem hilbertFiltrationLayer_inner_eq_zero_of_lt (F : ℕ → Submodule ℝ E)
    (hmono : Monotone F) {i j : ℕ} (hij : i < j)
    {x y : E} (hx : x ∈ hilbertFiltrationLayer F i) (hy : y ∈ hilbertFiltrationLayer F j) :
    inner ℝ x y = 0 := by
  cases j with
  | zero => omega
  | succ j =>
    have hxf : x ∈ F j := hmono (Nat.le_of_lt_succ hij) (hilbertFiltrationLayer_le F i hx)
    exact (Submodule.mem_orthogonal (F j) y).mp hy.2 x hxf

theorem hilbertFiltrationLayer_orthogonal (F : ℕ → Submodule ℝ E) (hmono : Monotone F) :
    OrthogonalFamily ℝ (fun m => hilbertFiltrationLayer F m)
      (fun m => (hilbertFiltrationLayer F m).subtypeₗᵢ) := by
  intro i j hij x y
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hilbertFiltrationLayer_inner_eq_zero_of_lt F hmono hlt x.property y.property
  · rw [real_inner_comm]
    exact hilbertFiltrationLayer_inner_eq_zero_of_lt F hmono hgt y.property x.property

def hilbertFiltrationVectors (F : ℕ → Submodule ℝ E) [∀ m, FiniteDimensional ℝ (F m)] :
    (Σ m : ℕ, Fin (Module.finrank ℝ (hilbertFiltrationLayer F m))) → E :=
  fun p => (stdOrthonormalBasis ℝ (hilbertFiltrationLayer F p.1) p.2 : E)

theorem hilbertFiltrationVectors_orthonormal (F : ℕ → Submodule ℝ E)
    [∀ m, FiniteDimensional ℝ (F m)] (hmono : Monotone F) :
    Orthonormal ℝ (hilbertFiltrationVectors F) :=
  (hilbertFiltrationLayer_orthogonal F hmono).orthonormal_sigma_orthonormal
    (fun m => (stdOrthonormalBasis ℝ (hilbertFiltrationLayer F m)).orthonormal)

theorem hilbertFiltrationVectors_layer_span (F : ℕ → Submodule ℝ E)
    [∀ m, FiniteDimensional ℝ (F m)] (m : ℕ) :
    Submodule.span ℝ (Set.range (fun j : Fin (Module.finrank ℝ (hilbertFiltrationLayer F m)) =>
      (stdOrthonormalBasis ℝ (hilbertFiltrationLayer F m) j : E))) =
      hilbertFiltrationLayer F m := by
  let b := stdOrthonormalBasis ℝ (hilbertFiltrationLayer F m)
  apply (Submodule.span_range_subtype_eq_top_iff (hilbertFiltrationLayer F m)
    (fun j => (b j).property)).mp
  exact b.toBasis.span_eq

theorem hilbertFiltrationVectors_span (F : ℕ → Submodule ℝ E)
    [∀ m, FiniteDimensional ℝ (F m)] (hmono : Monotone F) :
    Submodule.span ℝ (Set.range (hilbertFiltrationVectors F)) = ⨆ m, F m := by
  rw [Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]
  simp only [hilbertFiltrationVectors, hilbertFiltrationVectors_layer_span]
  exact hilbertFiltrationLayer_iSup_eq F hmono

variable [CompleteSpace E]

/-- The actual complete orthonormal basis indexed by finite difference-layer
coordinates. Dense span is proved from the original filtration hypothesis. -/
def hilbertFiltrationBasis (F : ℕ → Submodule ℝ E) [∀ m, FiniteDimensional ℝ (F m)]
    (hmono : Monotone F) (hdense : (⨆ m, F m).topologicalClosure = ⊤) :
    HilbertBasis (Σ m : ℕ, Fin (Module.finrank ℝ (hilbertFiltrationLayer F m))) ℝ E :=
  HilbertBasis.mk (hilbertFiltrationVectors_orthonormal F hmono)
    (by rw [hilbertFiltrationVectors_span F hmono, hdense])

theorem hilbertFiltrationBasis_apply (F : ℕ → Submodule ℝ E)
    [∀ m, FiniteDimensional ℝ (F m)] (hmono : Monotone F)
    (hdense : (⨆ m, F m).topologicalClosure = ⊤)
    (p : Σ m : ℕ, Fin (Module.finrank ℝ (hilbertFiltrationLayer F m))) :
    hilbertFiltrationBasis F hmono hdense p =
      (stdOrthonormalBasis ℝ (hilbertFiltrationLayer F p.1) p.2 : E) := by
  rw [hilbertFiltrationBasis, HilbertBasis.coe_mk]
  rfl

theorem hilbertFiltrationBasis_mem_layer (F : ℕ → Submodule ℝ E)
    [∀ m, FiniteDimensional ℝ (F m)] (hmono : Monotone F)
    (hdense : (⨆ m, F m).topologicalClosure = ⊤)
    (p : Σ m : ℕ, Fin (Module.finrank ℝ (hilbertFiltrationLayer F m))) :
    hilbertFiltrationBasis F hmono hdense p ∈ hilbertFiltrationLayer F p.1 := by
  rw [hilbertFiltrationBasis_apply]
  exact (stdOrthonormalBasis ℝ (hilbertFiltrationLayer F p.1) p.2).property

end
end KernelSeq
