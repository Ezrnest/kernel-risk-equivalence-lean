import KernelSeq.SpherePolynomialFiltration
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Genuine orthogonal layers of the spherical polynomial filtration

The layers are constructed as finite-subspace orthogonal differences. A
self-adjoint operator acting by a scalar modulo lower polynomials acts by
that scalar on the actual layer; this is proved by orthogonality.
-/

namespace KernelSeq
open MeasureTheory Submodule Set
noncomputable section

section GenericLayer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem symmetric_eigen_of_scalar_mod_lower
    (T : E →L[ℝ] E) (hT : T.IsSymmetric) (U V : Submodule ℝ E) (c : ℝ)
    (hU : ∀ u ∈ U, T u ∈ U)
    (hmod : ∀ v ∈ V, T v-c • v ∈ U)
    {x : E} (hx : x ∈ V ⊓ Uᗮ) : T x = c • x := by
  have hr : T x-c • x ∈ U := hmod x hx.1
  have ho : T x-c • x ∈ Uᗮ := by
    change ∀ u ∈ U, inner ℝ u (T x-c • x) = 0
    intro u hu
    have hux : inner ℝ u x = 0 := Submodule.inner_right_of_mem_orthogonal hu hx.2
    have hTu : inner ℝ u (T x) = 0 :=
      (hT u x).symm.trans (Submodule.inner_right_of_mem_orthogonal (hU u hu) hx.2)
    simp only [inner_sub_right, inner_smul_right, hTu, hux, mul_zero, sub_zero]
  have hn := Submodule.inner_right_of_mem_orthogonal hr ho
  rw [real_inner_self_eq_norm_sq] at hn
  have hz : T x-c • x = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (T x-c • x)])
  exact sub_eq_zero.mp hz

end GenericLayer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def spherePolynomialLayer (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ℕ → Submodule ℝ (Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))
  | 0 => spherePolynomialSpace ι 0
  | m+1 => spherePolynomialSpace ι (m+1) ⊓ (spherePolynomialSpace ι m)ᗮ

theorem spherePolynomialLayer_le_filtration (m : ℕ) :
    spherePolynomialLayer ι m ≤ spherePolynomialSpace ι m := by
  cases m <;> simp only [spherePolynomialLayer, le_refl, inf_le_left]

instance spherePolynomialLayer_finiteDimensional (m : ℕ) :
    FiniteDimensional ℝ (spherePolynomialLayer ι m) :=
  Submodule.finiteDimensional_of_le (spherePolynomialLayer_le_filtration m)

theorem spherePolynomialSpace_sup_layer (m : ℕ) :
    spherePolynomialSpace ι m ⊔ spherePolynomialLayer ι (m+1) = spherePolynomialSpace ι (m+1) := by
  simpa only [spherePolynomialLayer, inf_comm] using
    Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      (spherePolynomialSpace_mono (ι := ι) (Nat.le_succ m))

theorem spherePolynomialLayer_finrank_add (m : ℕ) :
    Module.finrank ℝ (spherePolynomialSpace ι m) +
      Module.finrank ℝ (spherePolynomialLayer ι (m+1)) = Module.finrank ℝ (spherePolynomialSpace ι (m+1)) := by
  rw [spherePolynomialLayer, inf_comm (spherePolynomialSpace ι (m+1))]
  exact Submodule.finrank_add_inf_finrank_orthogonal
    (spherePolynomialSpace_mono (ι := ι) (Nat.le_succ m))

theorem spherePolynomialLayer_inner_eq_zero_of_lt {j m : ℕ} (hjm : j < m)
    {x y : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))}
    (hx : x ∈ spherePolynomialLayer ι j) (hy : y ∈ spherePolynomialLayer ι m) : inner ℝ x y = 0 := by
  cases m with
  | zero => omega
  | succ m =>
    exact Submodule.inner_right_of_mem_orthogonal
      (spherePolynomialSpace_mono (by omega : j ≤ m) (spherePolynomialLayer_le_filtration j hx)) hy.2

theorem spherePolynomialLayer_pairwise_orthogonal :
    Pairwise (fun j m : ℕ => (spherePolynomialLayer ι j) ⟂ (spherePolynomialLayer ι m)) := by
  intro j m hjm x hx y hy
  change inner ℝ y x = 0
  rcases lt_or_gt_of_ne hjm with hj | hm
  · rw [real_inner_comm]
    exact spherePolynomialLayer_inner_eq_zero_of_lt hj hx hy
  · exact spherePolynomialLayer_inner_eq_zero_of_lt hm hy hx

theorem spherePolynomialSpace_eq_iSup_layers (m : ℕ) :
    spherePolynomialSpace ι m = ⨆ j ≤ m, spherePolynomialLayer ι j := by
  apply le_antisymm
  · induction m with
    | zero => exact le_iSup_of_le 0 (le_iSup_of_le le_rfl le_rfl)
    | succ m ih =>
      rw [← spherePolynomialSpace_sup_layer]
      apply sup_le
      · exact ih.trans (iSup_le fun j => iSup_le fun hj =>
          le_iSup_of_le j (le_iSup_of_le (Nat.le_succ_of_le hj) le_rfl))
      · exact le_iSup_of_le (m+1) (le_iSup_of_le le_rfl le_rfl)
  · exact iSup_le fun j => iSup_le fun hj =>
      (spherePolynomialLayer_le_filtration j).trans (spherePolynomialSpace_mono hj)

end
end KernelSeq
