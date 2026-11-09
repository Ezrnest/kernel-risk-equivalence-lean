import KernelSeq.FiniteSchurExtension
import KernelSeq.CompactDOI
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Explicit finite analytic Schur leaves and their proved extension

`FiniteLipschitzSchur` and `FiniteHMS` are named external propositions. They
are not axioms, and neither proposition is proved in this file. Every theorem
using them displays the corresponding hypothesis. They concern only general
scalar grids and Schur symbols, not a regression filter or an interaction.

Primary sources:
* Caspers--Montgomery-Smith--Potapov--Sukochev, Theorem 5.1:
  https://stephenmontgomerysmith.github.io/preprints/op-lip2.pdf
* Conde-Alonso--Gonzalez-Perez--Parcet--Tablate, Theorem A and Remark 2.1:
  https://arxiv.org/html/2201.05511

The finite real rectangular-grid specialization, zero diagonal convention,
and any complex-to-real restriction needed to connect those sources are part
of the explicitly unproved finite leaves. They are not asserted to have been
formalized. Given a leaf, the passage to the actual infinite HS DOI and its
finite Schatten bound is proved by `FiniteSchurExtension`.
-/

namespace KernelSeq

noncomputable section

/-- The one-dimensional HMS regularity domain. -/
def schurOffDiagonal : Set (ℝ × ℝ) := {z | z.1 ≠ z.2}

/-- The full bounded one-dimensional symbol controls used for HMS. Smoothness
is required away from the diagonal; the two derivative bounds are the genuine
one-variable partial derivatives there. Diagonal values are globally bounded
but are discarded by the grid kernel below. -/
structure HMSBoundedSymbol (M : ℝ → ℝ → ℝ) (B : ℝ) : Prop where
  bound_nonneg : 0 ≤ B
  smooth_offDiagonal : ContDiffOn ℝ 1 (Function.uncurry M) schurOffDiagonal
  size_bound : ∀ s t, |M s t| ≤ B
  deriv_left_bound : ∀ s t, s ≠ t → |s - t| * |deriv (fun u => M u t) s| ≤ B
  deriv_right_bound : ∀ s t, s ≠ t → |s - t| * |deriv (fun u => M s u) t| ≤ B

/-- The exact `p²/(p-1)` growth, with its universal external constant and
scalar profile or symbol bound shown separately. -/
def schurSchattenConstant (C p B : ℝ) : ℝ := C * (p ^ 2 / (p - 1)) * B

theorem schurSchattenConstant_nonneg {C p B : ℝ} (hC : 0 ≤ C) (hp : 1 < p) (hB : 0 ≤ B) :
    0 ≤ schurSchattenConstant C p B :=
  mul_nonneg (mul_nonneg hC (div_nonneg (sq_nonneg _) (by linarith))) hB

/-- On the formalized range `p ≥ 2`, the sharp growth is at most `2p`.
This scalar reduction is proved and is separate from the external multiplier
leaves. -/
theorem schurSchattenConstant_le_two_mul {C p B : ℝ}
    (hC : 0 ≤ C) (hp : 2 ≤ p) (hB : 0 ≤ B) :
    schurSchattenConstant C p B ≤ 2 * C * p * B := by
  have hrat : p ^ 2 / (p - 1) ≤ 2 * p := by
    apply (div_le_iff₀ (by linarith : 0 < p - 1)).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ p) (by linarith : 0 ≤ p - 2)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrat hC) hB).trans_eq (by ring)

/-- The actual off-diagonal symbol on any two scalar grids. Equality is tested
on the scalar grid values, so repeated labels at the same scalar value also
receive the zero diagonal convention. -/
def offDiagonalGridKernel {ι κ : Type*} (M : ℝ → ℝ → ℝ)
    (x : κ → ℝ) (y : ι → ℝ) (i : κ) (j : ι) : ℝ :=
  if x i = y j then 0 else M (x i) (y j)

theorem HMSBoundedSymbol.grid_norm_le {ι κ : Type*} {M : ℝ → ℝ → ℝ} {B : ℝ}
    (h : HMSBoundedSymbol M B) (x : κ → ℝ) (y : ι → ℝ) (i : κ) (j : ι) :
    ‖offDiagonalGridKernel M x y i j‖ ≤ B := by
  classical
  unfold offDiagonalGridKernel
  split_ifs
  · simpa only [norm_zero] using h.bound_nonneg
  · exact h.size_bound _ _

/-- The zero-diagonal divided-difference kernel on arbitrary scalar grids. -/
def lipschitzGridKernel {ι κ : Type*} (f : ℝ → ℝ)
    (x : κ → ℝ) (y : ι → ℝ) (i : κ) (j : ι) : ℝ :=
  dividedDifference f (x i) (y j)

theorem lipschitzGridKernel_norm_le {ι κ : Type*} {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|)
    (x : κ → ℝ) (y : ι → ℝ) (i : κ) (j : ι) :
    ‖lipschitzGridKernel f x y i j‖ ≤ L :=
  dividedDifference_norm_le hL (hLip _ _)

universe uι uκ uH uE

/-- Explicit external finite real-grid Lipschitz Schur proposition, motivated
by the one-dimensional off-diagonal form of Caspers et al., Theorem 5.1.
This universal finite leaf is not proved here. In particular its real and
two-grid specialization is not supplied by an implicit complexification rule.
Any fixed diagonal-zeroing or restriction factors are absorbed in `C`.
Finite index types, including empty types and repeated scalar grid values,
are quantified directly. Only the range `p ≥ 2` used by the main theorem is
required; the bound is not a filter-specific premise. -/
structure FiniteLipschitzSchur (C : ℝ) : Prop where
  constant_nonneg : 0 ≤ C
  bound : ∀ {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    {H : Type uH} {E : Type uE}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ)
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|)
    (p : ℝ), 2 ≤ p → ∀ c : HilbertSchmidtColumns ι E,
      hsSchattenNorm b (hsSchurMultiplier a (lipschitzGridKernel f x y) L hL
        (lipschitzGridKernel_norm_le hL hLip x y) c) p ≤
      schurSchattenConstant C p L * hsSchattenNorm b c p

/-- Explicit external finite real-grid HMS proposition for a general bounded
`C¹` symbol away from the diagonal. Theorem A and Remark 2.1 of Conde-Alonso
et al. motivate the growth `p²/(p-1)`; the universal constant absorbs the fixed
one-dimensional derivative-sum factors. Its finite real zero-diagonal grid
form remains an unproved external leaf, not an asserted source derivation. -/
structure FiniteHMS (C : ℝ) : Prop where
  constant_nonneg : 0 ≤ C
  bound : ∀ {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    {H : Type uH} {E : Type uE}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ)
    (M : ℝ → ℝ → ℝ) (B : ℝ) (hB : HMSBoundedSymbol M B) (p : ℝ), 1 < p →
    ∀ c : HilbertSchmidtColumns ι E,
      hsSchattenNorm b (hsSchurMultiplier a (offDiagonalGridKernel M x y) B hB.bound_nonneg
        (hB.grid_norm_le x y) c) p ≤
      schurSchattenConstant C p B * hsSchattenNorm b c p

variable {ι : Type uι} {κ : Type uκ} {H : Type uH} {E : Type uE}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace H] [CompleteSpace E] in
/-- The universal finite Lipschitz leaf supplies the actual selected-grid
finite multiplier premise, with original basis labels retained. -/
theorem finiteLipschitzSchur_selected_bound {C p L : ℝ}
    (hFinite : FiniteLipschitzSchur.{uι, uκ, uH, uE} C)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ)
    (f : ℝ → ℝ) (hL : 0 ≤ L) (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|) (hp : 2 ≤ p) :
    FiniteSchurSchattenBound b a (lipschitzGridKernel f x y) L hL
      (lipschitzGridKernel_norm_le hL hLip x y) p (schurSchattenConstant C p L) := by
  intro s t c
  exact hFinite.bound (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
    (fun i : t => x i) (fun j : s => y j) f L hL hLip p hp c

/-- Conditional on the named finite Lipschitz theorem, its exact finite
Schatten constant holds for the actual infinite HS divided-difference DOI.
The extension and its HS output are constructed rather than postulated. -/
theorem infiniteLipschitzSchur_bound {C p L : ℝ}
    (hFinite : FiniteLipschitzSchur.{uι, uκ, uH, uE} C)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ)
    (f : ℝ → ℝ) (hL : 0 ≤ L) (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|) (hp : 2 ≤ p)
    (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (hsSchurMultiplier a (lipschitzGridKernel f x y) L hL
      (lipschitzGridKernel_norm_le hL hLip x y) c) p ≤
      schurSchattenConstant C p L * hsSchattenNorm b c p :=
  hsSchur_schatten_bound_of_finite b a _ L hL _ hp
    (schurSchattenConstant_nonneg hFinite.constant_nonneg (by linarith) hL)
    (finiteLipschitzSchur_selected_bound hFinite b a x y f hL hLip hp) c

omit [CompleteSpace H] [CompleteSpace E] in
/-- The universal finite HMS leaf supplies the actual selected finite-grid
multiplier bound. No infinite HMS estimate is hidden in this instantiation. -/
theorem finiteHMS_selected_bound {C p B : ℝ}
    (hFinite : FiniteHMS.{uι, uκ, uH, uE} C)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ)
    (M : ℝ → ℝ → ℝ) (hB : HMSBoundedSymbol M B) (hp : 1 < p) :
    FiniteSchurSchattenBound b a (offDiagonalGridKernel M x y) B hB.bound_nonneg
      (hB.grid_norm_le x y) p (schurSchattenConstant C p B) := by
  intro s t c
  exact hFinite.bound (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
    (fun i : t => x i) (fun j : s => y j) M B hB p hp c

/-- Conditional on the named finite HMS theorem, its exact growth bound holds
for the actual infinite HS Schur DOI. No separability, infinite multiplier
certificate, or project-specific interaction hypothesis is added. -/
theorem infiniteHMS_bound {C p B : ℝ}
    (hFinite : FiniteHMS.{uι, uκ, uH, uE} C)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ)
    (M : ℝ → ℝ → ℝ) (hB : HMSBoundedSymbol M B) (hp : 2 ≤ p)
    (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (hsSchurMultiplier a (offDiagonalGridKernel M x y) B hB.bound_nonneg
      (hB.grid_norm_le x y) c) p ≤
      schurSchattenConstant C p B * hsSchattenNorm b c p :=
  hsSchur_schatten_bound_of_finite b a _ B hB.bound_nonneg _ hp
    (schurSchattenConstant_nonneg hFinite.constant_nonneg (by linarith) hB.bound_nonneg)
    (finiteHMS_selected_bound hFinite b a x y M hB (by linarith)) c

end
end KernelSeq
