import KernelSeq.LipschitzHMSReduction

/-!
# The finite Lipschitz Schur proposition follows from finite HMS

The actual Steklov profiles are C1, retain the original global Lipschitz
constant, and converge pointwise along nonzero smoothing scales. Their genuine
divided differences satisfy the proved HMS symbol conditions with bound `2L`.
Finite Schur columns converge by their actual finite single-column expansion;
continuity of the actual Schatten quantity passes the finite HMS bound to the
original Lipschitz profile. Equal scalar grid values have identically zero
divided-difference entries throughout the approximation.

Thus finite Lipschitz Schur is no longer an independent external premise on
the range p≥2 used in this project. No smooth approximation certificate or
operator multiplier identity is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelSeq

noncomputable section

/-- Pointwise convergence of the actual smoothed divided differences, including
coincident scalar values. No derivative convergence is required. -/
theorem steklov_dividedDifference_tendsto {f : ℝ → ℝ} (hf : Continuous f) (s t : ℝ) :
    Tendsto (fun ε : ℝ => dividedDifference (steklovProfile f ε) s t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (dividedDifference f s t)) := by
  by_cases hst : s = t
  · subst t
    simpa only [dividedDifference, if_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  · simp only [dividedDifference, if_neg hst]
    exact ((steklovProfile_tendsto hf s).sub (steklovProfile_tendsto hf t)).div_const (s - t)

/-- Removing the diagonal again leaves the divided-difference grid unchanged.
This is equality of actual scalar kernels, even for repeated grid values. -/
theorem offDiagonal_dividedDifference_grid_eq {ι κ : Type*}
    (f : ℝ → ℝ) (x : κ → ℝ) (y : ι → ℝ) :
    offDiagonalGridKernel (dividedDifference f) x y = lipschitzGridKernel f x y := by
  classical
  funext i j
  by_cases hij : x i = y j
  · simp only [offDiagonalGridKernel, lipschitzGridKernel, hij, if_true, dividedDifference]
  · simp only [offDiagonalGridKernel, lipschitzGridKernel, if_neg hij]

universe uι uκ uH uE
variable {ι : Type uι} {κ : Type uκ} {H : Type uH} {E : Type uE}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Finite

variable [Fintype ι] [Fintype κ]

omit [CompleteSpace E] in
/-- Coordinate limits imply actual HS-column convergence on a finite grid.
The proof uses finite sums in the existing HS Hilbert space. -/
theorem finiteMatrixSchurColumns_tendsto {J : Type*} {l : Filter J}
    (a : HilbertBasis κ ℝ E) (M : J → κ → ι → ℝ) (M₀ : κ → ι → ℝ)
    (hM : ∀ i j, Tendsto (fun n => M n i j) l (𝓝 (M₀ i j)))
    (c : HilbertSchmidtColumns ι E) :
    Tendsto (fun n => finiteMatrixSchurColumns a (M n) c) l (𝓝 (finiteMatrixSchurColumns a M₀ c)) := by
  classical
  unfold finiteMatrixSchurColumns
  exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun i _ => (hM i j).smul tendsto_const_nhds

/-- A finite C1 divided-difference estimate is supplied directly by the
universal finite HMS proposition, with the scalar factor two made explicit. -/
theorem finiteC1_lipschitzSchur_from_HMS {C L p : ℝ}
    (hFinite : FiniteHMS.{uι, uκ, uH, uE} C)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hL : 0 ≤ L)
    (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|) (hp : 2 ≤ p)
    (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (lipschitzGridKernel f x y) c) p ≤
      schurSchattenConstant (2 * C) p L * hsSchattenNorm b c p := by
  have hB := dividedDifference_hms hf hL hLip
  have ht := hFinite.bound b a x y (dividedDifference f) (2 * L) hB p (by linarith) c
  rw [← finiteMatrixSchurColumns_eq b a _ (2 * L) hB.bound_nonneg (hB.grid_norm_le x y) c,
    offDiagonal_dividedDifference_grid_eq] at ht
  exact ht.trans_eq (by unfold schurSchattenConstant; ring)

/-- The finite nonsmooth Lipschitz estimate is a consequence of the finite
HMS proposition and proved actual approximation and Schatten continuity. -/
theorem finiteLipschitz_grid_bound_from_HMS {C L p : ℝ}
    (hFinite : FiniteHMS.{uι, uκ, uH, uE} C)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ)
    (f : ℝ → ℝ) (hL : 0 ≤ L) (hLip : ∀ s t, |f s - f t| ≤ L * |s - t|) (hp : 2 ≤ p)
    (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (hsSchurMultiplier a (lipschitzGridKernel f x y) L hL
      (lipschitzGridKernel_norm_le hL hLip x y) c) p ≤
      schurSchattenConstant (2 * C) p L * hsSchattenNorm b c p := by
  have hf := continuous_of_abs_lipschitz hLip
  rw [← finiteMatrixSchurColumns_eq b a _ L hL (lipschitzGridKernel_norm_le hL hLip x y) c]
  have hcols := finiteMatrixSchurColumns_tendsto a
    (fun ε => lipschitzGridKernel (steklovProfile f ε) x y) (lipschitzGridKernel f x y)
    (fun i j => steklov_dividedDifference_tendsto hf (x i) (y j)) c
  have hlim := (hsSchattenNorm_continuous b hp).continuousAt.tendsto.comp hcols
  apply le_of_tendsto hlim
  have hne : ∀ᶠ ε : ℝ in 𝓝[≠] (0 : ℝ), ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hε
  filter_upwards [hne] with ε hε
  exact finiteC1_lipschitzSchur_from_HMS hFinite b a x y (steklovProfile f ε)
    (steklovProfile_contDiff hf ε) hL (steklovProfile_lipschitz hε hLip) hp c

end Finite

/-- The finite Lipschitz Schur proposition on the actual project range p≥2
is derived from the one general finite HMS proposition, with constant `2C`.
This removes an independent external assumption rather than renaming it. -/
theorem finiteLipschitzSchur_of_finiteHMS {C : ℝ}
    (hFinite : FiniteHMS.{uι, uκ, uH, uE} C) : FiniteLipschitzSchur.{uι, uκ, uH, uE} (2 * C) where
  constant_nonneg := mul_nonneg (by norm_num) hFinite.constant_nonneg
  bound := by
    intro ι κ _ _ H E _ _ _ _ _ _ b a x y f L hL hLip p hp c
    exact finiteLipschitz_grid_bound_from_HMS hFinite b a x y f hL hLip hp c

end
end KernelSeq
