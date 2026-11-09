import KernelSeq.LipschitzLatticeApproximation
import KernelSeq.DyadicSchattenEndpoint
import KernelSeq.ChiSchurDyadic

/-!
# The exact finite Lipschitz range needed by localization

Only the dyadic exponents enter the actual localized estimate. This narrower
interface asks for genuine finite matrix columns, including zero diagonal and
repeated labels. A proved integer approximation reduces its one-Lipschitz
case to the single fixed planar symbol. The estimates remain explicit inputs
to this modular layer; `FixedSymbolFourierLpBound` supplies the actual
`fixedEvenFourierLpBound_proved` and `finiteDyadicLipschitzSchur_proved`
constructors. This does not assert the broader all-exponent interface.
-/

open Filter Topology

namespace KernelSeq
noncomputable section

universe uι uκ uH uE

/-- The finite Lipschitz interface restricted to the needed dyadic exponents.
Its actual constructor `finiteDyadicLipschitzSchur_proved` is proved separately
in `FixedSymbolFourierLpBound`. -/
structure FiniteDyadicLipschitzSchur (C : ℝ) : Prop where
  constant_nonneg : 0 ≤ C
  bound : ∀ {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    {H : Type uH} {E : Type uE}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ)
    (f : ℝ → ℝ) (L : ℝ) (_hL : 0 ≤ L) (_hLip : ∀ s t, |f s - f t| ≤ L * |s - t|)
    (m : ℕ) (c : HilbertSchmidtColumns ι E),
      hsSchattenNorm b (finiteMatrixSchurColumns a (lipschitzGridKernel f x y) c)
          (dyadicSchattenExponent m) ≤
        schurSchattenConstant C (dyadicSchattenExponent m) L *
          hsSchattenNorm b c (dyadicSchattenExponent m)

/-- The older all-exponent proposition supplies the narrower dyadic one,
without an interpolation premise or constant loss. -/
theorem FiniteLipschitzSchur.toDyadic {C : ℝ}
    (h : FiniteLipschitzSchur.{uι, uκ, uH, uE} C) :
    FiniteDyadicLipschitzSchur.{uι, uκ, uH, uE} C where
  constant_nonneg := h.constant_nonneg
  bound := by
    intro ι κ _ _ H E _ _ _ _ _ _ b a x y f L hL hf m c
    have ht := h.bound b a x y f L hL hf (dyadicSchattenExponent m)
      (dyadicSchattenExponent_ge_two m) c
    rw [← finiteMatrixSchurColumns_eq b a _ L hL (lipschitzGridKernel_norm_le hL hf x y) c] at ht
    exact ht

variable {ι : Type uι} {κ : Type uκ} {H : Type uH} {E : Type uE}
  [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [Fintype ι] [Fintype κ] in
/-- Actual scaling of the finite divided-difference matrix, including its
zero diagonal, handles an arbitrary positive Lipschitz constant. -/
theorem lipschitzGridKernel_div_scale (f : ℝ → ℝ) {L : ℝ} (hL : L ≠ 0)
    (x : κ → ℝ) (y : ι → ℝ) :
    lipschitzGridKernel f x y = fun i j => L * lipschitzGridKernel (fun t => f t / L) x y i j := by
  funext i j
  simp only [lipschitzGridKernel, dividedDifference]
  split_ifs
  · ring
  · field_simp

/-- A uniform bound for the fixed symbol on arbitrary integer rectangular
grids implies the actual dyadic divided-difference bound. The integer bound
is the displayed modular input; rounding and real-grid passage are proved. -/
theorem finiteDyadicLipschitz_grid_le_of_integer {C : ℝ} (hC : 0 ≤ C)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (hinteger : ∀ (x : κ → ℤ × ℤ) (y : ι → ℤ × ℤ) (m : ℕ)
      (c : HilbertSchmidtColumns ι E), hsSchattenNorm b (finiteMatrixSchurColumns a
        (fun i j => lipschitzEvenSymbol ((x i).1 - (y j).1) ((x i).2 - (y j).2)) c)
          (dyadicSchattenExponent m) ≤
        C * dyadicSchattenExponent m * hsSchattenNorm b c (dyadicSchattenExponent m))
    (x : κ → ℝ) (y : ι → ℝ) (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ s t, |f s - f t| ≤ L * |s - t|) (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (lipschitzGridKernel f x y) c)
        (dyadicSchattenExponent m) ≤
      schurSchattenConstant C (dyadicSchattenExponent m) L *
        hsSchattenNorm b c (dyadicSchattenExponent m) := by
  let p := dyadicSchattenExponent m
  have hp : 2 ≤ p := dyadicSchattenExponent_ge_two m
  have hSp := hsSchattenNorm_nonneg b c p
  by_cases hL0 : L = 0
  · subst L
    have hk : lipschitzGridKernel f x y = fun _ _ => 0 := by
      funext i j
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [zero_mul] using lipschitzGridKernel_norm_le hL hf x y i j)
        (norm_nonneg _)
    rw [hk, finiteMatrixSchurColumns_const, zero_smul]
    change hsSchattenNorm b 0 p ≤ schurSchattenConstant C p 0 * hsSchattenNorm b c p
    rw [hsSchattenNorm_zero b hp]
    simp only [schurSchattenConstant, mul_zero, zero_mul, le_refl]
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    let g := fun t => f t / L
    have hg : ∀ s t, |g s - g t| ≤ |s - t| := by
      intro s t
      dsimp only [g]
      rw [← sub_div, abs_div, abs_of_pos hLpos]
      exact (div_le_iff₀ hLpos).mpr (by simpa only [mul_comm] using hf s t)
    have hgBound : hsSchattenNorm b (finiteMatrixSchurColumns a (lipschitzGridKernel g x y) c) p ≤
        C * p * hsSchattenNorm b c p := by
      apply realGraphSchur_le_of_lattice b a g hg x y c hp
      intro n
      exact hinteger
        (fun i => (graphLatticeCoordinate n (x i), graphLatticeCoordinate n (g (x i))))
        (fun j => (graphLatticeCoordinate n (y j), graphLatticeCoordinate n (g (y j)))) m c
    rw [lipschitzGridKernel_div_scale f hL0 x y, finiteMatrixSchurColumns_smul,
      hsSchattenNorm_smul b _ L hp, abs_of_pos hLpos]
    have hfrac : p ≤ p ^ 2 / (p - 1) := by
      apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_left hgBound hL).trans (by
      unfold schurSchattenConstant
      have ht := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfrac hC) (mul_nonneg hL hSp)
      nlinarith)

end
end KernelSeq
