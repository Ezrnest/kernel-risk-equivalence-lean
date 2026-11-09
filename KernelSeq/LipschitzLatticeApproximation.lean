import KernelSeq.LipschitzEvenSymbol
import KernelSeq.FiniteLipschitzFromHMS
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Actual integer approximation of Lipschitz graph multipliers

The same integer rounding is applied to every occurrence of a scalar label.
Repeated labels therefore remain exactly equal. Away from equal labels, the
fixed smooth planar symbol is continuous at the genuine graph difference.
This proves an actual finite-column and Schatten limit from integer grids;
it does not assume continuity of the homogeneous symbol at the origin.
-/

open Filter Topology

namespace KernelSeq
noncomputable section

def graphLatticeCoordinate (n : ℕ) (x : ℝ) : ℤ := ⌊((n : ℝ) + 1) * x⌋

def graphLatticeApproximation (n : ℕ) (x : ℝ) : ℝ :=
  (graphLatticeCoordinate n x : ℝ) / ((n : ℝ) + 1)

theorem graphLatticeApproximation_error (n : ℕ) (x : ℝ) :
    0 ≤ x - graphLatticeApproximation n x ∧
      x - graphLatticeApproximation n x ≤ 1 / ((n : ℝ) + 1) := by
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have h1 := Int.floor_le (((n : ℝ) + 1) * x)
  have h2 := Int.lt_floor_add_one (((n : ℝ) + 1) * x)
  unfold graphLatticeApproximation graphLatticeCoordinate
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · apply (sub_le_iff_le_add).mpr
    rw [← add_div]
    apply (le_div_iff₀ hd).mpr
    nlinarith

theorem graphLatticeApproximation_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => graphLatticeApproximation n x) atTop (𝓝 x) := by
  have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    have hd : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    convert! tendsto_inv_atTop_zero.comp hd using 1
    funext n
    simp only [one_div, Function.comp_apply]
  have he : Tendsto (fun n : ℕ => x - graphLatticeApproximation n x) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => (graphLatticeApproximation_error n x).1)
      (fun n => (graphLatticeApproximation_error n x).2) hi
  simpa only [sub_zero, sub_sub_cancel] using (tendsto_const_nhds (x := x)).sub he

/-- Genuine lattice graph differences use integer frequencies. -/
def graphLatticeMultiplier (n : ℕ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  lipschitzEvenSymbol
    ((graphLatticeCoordinate n x : ℝ) - (graphLatticeCoordinate n y : ℝ))
    ((graphLatticeCoordinate n (f x) : ℝ) - (graphLatticeCoordinate n (f y) : ℝ))

theorem graphLatticeMultiplier_eq_normalized (n : ℕ) (f : ℝ → ℝ) (x y : ℝ) :
    graphLatticeMultiplier n f x y =
      lipschitzEvenSymbol
        (graphLatticeApproximation n x - graphLatticeApproximation n y)
        (graphLatticeApproximation n (f x) - graphLatticeApproximation n (f y)) := by
  have hd : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hh := lipschitzEvenSymbol_homogeneous
    ((graphLatticeCoordinate n x : ℝ) - (graphLatticeCoordinate n y : ℝ))
    ((graphLatticeCoordinate n (f x) : ℝ) - (graphLatticeCoordinate n (f y) : ℝ))
    (r := ((n : ℝ) + 1)⁻¹) (inv_ne_zero hd)
  simpa only [graphLatticeMultiplier, graphLatticeApproximation, mul_sub,
    ← div_eq_inv_mul] using hh.symm

/-- The actual integer symbols converge to the zero-diagonal divided
difference, with no noncollision or graph approximation premise. -/
theorem graphLatticeMultiplier_tendsto {f : ℝ → ℝ}
    (hf : ∀ x y, |f x - f y| ≤ |x - y|) (x y : ℝ) :
    Tendsto (fun n : ℕ => graphLatticeMultiplier n f x y) atTop
      (𝓝 (dividedDifference f x y)) := by
  by_cases hxy : x = y
  · subst y
    simpa only [graphLatticeMultiplier, sub_self, lipschitzEvenSymbol_zero_left,
      dividedDifference, if_true] using (tendsto_const_nhds (x := (0 : ℝ)))
  · have hz : (x - y, f x - f y) ≠ (0 : ℝ × ℝ) := by
      intro h
      have hh := congrArg Prod.fst h
      exact hxy (sub_eq_zero.mp hh)
    have ht := ((graphLatticeApproximation_tendsto x).sub
      (graphLatticeApproximation_tendsto y)).prodMk_nhds
      ((graphLatticeApproximation_tendsto (f x)).sub
        (graphLatticeApproximation_tendsto (f y)))
    have hc := (lipschitzEvenSymbol_contDiffAt hz).continuousAt.tendsto.comp ht
    change Tendsto (fun n : ℕ => lipschitzEvenSymbol
      (graphLatticeApproximation n x - graphLatticeApproximation n y)
      (graphLatticeApproximation n (f x) - graphLatticeApproximation n (f y))) atTop
        (𝓝 (lipschitzEvenSymbol (x - y) (f x - f y))) at hc
    simpa only [← graphLatticeMultiplier_eq_normalized,
      ← dividedDifference_eq_lipschitzEvenSymbol hf x y] using hc

universe uι uκ uH uE
variable {ι : Type uι} {κ : Type uκ} {H : Type uH} {E : Type uE}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype ι] [Fintype κ]

omit [CompleteSpace E] in
/-- Actual finite HS-column convergence transfers the genuine integer-grid
approximation to the manuscript divided-difference matrix. -/
theorem graphLatticeColumns_tendsto (a : HilbertBasis κ ℝ E)
    (f : ℝ → ℝ) (hf : ∀ x y, |f x - f y| ≤ |x - y|)
    (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E) :
    Tendsto (fun n : ℕ => finiteMatrixSchurColumns a
      (fun i j => graphLatticeMultiplier n f (x i) (y j)) c) atTop
      (𝓝 (finiteMatrixSchurColumns a (lipschitzGridKernel f x y) c)) :=
  finiteMatrixSchurColumns_tendsto a _ _
    (fun i j => graphLatticeMultiplier_tendsto hf (x i) (y j)) c

/-- A genuine uniform integer-grid bound passes to the actual real graph.
This is a limit theorem; its displayed integer estimate remains a premise. -/
theorem realGraphSchur_le_of_lattice (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (f : ℝ → ℝ) (hf : ∀ x y, |f x - f y| ≤ |x - y|)
    (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E) {p C : ℝ}
    (hp : 2 ≤ p)
    (hbound : ∀ n : ℕ, hsSchattenNorm b (finiteMatrixSchurColumns a
      (fun i j => graphLatticeMultiplier n f (x i) (y j)) c) p ≤ C) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (lipschitzGridKernel f x y) c) p ≤ C := by
  have ht := (hsSchattenNorm_continuous b hp).continuousAt.tendsto.comp
    (graphLatticeColumns_tendsto a f hf x y c)
  exact le_of_tendsto ht (Filter.Eventually.of_forall hbound)

end
end KernelSeq
