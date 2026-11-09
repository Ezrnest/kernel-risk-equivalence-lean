import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Monotonicity and constant absorption for the logarithmic Schatten rate

The endpoint optimization itself is proved separately. Here the scalar rate
`x log (e + c/x)` is proved monotone in both nonnegative arguments, with its
value at `x = 0` explicitly set to zero. Common dilation then absorbs the two
constants in the operator-norm and Hilbert--Schmidt estimates.
-/

namespace KernelSeq

/-- The logarithmic endpoint rate, with the manuscript's zero convention. -/
noncomputable def logarithmicRate (x c : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.log (Real.exp 1 + c / x)

@[simp]
theorem logarithmicRate_zero (c : ℝ) : logarithmicRate 0 c = 0 := by
  simp [logarithmicRate]

theorem logarithmicRate_of_pos {x : ℝ} (hx : 0 < x) (c : ℝ) :
    logarithmicRate x c = x * Real.log (Real.exp 1 + c / x) := by
  simp only [logarithmicRate, if_neg (ne_of_gt hx)]

/-- Concavity of the logarithm proves monotonicity in the positive first
argument, including `c = 0`, without differentiability at the origin. -/
theorem mul_log_exp_add_div_mono_left {x y c : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hc : 0 ≤ c) :
    x * Real.log (Real.exp 1 + c / x) ≤ y * Real.log (Real.exp 1 + c / y) := by
  have hy : 0 < y := hx.trans_le hxy
  have ht : 0 ≤ x / y := div_nonneg hx.le hy.le
  have ht1 : 0 ≤ 1 - x / y := sub_nonneg.mpr ((div_le_one hy).2 hxy)
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2
    (show Real.exp 1 + c / x ∈ Set.Ioi (0 : ℝ) from
      add_pos_of_pos_of_nonneg (Real.exp_pos _) (div_nonneg hc hx.le))
    (show Real.exp 1 ∈ Set.Ioi (0 : ℝ) from Real.exp_pos _)
    ht ht1 (show x / y + (1 - x / y) = 1 by ring)
  have harg : x / y * (Real.exp 1 + c / x) + (1 - x / y) * Real.exp 1 =
      Real.exp 1 + c / y := by
    field_simp
    ring
  simp only [smul_eq_mul, Real.log_exp, harg] at hconc
  have hlog : x / y * Real.log (Real.exp 1 + c / x) ≤
      Real.log (Real.exp 1 + c / y) := by linarith
  calc
    x * Real.log (Real.exp 1 + c / x) =
        y * (x / y * Real.log (Real.exp 1 + c / x)) := by field_simp
    _ ≤ y * Real.log (Real.exp 1 + c / y) := mul_le_mul_of_nonneg_left hlog hy.le

/-- Monotonicity in the second argument at a positive first argument. -/
theorem mul_log_exp_add_div_mono_right {x c d : ℝ}
    (hx : 0 < x) (hc : 0 ≤ c) (hcd : c ≤ d) :
    x * Real.log (Real.exp 1 + c / x) ≤ x * Real.log (Real.exp 1 + d / x) := by
  apply mul_le_mul_of_nonneg_left _ hx.le
  apply Real.log_le_log
  · exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (div_nonneg hc hx.le)
  · exact add_le_add le_rfl (div_le_div_of_nonneg_right hcd hx.le)

/-- The logarithmic factor is at least one on the intended domain. -/
theorem one_le_log_exp_add_div {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) :
    1 ≤ Real.log (Real.exp 1 + c / x) := by
  have h := Real.log_le_log (Real.exp_pos 1)
    (le_add_of_nonneg_right (div_nonneg hc hx.le))
  simpa only [Real.log_exp] using h

/-- Nonnegativity includes the explicit zero convention. -/
theorem logarithmicRate_nonneg {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    0 ≤ logarithmicRate x c := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [logarithmicRate_of_pos hxpos]
    exact mul_nonneg hx (zero_le_one.trans (one_le_log_exp_add_div hxpos hc))

/-- Monotonicity extends to the origin with the zero convention. -/
theorem logarithmicRate_mono_left {x y c : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hc : 0 ≤ c) :
    logarithmicRate x c ≤ logarithmicRate y c := by
  by_cases hx0 : x = 0
  · rw [hx0, logarithmicRate_zero]
    exact logarithmicRate_nonneg (hx.trans hxy) hc
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [logarithmicRate_of_pos hxpos, logarithmicRate_of_pos (hxpos.trans_le hxy)]
    exact mul_log_exp_add_div_mono_left hxpos hxy hc

/-- Monotonicity in the second argument also holds when the first is zero. -/
theorem logarithmicRate_mono_right {x c d : ℝ}
    (hx : 0 ≤ x) (hc : 0 ≤ c) (hcd : c ≤ d) :
    logarithmicRate x c ≤ logarithmicRate x d := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [logarithmicRate_of_pos hxpos, logarithmicRate_of_pos hxpos]
    exact mul_log_exp_add_div_mono_right hxpos hc hcd

/-- Dilation of both arguments scales the endpoint rate by the same factor. -/
theorem logarithmicRate_mul (r x c : ℝ) (hr : r ≠ 0) :
    logarithmicRate (r * x) (r * c) = r * logarithmicRate x c := by
  by_cases hx : x = 0
  · simp [hx]
  · have hrx : r * x ≠ 0 := mul_ne_zero hr hx
    have hratio : r * c / (r * x) = c / x := by field_simp
    simp only [logarithmicRate, if_neg hrx, if_neg hx, hratio]
    ring

/-- A single common constant absorbs both stochastic upper-bound constants.
`C` and `D` need not separately be assumed positive: the chosen constant is
always at least one. No positive lower bound on `δ` or `η` is required. -/
theorem logarithmicRate_absorb_constants {δ η a b C D : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (ha : 0 < a) (hb : 0 ≤ b)
    (hδa : δ ≤ C * a) (hηb : η ≤ D * b) :
    logarithmicRate δ η ≤
      max 1 (max C D) * a * Real.log (Real.exp 1 + b / a) := by
  let K := max 1 (max C D)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCK : C ≤ K := (le_max_left C D).trans (le_max_right _ _)
  have hDK : D ≤ K := (le_max_right C D).trans (le_max_right _ _)
  have hδK : δ ≤ K * a := hδa.trans (mul_le_mul_of_nonneg_right hCK ha.le)
  have hηK : η ≤ K * b := hηb.trans (mul_le_mul_of_nonneg_right hDK hb)
  calc
    logarithmicRate δ η ≤ logarithmicRate (K * a) η :=
      logarithmicRate_mono_left hδ hδK hη
    _ ≤ logarithmicRate (K * a) (K * b) :=
      logarithmicRate_mono_right (mul_nonneg hK.le ha.le) hη hηK
    _ = K * logarithmicRate a b := logarithmicRate_mul K a b (ne_of_gt hK)
    _ = _ := by rw [logarithmicRate_of_pos ha]; dsimp [K]; ring

/-- Failure of the optimized scalar bound is contained in the union of the two
original norm-bound failures. This is a pointwise statement, with no random
variable measurability assumption. -/
theorem logarithmicRate_exceedance_subset {Ω : Type*} (δ η : Ω → ℝ)
    (hδ : ∀ ω, 0 ≤ δ ω) (hη : ∀ ω, 0 ≤ η ω)
    {a b C D : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    {ω | max 1 (max C D) * a * Real.log (Real.exp 1 + b / a) < logarithmicRate (δ ω) (η ω)} ⊆
      {ω | C * a < δ ω} ∪ {ω | D * b < η ω} := by
  intro ω hω
  by_contra hnot
  have hδa : δ ω ≤ C * a := le_of_not_gt (fun h => hnot (Or.inl h))
  have hηb : η ω ≤ D * b := le_of_not_gt (fun h => hnot (Or.inr h))
  exact (not_lt_of_ge (logarithmicRate_absorb_constants (hδ ω) (hη ω) ha hb hδa hηb)) hω

/-- Outer-measure tail domination usable directly on good events. No
measurability of the norm functions or the displayed events is required. -/
theorem measure_logarithmicRate_exceedance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (δ η : Ω → ℝ)
    (hδ : ∀ ω, 0 ≤ δ ω) (hη : ∀ ω, 0 ≤ η ω)
    {a b C D : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    μ {ω | max 1 (max C D) * a * Real.log (Real.exp 1 + b / a) < logarithmicRate (δ ω) (η ω)} ≤
      μ {ω | C * a < δ ω} + μ {ω | D * b < η ω} :=
  (MeasureTheory.measure_mono (logarithmicRate_exceedance_subset δ η hδ hη ha hb)).trans
    (MeasureTheory.measure_union_le _ _)

end KernelSeq
