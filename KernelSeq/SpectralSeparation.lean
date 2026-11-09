import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Noncommuting geometric-series and Sylvester estimates

An operator-norm geometric series gives the multiplier on separated
spectral blocks. It constructs a
bounded linear map on actual bounded operators on an arbitrary Banach space.
No commutativity or finite-dimensional hypothesis is imposed.

Connecting the separated spectral restrictions of the manuscript to the
inverse/high and low operator norm bounds remains a distinct application.
-/

namespace KernelSeq

noncomputable section

variable {𝕜 H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] [CompleteSpace H]

/-- Simultaneous left and right multiplication on the bounded-operator space. -/
def sandwichMap (A B : H →L[𝕜] H) : (H →L[𝕜] H) →L[𝕜] H →L[𝕜] H :=
  ContinuousLinearMap.mulLeftRight 𝕜 (H →L[𝕜] H) A B

omit [CompleteSpace H] in
@[simp] theorem sandwichMap_apply (A B C : H →L[𝕜] H) :
    sandwichMap A B C = A * C * B := rfl

omit [CompleteSpace H] in
theorem norm_sandwichMap_le (A B : H →L[𝕜] H) :
    ‖sandwichMap A B‖ ≤ ‖A‖ * ‖B‖ :=
  ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le 𝕜 _ A B

omit [CompleteSpace H] in
/-- Iterating the sandwich map preserves the original noncommuting order. -/
theorem sandwichMap_pow_apply (A B C : H →L[𝕜] H) (n : ℕ) :
    (sandwichMap A B ^ n) C = A ^ n * C * B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, sandwichMap_apply,
        pow_succ' A n, pow_succ B n]
      simp only [mul_assoc]

/-- The Neumann resolvent of the sandwich map, itself a bounded linear map. -/
def sandwichResolvent (A B : H →L[𝕜] H) : (H →L[𝕜] H) →L[𝕜] H →L[𝕜] H :=
  ∑' n : ℕ, sandwichMap A B ^ n

/-- The actual operator-valued series is summable in operator norm. -/
theorem hasSum_sandwichResolvent (A B C : H →L[𝕜] H)
    (hq : ‖A‖ * ‖B‖ < 1) :
    HasSum (fun n : ℕ => A ^ n * C * B ^ n) (sandwichResolvent A B C) := by
  have hm : ‖sandwichMap A B‖ < 1 := (norm_sandwichMap_le A B).trans_lt hq
  have hs := (ContinuousLinearMap.apply 𝕜 (H →L[𝕜] H) C).hasSum
    (summable_geometric_of_norm_lt_one hm).hasSum
  change HasSum (fun n : ℕ => (sandwichMap A B ^ n) C)
    ((∑' n : ℕ, sandwichMap A B ^ n) C) at hs
  simpa only [sandwichMap_pow_apply, sandwichResolvent] using hs

/-- The resolvent solves the noncommuting sandwich equation. -/
theorem sandwichResolvent_equation (A B C : H →L[𝕜] H)
    (hq : ‖A‖ * ‖B‖ < 1) :
    sandwichResolvent A B C - A * sandwichResolvent A B C * B = C := by
  have hm : ‖sandwichMap A B‖ < 1 := (norm_sandwichMap_le A B).trans_lt hq
  have h := congrArg (fun L : (H →L[𝕜] H) →L[𝕜] H →L[𝕜] H => L C)
    (mul_neg_geom_series (sandwichMap A B) hm)
  simpa only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self, sandwichMap_apply, sandwichResolvent] using h

omit [CompleteSpace H] in
/-- A priori norm bound for any solution, not just the series solution. -/
theorem norm_le_of_sandwich_equation (A B C X : H →L[𝕜] H)
    (hq : ‖A‖ * ‖B‖ < 1) (heq : X - A * X * B = C) :
    ‖X‖ ≤ ‖C‖ / (1 - ‖A‖ * ‖B‖) := by
  have hid : X = C + A * X * B := by rw [← heq]; abel
  have hm : ‖A * X * B‖ ≤ ‖A‖ * ‖X‖ * ‖B‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg B))
  have hx : ‖X‖ ≤ ‖C‖ + ‖A * X * B‖ := by
    calc
      ‖X‖ = ‖C + A * X * B‖ := congrArg norm hid
      _ ≤ _ := norm_add_le _ _
  apply (le_div_iff₀ (sub_pos.mpr hq)).2
  nlinarith

/-- Operator norm of the series multiplier, dimension free. -/
theorem norm_sandwichResolvent_le (A B : H →L[𝕜] H)
    (hq : ‖A‖ * ‖B‖ < 1) :
    ‖sandwichResolvent A B‖ ≤ (1 - ‖A‖ * ‖B‖)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro C
  calc
    ‖sandwichResolvent A B C‖ ≤ ‖C‖ / (1 - ‖A‖ * ‖B‖) :=
      norm_le_of_sandwich_equation A B C _ hq (sandwichResolvent_equation A B C hq)
    _ = _ := by ring

omit [CompleteSpace H] in
/-- The sandwich equation has a unique bounded-operator solution. -/
theorem sandwich_equation_unique (A B C X Y : H →L[𝕜] H)
    (hq : ‖A‖ * ‖B‖ < 1)
    (hX : X - A * X * B = C) (hY : Y - A * Y * B = C) : X = Y := by
  have hdiff : (X - Y) - A * (X - Y) * B = 0 := by
    calc
      _ = (X - A * X * B) - (Y - A * Y * B) := by noncomm_ring
      _ = 0 := by rw [hX, hY, sub_self]
  have hn := norm_le_of_sandwich_equation A B 0 (X - Y) hq hdiff
  simp only [norm_zero, zero_div] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

/-- Solution of a separated Sylvester equation, using the actual operator inverse. -/
def separatedSylvesterSolution (U V C : H →L[𝕜] H) : H →L[𝕜] H :=
  sandwichResolvent (Ring.inverse U) V (Ring.inverse U * C)

theorem separatedSylvester_equation (U V C : H →L[𝕜] H) (hU : IsUnit U)
    (hq : ‖Ring.inverse U‖ * ‖V‖ < 1) :
    U * separatedSylvesterSolution U V C - separatedSylvesterSolution U V C * V = C := by
  have he := sandwichResolvent_equation (Ring.inverse U) V (Ring.inverse U * C) hq
  change separatedSylvesterSolution U V C -
    Ring.inverse U * separatedSylvesterSolution U V C * V = Ring.inverse U * C at he
  have hUA := Ring.mul_inverse_cancel U hU
  calc
    _ = U * (separatedSylvesterSolution U V C -
        Ring.inverse U * separatedSylvesterSolution U V C * V) := by
      rw [mul_sub]
      simp only [← mul_assoc, hUA, one_mul]
    _ = U * (Ring.inverse U * C) := congrArg (fun X => U * X) he
    _ = C := by rw [← mul_assoc, hUA, one_mul]

theorem norm_separatedSylvesterSolution_le (U V C : H →L[𝕜] H)
    (hq : ‖Ring.inverse U‖ * ‖V‖ < 1) :
    ‖separatedSylvesterSolution U V C‖ ≤
      ‖Ring.inverse U‖ * ‖C‖ / (1 - ‖Ring.inverse U‖ * ‖V‖) := by
  apply (norm_le_of_sandwich_equation (Ring.inverse U) V (Ring.inverse U * C) _ hq
    (sandwichResolvent_equation (Ring.inverse U) V (Ring.inverse U * C) hq)).trans
  exact div_le_div_of_nonneg_right (norm_mul_le _ _) (sub_pos.mpr hq).le

/-- The geometric-series separated-frequency estimate with high/low scales
`2τ` and `τ`. There is no assumption that any pair of operators commutes. -/
theorem separatedSylvester_norm_le_of_gap (U V C : H →L[𝕜] H) {τ : ℝ}
    (hτ : 0 < τ) (hUinv : ‖Ring.inverse U‖ ≤ 1 / (2 * τ)) (hV : ‖V‖ ≤ τ) :
    ‖separatedSylvesterSolution U V C‖ ≤ ‖C‖ / τ := by
  have hqhalf : ‖Ring.inverse U‖ * ‖V‖ ≤ 1 / 2 := by
    have hh := mul_le_mul hUinv hV (norm_nonneg V) (by positivity : 0 ≤ 1 / (2 * τ))
    have hid : 1 / (2 * τ) * τ = (1 / 2 : ℝ) := by field_simp
    simpa only [hid] using hh
  have hq : ‖Ring.inverse U‖ * ‖V‖ < 1 := by linarith
  calc
    ‖separatedSylvesterSolution U V C‖ ≤
        ‖Ring.inverse U‖ * ‖C‖ / (1 - ‖Ring.inverse U‖ * ‖V‖) :=
      norm_separatedSylvesterSolution_le U V C hq
    _ ≤ ‖Ring.inverse U‖ * ‖C‖ / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (by norm_num) (by linarith)
    _ = 2 * ‖Ring.inverse U‖ * ‖C‖ := by ring
    _ ≤ 2 * (1 / (2 * τ)) * ‖C‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUinv (by norm_num)) (norm_nonneg _)
    _ = ‖C‖ / τ := by field_simp

/-- The Sylvester series itself converges in operator norm. -/
theorem hasSum_separatedSylvesterSolution (U V C : H →L[𝕜] H)
    (hq : ‖Ring.inverse U‖ * ‖V‖ < 1) :
    HasSum (fun n : ℕ => Ring.inverse U ^ (n + 1) * C * V ^ n)
      (separatedSylvesterSolution U V C) := by
  have h := hasSum_sandwichResolvent (Ring.inverse U) V (Ring.inverse U * C) hq
  change HasSum (fun n : ℕ => Ring.inverse U ^ (n + 1) * C * V ^ n)
    (sandwichResolvent (Ring.inverse U) V (Ring.inverse U * C))
  convert h using 1
  funext n
  rw [pow_succ]
  simp only [mul_assoc]

omit [CompleteSpace H] in
/-- Uniqueness of the separated Sylvester solution in bounded operators. -/
theorem separatedSylvester_unique (U V C X Y : H →L[𝕜] H) (hU : IsUnit U)
    (hq : ‖Ring.inverse U‖ * ‖V‖ < 1)
    (hX : U * X - X * V = C) (hY : U * Y - Y * V = C) : X = Y := by
  have hAU := Ring.inverse_mul_cancel U hU
  have hnormalize : ∀ Z : H →L[𝕜] H, U * Z - Z * V = C →
      Z - Ring.inverse U * Z * V = Ring.inverse U * C := by
    intro Z hZ
    calc
      _ = Ring.inverse U * (U * Z - Z * V) := by
        rw [mul_sub]
        simp only [← mul_assoc, hAU, one_mul]
      _ = _ := congrArg (fun W => Ring.inverse U * W) hZ
  exact sandwich_equation_unique (Ring.inverse U) V (Ring.inverse U * C) X Y hq
    (hnormalize X hX) (hnormalize Y hY)

/-- The separated inverse is a genuine bounded linear multiplier on operators. -/
def separatedSylvesterMap (U V : H →L[𝕜] H) :
    (H →L[𝕜] H) →L[𝕜] H →L[𝕜] H :=
  (sandwichResolvent (Ring.inverse U) V).comp
    (ContinuousLinearMap.mul 𝕜 (H →L[𝕜] H) (Ring.inverse U))

omit [CompleteSpace H] in
@[simp] theorem separatedSylvesterMap_apply (U V C : H →L[𝕜] H) :
    separatedSylvesterMap U V C = separatedSylvesterSolution U V C := rfl

/-- Operator-norm multiplier bound for the separated high/low gap. -/
theorem norm_separatedSylvesterMap_le_of_gap (U V : H →L[𝕜] H) {τ : ℝ}
    (hτ : 0 < τ) (hUinv : ‖Ring.inverse U‖ ≤ 1 / (2 * τ)) (hV : ‖V‖ ≤ τ) :
    ‖separatedSylvesterMap U V‖ ≤ τ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hτ.le)
  intro C
  simpa only [separatedSylvesterMap_apply, div_eq_mul_inv, mul_comm] using
    separatedSylvester_norm_le_of_gap U V C hτ hUinv hV

/-- Existence and uniqueness of a bounded-operator solution for a separated
Sylvester equation. Invertibility of the high operator is an explicit premise. -/
theorem separatedSylvester_existsUnique (U V C : H →L[𝕜] H) (hU : IsUnit U)
    (hq : ‖Ring.inverse U‖ * ‖V‖ < 1) :
    ∃! X : H →L[𝕜] H, U * X - X * V = C := by
  refine ⟨separatedSylvesterSolution U V C, separatedSylvester_equation U V C hU hq, ?_⟩
  intro Y hY
  exact separatedSylvester_unique U V C Y (separatedSylvesterSolution U V C) hU hq hY
    (separatedSylvester_equation U V C hU hq)

/-- A separated gap gives a bounded linear Sylvester inverse on operator space,
with multiplier norm at most `1/τ`; this is stronger than a scalar kernel bound. -/
theorem separatedSylvester_multiplier_of_gap (U V : H →L[𝕜] H) (hU : IsUnit U)
    {τ : ℝ} (hτ : 0 < τ) (hUinv : ‖Ring.inverse U‖ ≤ 1 / (2 * τ)) (hV : ‖V‖ ≤ τ) :
    ∃ S : (H →L[𝕜] H) →L[𝕜] H →L[𝕜] H,
      ‖S‖ ≤ τ⁻¹ ∧ ∀ C, U * S C - S C * V = C := by
  refine ⟨separatedSylvesterMap U V, norm_separatedSylvesterMap_le_of_gap U V hτ hUinv hV, ?_⟩
  intro C
  have hqhalf : ‖Ring.inverse U‖ * ‖V‖ ≤ 1 / 2 := by
    have hh := mul_le_mul hUinv hV (norm_nonneg V) (by positivity : 0 ≤ 1 / (2 * τ))
    have hid : 1 / (2 * τ) * τ = (1 / 2 : ℝ) := by field_simp
    simpa only [hid] using hh
  exact separatedSylvester_equation U V C hU (by linarith)

section Rectangular

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Genuine rectangular left/right multiplication on operators `E →L F`.
The high and low spectral subspaces may be different Banach spaces. -/
def rectangularSandwichMap (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    (E →L[𝕜] F) →L[𝕜] E →L[𝕜] F :=
  (ContinuousLinearMap.compL 𝕜 E F F A).comp
    ((ContinuousLinearMap.compL 𝕜 E E F).flip B)

omit [CompleteSpace F] in
@[simp] theorem rectangularSandwichMap_apply (A : F →L[𝕜] F)
    (B : E →L[𝕜] E) (C : E →L[𝕜] F) :
    rectangularSandwichMap A B C = A.comp (C.comp B) := rfl

omit [CompleteSpace F] in
theorem norm_rectangularSandwichMap_le (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    ‖rectangularSandwichMap A B‖ ≤ ‖A‖ * ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro C
  calc
    ‖A.comp (C.comp B)‖ ≤ ‖A‖ * ‖C.comp B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * (‖C‖ * ‖B‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = (‖A‖ * ‖B‖) * ‖C‖ := by ring

omit [CompleteSpace F] in
theorem rectangularSandwichMap_pow_apply (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (C : E →L[𝕜] F) (n : ℕ) :
    (rectangularSandwichMap A B ^ n) C = (A ^ n).comp (C.comp (B ^ n)) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, rectangularSandwichMap_apply]
      ext x
      simp only [ContinuousLinearMap.comp_apply, pow_succ' A n, pow_succ B n,
        mul_apply_eq_comp]

/-- Rectangular Neumann resolvent, converging in the norm of the multiplier space. -/
def rectangularSandwichResolvent (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    (E →L[𝕜] F) →L[𝕜] E →L[𝕜] F :=
  ∑' n : ℕ, rectangularSandwichMap A B ^ n

/-- Operator-norm convergence of the actual rectangular series. -/
theorem hasSum_rectangularSandwichResolvent (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (C : E →L[𝕜] F) (hq : ‖A‖ * ‖B‖ < 1) :
    HasSum (fun n : ℕ => (A ^ n).comp (C.comp (B ^ n)))
      (rectangularSandwichResolvent A B C) := by
  have hm : ‖rectangularSandwichMap A B‖ < 1 :=
    (norm_rectangularSandwichMap_le A B).trans_lt hq
  have hsGeom := (summable_geometric_of_norm_lt_one
    (K := (E →L[𝕜] F) →L[𝕜] (E →L[𝕜] F)) hm).hasSum
  have hs := (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] F) C).hasSum hsGeom
  change HasSum (fun n : ℕ => (rectangularSandwichMap A B ^ n) C)
    ((∑' n : ℕ, rectangularSandwichMap A B ^ n) C) at hs
  apply hs.congr_fun
  intro n
  exact (rectangularSandwichMap_pow_apply A B C n).symm

/-- The rectangular resolvent solves its sandwich equation. -/
theorem rectangularSandwichResolvent_equation (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (C : E →L[𝕜] F) (hq : ‖A‖ * ‖B‖ < 1) :
    rectangularSandwichResolvent A B C -
      A.comp ((rectangularSandwichResolvent A B C).comp B) = C := by
  have hm : ‖rectangularSandwichMap A B‖ < 1 :=
    (norm_rectangularSandwichMap_le A B).trans_lt hq
  have h := congrArg (fun L : (E →L[𝕜] F) →L[𝕜] E →L[𝕜] F => L C)
    (mul_neg_geom_series (rectangularSandwichMap A B) hm)
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self,
    rectangularSandwichMap_apply, rectangularSandwichResolvent] using h

omit [CompleteSpace F] in
/-- Rectangular a priori estimate; no inverse or square root is presumed. -/
theorem norm_le_of_rectangularSandwich_equation (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (C X : E →L[𝕜] F) (hq : ‖A‖ * ‖B‖ < 1)
    (heq : X - A.comp (X.comp B) = C) :
    ‖X‖ ≤ ‖C‖ / (1 - ‖A‖ * ‖B‖) := by
  have hid : X = C + A.comp (X.comp B) := by rw [← heq]; abel
  have hm : ‖A.comp (X.comp B)‖ ≤ ‖A‖ * ‖X‖ * ‖B‖ := by
    calc
      _ ≤ ‖A‖ * ‖X.comp B‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ * (‖X‖ * ‖B‖) := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = _ := by ring
  have hx : ‖X‖ ≤ ‖C‖ + ‖A.comp (X.comp B)‖ := by
    calc
      ‖X‖ = ‖C + A.comp (X.comp B)‖ := congrArg norm hid
      _ ≤ _ := norm_add_le _ _
  apply (le_div_iff₀ (sub_pos.mpr hq)).2
  nlinarith

/-- Dimension-free norm bound on the rectangular series multiplier. -/
theorem norm_rectangularSandwichResolvent_le (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (hq : ‖A‖ * ‖B‖ < 1) :
    ‖rectangularSandwichResolvent A B‖ ≤ (1 - ‖A‖ * ‖B‖)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro C
  calc
    ‖rectangularSandwichResolvent A B C‖ ≤ ‖C‖ / (1 - ‖A‖ * ‖B‖) :=
      norm_le_of_rectangularSandwich_equation A B C _ hq
        (rectangularSandwichResolvent_equation A B C hq)
    _ = _ := by ring

omit [CompleteSpace F] in
/-- Uniqueness on the actual rectangular operator space. -/
theorem rectangularSandwich_equation_unique (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (C X Y : E →L[𝕜] F) (hq : ‖A‖ * ‖B‖ < 1)
    (hX : X - A.comp (X.comp B) = C) (hY : Y - A.comp (Y.comp B) = C) : X = Y := by
  have hid : A.comp ((X - Y).comp B) = A.comp (X.comp B) - A.comp (Y.comp B) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  have hdiff : (X - Y) - A.comp ((X - Y).comp B) = 0 := by
    rw [hid]
    calc
      _ = (X - A.comp (X.comp B)) - (Y - A.comp (Y.comp B)) := by abel
      _ = 0 := by rw [hX, hY, sub_self]
  have hn := norm_le_of_rectangularSandwich_equation A B 0 (X - Y) hq hdiff
  simp only [norm_zero, zero_div] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

/-- Rectangular Sylvester solution; the inverse acts only on the high space F. -/
def rectangularSylvesterSolution (U : F →L[𝕜] F) (V : E →L[𝕜] E)
    (C : E →L[𝕜] F) : E →L[𝕜] F :=
  rectangularSandwichResolvent (Ring.inverse U) V ((Ring.inverse U).comp C)

/-- Actual rectangular high/low Sylvester equation. Only U on F is inverted. -/
theorem rectangularSylvester_equation (U : F →L[𝕜] F) (V : E →L[𝕜] E)
    (C : E →L[𝕜] F) (hU : IsUnit U) (hq : ‖Ring.inverse U‖ * ‖V‖ < 1) :
    U.comp (rectangularSylvesterSolution U V C) -
      (rectangularSylvesterSolution U V C).comp V = C := by
  have he := rectangularSandwichResolvent_equation (Ring.inverse U) V
    ((Ring.inverse U).comp C) hq
  change rectangularSylvesterSolution U V C -
    (Ring.inverse U).comp ((rectangularSylvesterSolution U V C).comp V) =
      (Ring.inverse U).comp C at he
  have hUA : U.comp (Ring.inverse U) = 1 := Ring.mul_inverse_cancel U hU
  calc
    _ = U.comp (rectangularSylvesterSolution U V C -
        (Ring.inverse U).comp ((rectangularSylvesterSolution U V C).comp V)) := by
      rw [ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.comp_assoc, hUA]
      simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    _ = U.comp ((Ring.inverse U).comp C) := congrArg (fun X => U.comp X) he
    _ = C := by
      rw [← ContinuousLinearMap.comp_assoc, hUA]
      exact ContinuousLinearMap.id_comp C

/-- Rectangular Sylvester-series representation in operator norm. -/
theorem hasSum_rectangularSylvesterSolution (U : F →L[𝕜] F) (V : E →L[𝕜] E)
    (C : E →L[𝕜] F) (hq : ‖Ring.inverse U‖ * ‖V‖ < 1) :
    HasSum (fun n : ℕ => (Ring.inverse U ^ (n + 1)).comp (C.comp (V ^ n)))
      (rectangularSylvesterSolution U V C) := by
  have h := hasSum_rectangularSandwichResolvent (Ring.inverse U) V ((Ring.inverse U).comp C) hq
  change HasSum (fun n : ℕ => (Ring.inverse U ^ (n + 1)).comp (C.comp (V ^ n)))
    (rectangularSandwichResolvent (Ring.inverse U) V ((Ring.inverse U).comp C))
  convert h using 1
  funext n
  ext x
  simp only [pow_succ, mul_apply_eq_comp, ContinuousLinearMap.comp_apply]

/-- A priori rectangular solution norm. -/
theorem norm_rectangularSylvesterSolution_le (U : F →L[𝕜] F) (V : E →L[𝕜] E)
    (C : E →L[𝕜] F) (hq : ‖Ring.inverse U‖ * ‖V‖ < 1) :
    ‖rectangularSylvesterSolution U V C‖ ≤
      ‖Ring.inverse U‖ * ‖C‖ / (1 - ‖Ring.inverse U‖ * ‖V‖) := by
  apply (norm_le_of_rectangularSandwich_equation (Ring.inverse U) V ((Ring.inverse U).comp C)
    _ hq (rectangularSandwichResolvent_equation (Ring.inverse U) V ((Ring.inverse U).comp C) hq)).trans
  exact div_le_div_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (sub_pos.mpr hq).le

/-- The separated high/low gap bound on actual operators E→F. -/
theorem rectangularSylvester_norm_le_of_gap (U : F →L[𝕜] F) (V : E →L[𝕜] E)
    (C : E →L[𝕜] F) {τ : ℝ} (hτ : 0 < τ)
    (hUinv : ‖Ring.inverse U‖ ≤ 1 / (2 * τ)) (hV : ‖V‖ ≤ τ) :
    ‖rectangularSylvesterSolution U V C‖ ≤ ‖C‖ / τ := by
  have hqhalf : ‖Ring.inverse U‖ * ‖V‖ ≤ 1 / 2 := by
    have hh := mul_le_mul hUinv hV (norm_nonneg V) (by positivity : 0 ≤ 1 / (2 * τ))
    have hid : 1 / (2 * τ) * τ = (1 / 2 : ℝ) := by field_simp
    simpa only [hid] using hh
  have hq : ‖Ring.inverse U‖ * ‖V‖ < 1 := by linarith
  calc
    ‖rectangularSylvesterSolution U V C‖ ≤
        ‖Ring.inverse U‖ * ‖C‖ / (1 - ‖Ring.inverse U‖ * ‖V‖) :=
      norm_rectangularSylvesterSolution_le U V C hq
    _ ≤ ‖Ring.inverse U‖ * ‖C‖ / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (by norm_num) (by linarith)
    _ = 2 * ‖Ring.inverse U‖ * ‖C‖ := by ring
    _ ≤ 2 * (1 / (2 * τ)) * ‖C‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUinv (by norm_num)) (norm_nonneg _)
    _ = ‖C‖ / τ := by field_simp

/-- Bounded linear Sylvester inverse on the rectangular operator space. -/
def rectangularSylvesterMap (U : F →L[𝕜] F) (V : E →L[𝕜] E) :
    (E →L[𝕜] F) →L[𝕜] E →L[𝕜] F :=
  (rectangularSandwichResolvent (Ring.inverse U) V).comp
    (ContinuousLinearMap.compL 𝕜 E F F (Ring.inverse U))

omit [CompleteSpace F] in
@[simp] theorem rectangularSylvesterMap_apply (U : F →L[𝕜] F) (V : E →L[𝕜] E)
    (C : E →L[𝕜] F) : rectangularSylvesterMap U V C = rectangularSylvesterSolution U V C := rfl

/-- A genuine rectangular multiplier with gap norm at most 1/τ. -/
theorem rectangularSylvester_multiplier_of_gap (U : F →L[𝕜] F) (V : E →L[𝕜] E)
    (hU : IsUnit U) {τ : ℝ} (hτ : 0 < τ)
    (hUinv : ‖Ring.inverse U‖ ≤ 1 / (2 * τ)) (hV : ‖V‖ ≤ τ) :
    ∃ S : (E →L[𝕜] F) →L[𝕜] E →L[𝕜] F,
      ‖S‖ ≤ τ⁻¹ ∧ ∀ C, U.comp (S C) - (S C).comp V = C := by
  have hqhalf : ‖Ring.inverse U‖ * ‖V‖ ≤ 1 / 2 := by
    have hh := mul_le_mul hUinv hV (norm_nonneg V) (by positivity : 0 ≤ 1 / (2 * τ))
    have hid : 1 / (2 * τ) * τ = (1 / 2 : ℝ) := by field_simp
    simpa only [hid] using hh
  refine ⟨rectangularSylvesterMap U V, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hτ.le)
    intro C
    simpa only [rectangularSylvesterMap_apply, div_eq_mul_inv, mul_comm] using
      rectangularSylvester_norm_le_of_gap U V C hτ hUinv hV
  · intro C
    exact rectangularSylvester_equation U V C hU (by linarith)

omit [CompleteSpace F] in
/-- Uniqueness of the rectangular Sylvester equation on the actual low-to-high
operator space. Only the high-space operator U must be invertible. -/
theorem rectangularSylvester_unique (U : F →L[𝕜] F) (V : E →L[𝕜] E)
    (C X Y : E →L[𝕜] F) (hU : IsUnit U) (hq : ‖Ring.inverse U‖ * ‖V‖ < 1)
    (hX : U.comp X - X.comp V = C) (hY : U.comp Y - Y.comp V = C) : X = Y := by
  have hAU : (Ring.inverse U).comp U = 1 := Ring.inverse_mul_cancel U hU
  have hnormalize : ∀ Z : E →L[𝕜] F, U.comp Z - Z.comp V = C →
      Z - (Ring.inverse U).comp (Z.comp V) = (Ring.inverse U).comp C := by
    intro Z hZ
    calc
      _ = (Ring.inverse U).comp (U.comp Z - Z.comp V) := by
        rw [ContinuousLinearMap.comp_sub]
        have hleft : (Ring.inverse U).comp (U.comp Z) = Z := by
          rw [← ContinuousLinearMap.comp_assoc, hAU]
          exact ContinuousLinearMap.id_comp Z
        rw [hleft]
      _ = _ := congrArg (fun W => (Ring.inverse U).comp W) hZ
  exact rectangularSandwich_equation_unique (Ring.inverse U) V ((Ring.inverse U).comp C)
    X Y hq (hnormalize X hX) (hnormalize Y hY)

/-- Existence and uniqueness in the rectangular operator space E→F. -/
theorem rectangularSylvester_existsUnique (U : F →L[𝕜] F) (V : E →L[𝕜] E)
    (C : E →L[𝕜] F) (hU : IsUnit U) (hq : ‖Ring.inverse U‖ * ‖V‖ < 1) :
    ∃! X : E →L[𝕜] F, U.comp X - X.comp V = C := by
  refine ⟨rectangularSylvesterSolution U V C, rectangularSylvester_equation U V C hU hq, ?_⟩
  intro Y hY
  exact rectangularSylvester_unique U V C Y (rectangularSylvesterSolution U V C) hU hq hY
    (rectangularSylvester_equation U V C hU hq)

end Rectangular

end
end KernelSeq
