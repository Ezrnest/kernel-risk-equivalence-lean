import KernelSeq.SchattenInterpolation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Logic.Equiv.Bool

/-!
# Actual finite Walsh--Paley second moments

Predictable coefficients depend only on preceding Boolean coordinates.
Flipping a genuine cube coordinate proves mean zero and cross cancellation;
finite Parseval then proves the actual L2 isometry of Walsh martingale
transforms. The final specialization concerns the existing actual HS/S2 space.

This is the genuine L2 base for a martingale route, not the missing O(p)
UMD2(S_p) estimate for p>2. Randrianantoanina, Theorem 4.3 / Remark 4.6:
https://arxiv.org/pdf/math/0111264
The quantitative Hilbert-transform-to-UMD shortcut is insufficient for the
sharp linear order; see GMSS, equation (2) and Remark 3.10:
https://stephenmontgomerysmith.github.io/preprints/geiss_ms_saksman.pdf
-/

open MeasureTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

/-- The actual finite Boolean probability cube. -/
abbrev WalshCube (n : ℕ) := Fin n → Bool

local instance walshCubeMeasurableSpace (n : ℕ) : MeasurableSpace (WalshCube n) := ⊤

/-- The actual uniform probability measure, including n=0. -/
def walshUniformMeasure (n : ℕ) : Measure (WalshCube n) :=
  (PMF.uniformOfFintype (WalshCube n)).toMeasure

instance walshUniformMeasure_isProbability (n : ℕ) : IsProbabilityMeasure (walshUniformMeasure n) := by
  unfold walshUniformMeasure
  infer_instance

/-- Real Rademacher sign attached to a Boolean coordinate. -/
def walshSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem walshSign_abs (b : Bool) : |walshSign b| = 1 := by cases b <;> norm_num [walshSign]
@[simp] theorem walshSign_not (b : Bool) : walshSign (!b) = -walshSign b := by cases b <;> norm_num [walshSign]

/-- Actual cube-coordinate flipping is an equivalence, not an assumed law. -/
def walshFlip {n : ℕ} (j : Fin n) : Equiv.Perm (WalshCube n) where
  toFun ω := Function.update ω j (!ω j)
  invFun ω := Function.update ω j (!ω j)
  left_inv ω := by
    funext i
    by_cases h : i = j
    · subst i; simp
    · simp [Function.update_of_ne h]
  right_inv ω := by
    funext i
    by_cases h : i = j
    · subst i; simp
    · simp [Function.update_of_ne h]

@[simp] theorem walshFlip_same {n : ℕ} (j : Fin n) (ω : WalshCube n) : walshFlip j ω j = !ω j := by
  simp [walshFlip]

@[simp] theorem walshFlip_ne {n : ℕ} (j i : Fin n) (ω : WalshCube n) (h : i ≠ j) : walshFlip j ω i = ω i := by
  simp [walshFlip, Function.update_of_ne h]

/-- Genuine predictable dependence on the preceding cube coordinates. -/
def WalshPredictable {n : ℕ} {V : Type*} (a : Fin n → WalshCube n → V) : Prop :=
  ∀ i ω ω', (∀ j, j < i → ω j = ω' j) → a i ω = a i ω'

/-- Flipping a current or later coordinate preserves a predictable value. -/
theorem WalshPredictable.flip {n : ℕ} {V : Type*} {a : Fin n → WalshCube n → V}
    (ha : WalshPredictable a) (i j : Fin n) (hij : i ≤ j) (ω : WalshCube n) :
    a i (walshFlip j ω) = a i ω := by
  apply ha i (walshFlip j ω) ω
  intro k hk
  apply walshFlip_ne
  omega

variable {n : ℕ} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- An actual Walsh--Paley difference from its predictable coefficient. -/
def walshDifference {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : Fin n → WalshCube n → V) (i : Fin n) (ω : WalshCube n) : V :=
  walshSign (ω i) • a i ω

/-- The current difference changes sign under its coordinate flip. -/
theorem walshDifference_flip_same {a : Fin n → WalshCube n → K}
    (ha : WalshPredictable a) (i : Fin n) (ω : WalshCube n) :
    walshDifference a i (walshFlip i ω) = -walshDifference a i ω := by
  simp only [walshDifference, walshFlip_same, walshSign_not, ha.flip i i le_rfl ω, neg_smul]

/-- Earlier actual differences are unchanged under a later coordinate flip. -/
theorem walshDifference_flip_later {a : Fin n → WalshCube n → K}
    (ha : WalshPredictable a) (i j : Fin n) (hij : i < j) (ω : WalshCube n) :
    walshDifference a i (walshFlip j ω) = walshDifference a i ω := by
  rw [walshDifference, walshFlip_ne j i ω (ne_of_lt hij), ha.flip i j hij.le ω]
  rfl

/-- Each actual difference has its coefficient's exact norm. -/
theorem walshDifference_norm (a : Fin n → WalshCube n → K) (i : Fin n) (ω : WalshCube n) :
    ‖walshDifference a i ω‖ = ‖a i ω‖ := by
  rw [walshDifference, norm_smul, Real.norm_eq_abs, walshSign_abs, one_mul]

/-- Mean zero is derived from a finite measure-preserving flip. -/
theorem walshDifference_sum_eq_zero {a : Fin n → WalshCube n → K}
    (ha : WalshPredictable a) (i : Fin n) : (∑ ω : WalshCube n, walshDifference a i ω) = 0 := by
  have h : (∑ ω : WalshCube n, walshDifference a i ω) = -(∑ ω : WalshCube n, walshDifference a i ω) := by
    calc
      _ = ∑ ω : WalshCube n, walshDifference a i (walshFlip i ω) := (Equiv.sum_comp (walshFlip i) _).symm
      _ = _ := by simp only [walshDifference_flip_same ha, Finset.sum_neg_distrib]
  have hz : (2 : ℝ) • (∑ ω : WalshCube n, walshDifference a i ω) = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Cross cancellation of two different actual predictable differences. -/
theorem walshDifference_sum_inner_eq_zero_of_lt {a : Fin n → WalshCube n → K}
    (ha : WalshPredictable a) (i j : Fin n) (hij : i < j) :
    (∑ ω : WalshCube n, inner ℝ (walshDifference a i ω) (walshDifference a j ω)) = 0 := by
  have h : (∑ ω : WalshCube n, inner ℝ (walshDifference a i ω) (walshDifference a j ω)) =
      -(∑ ω : WalshCube n, inner ℝ (walshDifference a i ω) (walshDifference a j ω)) := by
    calc
      _ = ∑ ω : WalshCube n, inner ℝ (walshDifference a i (walshFlip j ω)) (walshDifference a j (walshFlip j ω)) :=
        (Equiv.sum_comp (walshFlip j) _).symm
      _ = _ := by simp only [walshDifference_flip_later ha i j hij, walshDifference_flip_same ha,
        inner_neg_right, Finset.sum_neg_distrib]
  linarith

/-- The off-diagonal expected inner products vanish, with no conditional
moment premise. -/
theorem walshDifference_sum_inner_eq_zero {a : Fin n → WalshCube n → K}
    (ha : WalshPredictable a) (i j : Fin n) (hij : i ≠ j) :
    (∑ ω : WalshCube n, inner ℝ (walshDifference a i ω) (walshDifference a j ω)) = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact walshDifference_sum_inner_eq_zero_of_lt ha i j h
  · simpa only [real_inner_comm] using walshDifference_sum_inner_eq_zero_of_lt ha j i h

/-- Actual finite-cube Parseval for arbitrary predictable Hilbert-valued
coefficients. The differences need not be independent. -/
theorem walshDifference_sum_norm_sq {a : Fin n → WalshCube n → K} (ha : WalshPredictable a) :
    (∑ ω : WalshCube n, ‖∑ i : Fin n, walshDifference a i ω‖ ^ 2) =
      ∑ i : Fin n, ∑ ω : WalshCube n, ‖a i ω‖ ^ 2 := by
  have hex (ω : WalshCube n) : ‖∑ i : Fin n, walshDifference a i ω‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, inner ℝ (walshDifference a i ω) (walshDifference a j ω) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  simp_rw [hex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · simp only [real_inner_self_eq_norm_sq, walshDifference_norm]
  · intro j _ hji
    exact walshDifference_sum_inner_eq_zero ha i j hji.symm
  · simp

variable [CompleteSpace K]

/-- Every actual uniform-cube expectation is the normalized finite sum. -/
theorem integral_walshUniform_eq (f : WalshCube n → K) :
    (∫ ω, f ω ∂walshUniformMeasure n) =
      (Fintype.card (WalshCube n) : ℝ)⁻¹ • ∑ ω : WalshCube n, f ω := by
  rw [walshUniformMeasure, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, Finset.smul_sum]

/-- The actual probability-space Walsh differences are centered. -/
theorem integral_walshDifference_eq_zero {a : Fin n → WalshCube n → K}
    (ha : WalshPredictable a) (i : Fin n) :
    (∫ ω, walshDifference a i ω ∂walshUniformMeasure n) = 0 := by
  rw [integral_walshUniform_eq, walshDifference_sum_eq_zero ha, smul_zero]

omit [CompleteSpace K] in
/-- The actual probability-space Walsh second-moment identity. -/
theorem integral_norm_sq_walshDifference_sum {a : Fin n → WalshCube n → K} (ha : WalshPredictable a) :
    (∫ ω, ‖∑ i : Fin n, walshDifference a i ω‖ ^ 2 ∂walshUniformMeasure n) =
      ∑ i : Fin n, ∫ ω, ‖a i ω‖ ^ 2 ∂walshUniformMeasure n := by
  simp only [integral_walshUniform_eq, smul_eq_mul]
  rw [walshDifference_sum_norm_sq ha, Finset.mul_sum]

omit [CompleteSpace K] in
/-- A predictable scalar multiple of a predictable coefficient is predictable. -/
theorem WalshPredictable.smul {a : Fin n → WalshCube n → K} {σ : Fin n → WalshCube n → ℝ}
    (hσ : WalshPredictable σ) (ha : WalshPredictable a) :
    WalshPredictable (fun i ω => σ i ω • a i ω) := by
  intro i ω ω' hω
  change σ i ω • a i ω = σ i ω' • a i ω'
  rw [hσ i ω ω' hω, ha i ω ω' hω]

omit [CompleteSpace K] in
/-- A genuine predictable sign transform is an exact L2 isometry on the
actual probability cube. No martingale difference moment is assumed. -/
theorem integral_norm_sq_walsh_transform {a : Fin n → WalshCube n → K}
    {σ : Fin n → WalshCube n → ℝ} (ha : WalshPredictable a) (hσ : WalshPredictable σ)
    (hσunit : ∀ i ω, |σ i ω| = 1) :
    (∫ ω, ‖∑ i : Fin n, σ i ω • walshDifference a i ω‖ ^ 2 ∂walshUniformMeasure n) =
      ∫ ω, ‖∑ i : Fin n, walshDifference a i ω‖ ^ 2 ∂walshUniformMeasure n := by
  have hdiff (ω : WalshCube n) :
      (∑ i : Fin n, σ i ω • walshDifference a i ω) =
        ∑ i : Fin n, walshDifference (fun i ω => σ i ω • a i ω) i ω := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [walshDifference, smul_smul]
    rw [mul_comm]
  simp_rw [hdiff]
  rw [integral_norm_sq_walshDifference_sum (hσ.smul ha), integral_norm_sq_walshDifference_sum ha]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    change ‖σ i ω • a i ω‖ ^ 2 = ‖a i ω‖ ^ 2
    rw [norm_smul, Real.norm_eq_abs, hσunit i ω, one_mul]

omit [CompleteSpace K] in
/-- Deterministic sign sequences are a special case of the actual isometry. -/
theorem integral_norm_sq_walsh_transform_const {a : Fin n → WalshCube n → K}
    (ha : WalshPredictable a) (σ : Fin n → ℝ) (hσunit : ∀ i, |σ i| = 1) :
    (∫ ω, ‖∑ i : Fin n, σ i • walshDifference a i ω‖ ^ 2 ∂walshUniformMeasure n) =
      ∫ ω, ‖∑ i : Fin n, walshDifference a i ω‖ ^ 2 ∂walshUniformMeasure n :=
  integral_norm_sq_walsh_transform ha (fun _ _ _ _ => rfl) (fun i _ => hσunit i)

/-- Actual S2-valued Walsh transforms satisfy the actual normalized L2
isometry. This is the HS endpoint, not the missing UMD2(S_p) estimate at p>2. -/
theorem integral_schatten_two_sq_walsh_transform
    {I H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : HilbertBasis I ℝ H) {a : Fin n → WalshCube n → HilbertSchmidtColumns I E}
    (ha : WalshPredictable a) (σ : Fin n → ℝ) (hσunit : ∀ i, |σ i| = 1) :
    (∫ ω, hsSchattenNorm b (∑ i : Fin n, σ i • walshDifference a i ω) 2 ^ 2 ∂walshUniformMeasure n) =
      ∫ ω, hsSchattenNorm b (∑ i : Fin n, walshDifference a i ω) 2 ^ 2 ∂walshUniformMeasure n := by
  simp only [hsSchattenNorm_two]
  exact integral_norm_sq_walsh_transform_const ha σ hσunit

/-- The genuine operator quadratic variation of a Walsh difference is the
coefficient Gram operator, since the actual scalar sign squares to one. -/
theorem walshDifference_operator_gram
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (a : Fin n → WalshCube n → H →L[ℝ] H) (i : Fin n) (ω : WalshCube n) :
    (walshDifference a i ω).adjoint * walshDifference a i ω = (a i ω).adjoint * a i ω := by
  cases h : ω i <;> simp [walshDifference, walshSign, h]

/-- Exact finite noncommuting prefix Gram decomposition. Applied pointwise
to actual Walsh differences, the diagonal is the actual quadratic variation
above and the remaining terms involve genuinely preceding prefixes. This
identity alone does not bound their S_p norms. -/
theorem operator_prefix_sum_gram
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H →L[ℝ] H) (N : ℕ) :
    (∑ i ∈ Finset.range N, u i).adjoint * (∑ i ∈ Finset.range N, u i) =
      (∑ i ∈ Finset.range N, (u i).adjoint * u i) +
        ∑ i ∈ Finset.range N,
          ((∑ j ∈ Finset.range i, u j).adjoint * u i + (u i).adjoint * (∑ j ∈ Finset.range i, u j)) := by
  have hadd (A B : H →L[ℝ] H) :
      (A + B).adjoint * (A + B) = A.adjoint * A + B.adjoint * B + (A.adjoint * B + B.adjoint * A) := by
    rw [map_add]
    noncomm_ring
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    rw [hadd, ih]
    abel

end
end KernelSeq
