import KernelSeq.CuculescuCutoff
import KernelSeq.WalshPaleyMoments

/-!
# Actual finite Walsh Cuculescu recursion

Prefix conditional averages are finite uniform averages of the actual terminal
field. Adapted weighted trace identities follow from a genuine involution of
two Boolean cubes. The recursive spectral cutoffs therefore require no
conditional-expectation or terminal-trace certificate. This is the finite
prefix model of Cuculescu's construction (Randrianantoanina, Proposition 2.4,
https://arxiv.org/pdf/math/0111264); no weak-(1,1) martingale-transform or UMD
estimate is asserted here.
-/

open MeasureTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

local instance cuculescuWalshMeasurableSpace (n : ℕ) : MeasurableSpace (WalshCube n) := ⊤

/-- Genuine dependence on the first k Boolean coordinates. -/
def WalshAdapted {V : Type*} (k : ℕ) (f : WalshCube n → V) : Prop :=
  ∀ ω η, (∀ j : Fin n, (j : ℕ) < k → ω j = η j) → f ω = f η

/-- Retain the first k coordinates of ω and take the remaining ones from η. -/
def walshMerge (k : ℕ) (ω η : WalshCube n) : WalshCube n :=
  fun j => if (j : ℕ) < k then ω j else η j

theorem WalshAdapted.mono {V : Type*} {k l : ℕ} {f : WalshCube n → V}
    (hf : WalshAdapted k f) (hkl : k ≤ l) : WalshAdapted l f := by
  intro ω η h
  exact hf ω η (fun j hj => h j (lt_of_lt_of_le hj hkl))

theorem WalshAdapted.merge {V : Type*} {k : ℕ} {f : WalshCube n → V}
    (hf : WalshAdapted k f) (ω η : WalshCube n) : f (walshMerge k ω η) = f ω := by
  apply hf
  intro j hj
  simp only [walshMerge, if_pos hj]

/-- Exchanging the two tails is an actual involution on the pair of cubes. -/
def walshTailSwap (k : ℕ) : Equiv.Perm (WalshCube n × WalshCube n) where
  toFun p := (walshMerge k p.1 p.2, walshMerge k p.2 p.1)
  invFun p := (walshMerge k p.1 p.2, walshMerge k p.2 p.1)
  left_inv p := by
    apply Prod.ext <;> funext j <;> simp only [walshMerge] <;> split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext j <;> simp only [walshMerge] <;> split_ifs <;> rfl

/-- The actual conditional prefix average, written as a uniform full-cube
average so the definition includes k=0, k=n and n=0 without division cases. -/
def walshPrefixAverage {V : Type*} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (f : WalshCube n → V) (ω : WalshCube n) : V :=
  (Fintype.card (WalshCube n) : ℝ)⁻¹ • ∑ η : WalshCube n, f (walshMerge k ω η)

theorem walshPrefixAverage_adapted {V : Type*} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (f : WalshCube n → V) : WalshAdapted k (walshPrefixAverage k f) := by
  intro ω η h
  unfold walshPrefixAverage
  congr 1
  apply Finset.sum_congr rfl
  intro ζ _
  congr 1
  funext j
  by_cases hj : (j : ℕ) < k
  · simp only [walshMerge, if_pos hj, h j hj]
  · simp only [walshMerge, if_neg hj]

theorem walshPrefixAverage_of_adapted {V : Type*} [AddCommGroup V] [Module ℝ V]
    {k : ℕ} {f : WalshCube n → V} (hf : WalshAdapted k f) (ω : WalshCube n) :
    walshPrefixAverage k f ω = f ω := by
  have hc : (Fintype.card (WalshCube n) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [walshPrefixAverage, hf.merge, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem walshPrefixAverage_terminal {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : WalshCube n → V) (ω : WalshCube n) : walshPrefixAverage n f ω = f ω := by
  apply walshPrefixAverage_of_adapted
  intro η ζ h
  congr 1
  funext j
  exact h j j.isLt

/-- True finite expectation preservation, derived from tail exchange. -/
theorem sum_walshPrefixAverage {V : Type*} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (f : WalshCube n → V) :
    (∑ ω : WalshCube n, walshPrefixAverage k f ω) = ∑ ω : WalshCube n, f ω := by
  have hc : (Fintype.card (WalshCube n) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs := Equiv.sum_comp (walshTailSwap (n := n) k) (fun p : WalshCube n × WalshCube n => f p.1)
  change (∑ p : WalshCube n × WalshCube n, f (walshMerge k p.1 p.2)) =
    ∑ p : WalshCube n × WalshCube n, f p.1 at hs
  have hd : (∑ ω : WalshCube n, ∑ η : WalshCube n, f (walshMerge k ω η)) =
      (Fintype.card (WalshCube n)) • ∑ ω : WalshCube n, f ω := by
    simpa only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Finset.sum_nsmul] using hs
  simp only [walshPrefixAverage, ← Finset.smul_sum, hd,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- Positivity is inherited from the actual terminal field's finite average. -/
theorem walshPrefixAverage_positive (F : WalshCube n → H →L[ℝ] H)
    (hF : ∀ ω, (F ω).IsPositive) (k : ℕ) (ω : WalshCube n) :
    (walshPrefixAverage k F ω).IsPositive := by
  apply ContinuousLinearMap.IsPositive.smul_of_nonneg
  · exact ContinuousLinearMap.isPositive_sum _ (fun η _ => hF (walshMerge k ω η))
  · positivity

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem walshPrefixAverage_trace_mul {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F Q : WalshCube n → H →L[ℝ] H) {k : ℕ}
    (hQ : WalshAdapted k Q) (ω : WalshCube n) :
    basisTrace b (walshPrefixAverage k F ω * Q ω) =
      walshPrefixAverage k (fun η => basisTrace b (F η * Q η)) ω := by
  simp only [walshPrefixAverage, smul_mul_assoc, Finset.sum_mul,
    ← finiteBasisTraceCLM_apply, map_smul, map_sum, hQ.merge, smul_eq_mul]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- The actual adapted weighted trace expectation identity. It is derived
from finite averaging and is not a martingale premise. -/
theorem sum_trace_walshPrefixAverage_mul {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F Q : WalshCube n → H →L[ℝ] H) {k : ℕ}
    (hQ : WalshAdapted k Q) :
    (∑ ω : WalshCube n, basisTrace b (walshPrefixAverage k F ω * Q ω)) =
      ∑ ω : WalshCube n, basisTrace b (F ω * Q ω) := by
  simp_rw [walshPrefixAverage_trace_mul b F Q hQ]
  exact sum_walshPrefixAverage k _

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- The same exact identity for the actual uniform probability measure. -/
theorem integral_trace_walshPrefixAverage_mul {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F Q : WalshCube n → H →L[ℝ] H) {k : ℕ}
    (hQ : WalshAdapted k Q) :
    (∫ ω, basisTrace b (walshPrefixAverage k F ω * Q ω) ∂walshUniformMeasure n) =
      ∫ ω, basisTrace b (F ω * Q ω) ∂walshUniformMeasure n := by
  simp only [integral_walshUniform_eq, smul_eq_mul]
  rw [sum_trace_walshPrefixAverage_mul b F Q hQ]

/-- The actual recursive spectral projection, bundled only with the two
projection properties proved by its construction. -/
def cuculescuWalshState (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ℕ → WalshCube n → {q : H →L[ℝ] H // IsSelfAdjoint q ∧ IsIdempotentElem q}
  | 0, _ => ⟨1, IsSelfAdjoint.one (H →L[ℝ] H), IsIdempotentElem.one⟩
  | k + 1, ω =>
    let e := cuculescuWalshState F hF lam hlam k ω
    let X := walshPrefixAverage (k + 1) F ω
    let hX := walshPrefixAverage_positive F hF (k + 1) ω
    ⟨cuculescuCutoff e.val X e.property.1 hX lam,
      cuculescuCutoff_selfAdjoint e.val X e.property.1 hX lam,
      cuculescuCutoff_idempotent e.val X e.property.1 e.property.2 hX lam hlam⟩

/-- The actual nth cutoff, starting from q₀=1. -/
def cuculescuWalshProjection (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) : H →L[ℝ] H :=
  (cuculescuWalshState F hF lam hlam k ω).val

@[simp] theorem cuculescuWalshProjection_zero
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (ω : WalshCube n) :
    cuculescuWalshProjection F hF lam hlam 0 ω = 1 := rfl

theorem cuculescuWalshProjection_selfAdjoint
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    IsSelfAdjoint (cuculescuWalshProjection F hF lam hlam k ω) :=
  (cuculescuWalshState F hF lam hlam k ω).property.1

theorem cuculescuWalshProjection_idempotent
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    IsIdempotentElem (cuculescuWalshProjection F hF lam hlam k ω) :=
  (cuculescuWalshState F hF lam hlam k ω).property.2

theorem cuculescuWalshProjection_positive
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    (cuculescuWalshProjection F hF lam hlam k ω).IsPositive :=
  (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
    (cuculescuWalshProjection_idempotent F hF lam hlam k ω)).mpr
    (cuculescuWalshProjection_selfAdjoint F hF lam hlam k ω)

@[simp] theorem cuculescuWalshProjection_succ
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    cuculescuWalshProjection F hF lam hlam (k + 1) ω =
      cuculescuCutoff (cuculescuWalshProjection F hF lam hlam k ω)
        (walshPrefixAverage (k + 1) F ω)
        (cuculescuWalshProjection_selfAdjoint F hF lam hlam k ω)
        (walshPrefixAverage_positive F hF (k + 1) ω) lam := rfl

theorem cuculescuWalshProjection_adapted
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) :
    WalshAdapted k (cuculescuWalshProjection F hF lam hlam k) := by
  induction k with
  | zero => intro ω η h; rfl
  | succ k ih =>
    intro ω η h
    have he := ih.mono (Nat.le_succ k) ω η h
    have hX := walshPrefixAverage_adapted (k + 1) F ω η h
    simp only [cuculescuWalshProjection_succ]
    congr 1

theorem cuculescuWalshProjection_succ_le
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    cuculescuWalshProjection F hF lam hlam (k + 1) ω ≤
      cuculescuWalshProjection F hF lam hlam k ω := by
  rw [cuculescuWalshProjection_succ]
  exact cuculescuCutoff_le _ _ _ _ _

theorem cuculescuWalshProjection_antitone
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (ω : WalshCube n) :
    Antitone (fun k => cuculescuWalshProjection F hF lam hlam k ω) :=
  antitone_nat_of_succ_le (fun k => cuculescuWalshProjection_succ_le F hF lam hlam k ω)

/-- Every noninitial cutoff bounds the actual current prefix-average field. -/
theorem cuculescuWalshProjection_compression_upper
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    let q := cuculescuWalshProjection F hF lam hlam (k + 1) ω
    q * walshPrefixAverage (k + 1) F ω * q ≤ lam • q := by
  dsimp only
  rw [cuculescuWalshProjection_succ]
  exact cuculescuCutoff_compression_upper _ _ _
    (cuculescuWalshProjection_idempotent F hF lam hlam k ω) _ _ hlam

/-- At the terminal nonempty stage the actual field itself is bounded on
the retained projection. No independent terminal averaging law is assumed. -/
theorem cuculescuWalshProjection_terminal_compression_upper
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (hn : 0 < n) (ω : WalshCube n) :
    let q := cuculescuWalshProjection F hF lam hlam n ω
    q * F ω * q ≤ lam • q := by
  cases n with
  | zero => omega
  | succ k =>
    simpa only [walshPrefixAverage_terminal] using
      cuculescuWalshProjection_compression_upper F hF lam hlam k ω

/-- The actual discarded projection at each step is adapted to that step. -/
theorem cuculescuWalshDrop_adapted
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) :
    WalshAdapted (k + 1) (fun ω =>
      cuculescuWalshProjection F hF lam hlam k ω -
        cuculescuWalshProjection F hF lam hlam (k + 1) ω) := by
  intro ω η h
  change cuculescuWalshProjection F hF lam hlam k ω -
      cuculescuWalshProjection F hF lam hlam (k + 1) ω =
    cuculescuWalshProjection F hF lam hlam k η -
      cuculescuWalshProjection F hF lam hlam (k + 1) η
  rw [(cuculescuWalshProjection_adapted F hF lam hlam k).mono (Nat.le_succ k) ω η h,
    cuculescuWalshProjection_adapted F hF lam hlam (k + 1) ω η h]

theorem cuculescuWalshProjection_telescope
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) (ω : WalshCube n) :
    (∑ k ∈ Finset.range N,
      (cuculescuWalshProjection F hF lam hlam k ω -
        cuculescuWalshProjection F hF lam hlam (k + 1) ω)) =
      1 - cuculescuWalshProjection F hF lam hlam N ω := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; abel

/-- The actual terminal-trace payment for one discarded step. The weighted
terminal identity is proved above from the uniform finite average. -/
theorem sum_trace_cuculescuWalshDrop_bound {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H)
    (hF : ∀ ω, (F ω).IsPositive) (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) :
    lam * (∑ ω : WalshCube n, basisTrace b
      (cuculescuWalshProjection F hF lam hlam k ω -
        cuculescuWalshProjection F hF lam hlam (k + 1) ω)) ≤
      ∑ ω : WalshCube n, basisTrace b (F ω *
        (cuculescuWalshProjection F hF lam hlam k ω -
          cuculescuWalshProjection F hF lam hlam (k + 1) ω)) := by
  calc
    _ = ∑ ω : WalshCube n, lam * basisTrace b
        (cuculescuWalshProjection F hF lam hlam k ω -
          cuculescuWalshProjection F hF lam hlam (k + 1) ω) := Finset.mul_sum _ _ _
    _ ≤ ∑ ω : WalshCube n, basisTrace b (walshPrefixAverage (k + 1) F ω *
        (cuculescuWalshProjection F hF lam hlam k ω -
          cuculescuWalshProjection F hF lam hlam (k + 1) ω)) := by
      apply Finset.sum_le_sum
      intro ω _
      rw [cuculescuWalshProjection_succ]
      exact cuculescuDrop_trace_bound b _ _ _
        (cuculescuWalshProjection_idempotent F hF lam hlam k ω) _ _ hlam
    _ = _ := sum_trace_walshPrefixAverage_mul b F _ (cuculescuWalshDrop_adapted F hF lam hlam k)

/-- The genuine finite terminal trace tail, before normalization into a
probability expectation. The terminal operators need not commute with the
cutoff projections. -/
theorem sum_trace_cuculescuWalsh_tail_bound {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H)
    (hF : ∀ ω, (F ω).IsPositive) (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) :
    lam * (∑ ω : WalshCube n, basisTrace b (1 - cuculescuWalshProjection F hF lam hlam N ω)) ≤
      ∑ ω : WalshCube n, basisTrace b (F ω) := by
  let q := cuculescuWalshProjection F hF lam hlam
  have htel (ω : WalshCube n) : (∑ k ∈ Finset.range N, (q k ω - q (k + 1) ω)) = 1 - q N ω :=
    cuculescuWalshProjection_telescope F hF lam hlam N ω
  have htr (ω : WalshCube n) :
      (∑ k ∈ Finset.range N, basisTrace b (q k ω - q (k + 1) ω)) = basisTrace b (1 - q N ω) := by
    simp only [← finiteBasisTraceCLM_apply, ← map_sum, htel]
  have henergy (ω : WalshCube n) :
      (∑ k ∈ Finset.range N, basisTrace b (F ω * (q k ω - q (k + 1) ω))) =
        basisTrace b (F ω * (1 - q N ω)) := by
    simp only [← finiteBasisTraceCLM_apply, ← map_sum, ← Finset.mul_sum, htel]
  calc
    _ = ∑ k ∈ Finset.range N, lam * ∑ ω : WalshCube n, basisTrace b (q k ω - q (k + 1) ω) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [htr, q]
    _ ≤ ∑ k ∈ Finset.range N, ∑ ω : WalshCube n, basisTrace b (F ω * (q k ω - q (k + 1) ω)) :=
      Finset.sum_le_sum (fun k _ => sum_trace_cuculescuWalshDrop_bound b F hF lam hlam k)
    _ = ∑ ω : WalshCube n, basisTrace b (F ω * (1 - q N ω)) := by
      rw [Finset.sum_comm]
      simp only [henergy]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ω _
      have hnonneg := finiteBasisTrace_mul_nonneg b (F ω) (q N ω) (hF ω)
        (cuculescuWalshProjection_positive F hF lam hlam N ω)
      have hsplit : basisTrace b (F ω * (1 - q N ω)) =
          basisTrace b (F ω) - basisTrace b (F ω * q N ω) := by
        simp only [mul_sub, mul_one, ← finiteBasisTraceCLM_apply, map_sub]
      rw [hsplit]
      linarith

/-- Cuculescu's terminal trace tail on the actual finite uniform Walsh
probability space. The estimate includes the empty cube and zero threshold. -/
theorem integral_trace_cuculescuWalsh_tail_bound {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H)
    (hF : ∀ ω, (F ω).IsPositive) (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) :
    lam * (∫ ω, basisTrace b (1 - cuculescuWalshProjection F hF lam hlam N ω)
      ∂walshUniformMeasure n) ≤
      ∫ ω, basisTrace b (F ω) ∂walshUniformMeasure n := by
  simp only [integral_walshUniform_eq, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (sum_trace_cuculescuWalsh_tail_bound b F hF lam hlam N)
    (show 0 ≤ (Fintype.card (WalshCube n) : ℝ)⁻¹ by positivity)
  nlinarith only [h]

end
end KernelSeq
