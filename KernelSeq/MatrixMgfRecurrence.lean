import KernelSeq.FiniteOperatorTrace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Trace envelopes and the intrinsic matrix-moment recurrence

The geometric recurrence is valid even when its coefficient is zero. The
weighted trace estimate follows from genuine Loewner comparison and the
actual operator norm, not an assumed trace or variance certificate.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

theorem mgf_finset_recurrence_power {ι : Type*} [DecidableEq ι] {a d : ℝ} (ha : 0 ≤ a)
    (u : Finset ι → ℝ) (hzero : u ∅ ≤ 0)
    (hstep : ∀ s i, i ∉ s → u (insert i s) ≤ (1 + a) * u s + a * d) (s : Finset ι) :
    u s ≤ d * ((1 + a) ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | @insert i s hi ih =>
    calc
      _ ≤ (1 + a) * u s + a * d := hstep s i hi
      _ ≤ (1 + a) * (d * ((1 + a) ^ s.card - 1)) + a * d :=
        add_le_add (mul_le_mul_of_nonneg_left ih (show 0 ≤ 1 + a by linarith)) le_rfl
      _ = _ := by rw [Finset.card_insert_of_notMem hi, pow_succ]; ring

theorem one_add_pow_le_exp_nat_mul {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (1 + a) ^ m ≤ Real.exp ((m : ℝ) * a) := by
  have hbase : 1 + a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have heq : Real.exp a ^ m = Real.exp ((m : ℝ) * a) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + a) hbase m
  exact hp.trans_eq heq

/-- The exact scalar envelope used for the trace moment of a finite sum.
No positivity or lower bound on `a` beyond zero is needed. -/
theorem mgf_finset_recurrence_exp {ι : Type*} [DecidableEq ι] {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (u : Finset ι → ℝ) (hzero : u ∅ ≤ 0)
    (hstep : ∀ s i, i ∉ s → u (insert i s) ≤ (1 + a) * u s + a * d) (s : Finset ι) :
    u s ≤ d * (Real.exp ((s.card : ℝ) * a) - 1) :=
  (mgf_finset_recurrence_power ha u hzero hstep s).trans
    (mul_le_mul_of_nonneg_left (sub_le_sub_right (one_add_pow_le_exp_nat_mul ha s.card) 1) hd)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem selfAdjoint_le_norm_one (W : H →L[ℝ] H) (hW : IsSelfAdjoint W) :
    W ≤ ‖W‖ • (1 : H →L[ℝ] H) := by
  apply (ContinuousLinearMap.le_def _ _).mpr
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨?_, ?_⟩
  · exact ((ContinuousLinearMap.isPositive_one.smul_of_nonneg (norm_nonneg W)).isSymmetric).sub hW.isSymmetric
  · intro x
    have hi := real_inner_le_norm (W x) x
    have hm := mul_le_mul_of_nonneg_right (W.le_opNorm x) (norm_nonneg x)
    simp only [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
      inner_sub_left, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
    nlinarith

theorem finiteBasisTrace_weighted_le_norm {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A W : H →L[ℝ] H) (hA : A.IsPositive) (hW : IsSelfAdjoint W) :
    basisTrace b (A * W) ≤ ‖W‖ * basisTrace b A := by
  have h := finiteBasisTrace_mul_mono b A W (‖W‖ • 1) hA (selfAdjoint_le_norm_one W hW)
  have heq : A * (‖W‖ • 1) = ‖W‖ • A := by simp only [mul_smul_comm, mul_one]
  rw [heq, basisTrace_smul b ‖W‖ A (hasSum_fintype _).summable] at h
  exact h

end
end KernelSeq
