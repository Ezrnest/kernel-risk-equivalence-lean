import KernelSeq.FiniteSingularApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Actual finite singular-value distributions

Optimal rank approximations prove the additive singular-value Weyl bound.
The actual sorted singular values determine a counting function; its exact
relation to the next singular value yields a genuine distribution bound for
sums. These are finite spectral foundations for weak-type interpolation,
not an assumed interpolation or martingale-transform theorem.
-/

open scoped BigOperators
open MeasureTheory
open scoped ENNReal

namespace KernelSeq
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H]

/-- Actual additive Weyl bound from the two optimal rank truncations. -/
theorem finiteSingularValue_add_le (A B : H →L[ℝ] H) (k j : ℕ) :
    (A + B).toLinearMap.singularValues (k + j) ≤
      A.toLinearMap.singularValues k + B.toLinearMap.singularValues j := by
  let Ak := finiteSingularTruncation A k
  let Bj := finiteSingularTruncation B j
  let F := Ak + Bj
  have hF : Module.finrank ℝ F.range ≤ k + j :=
    (finiteOperator_rank_add_le Ak Bj).trans
      (add_le_add (finiteSingularTruncation_rank_le A k) (finiteSingularTruncation_rank_le B j))
  have heq : A + B - F = (A - Ak) + (B - Bj) := by dsimp only [F]; abel
  calc
    _ ≤ ‖A + B - F‖ := finiteSingularValue_le_rank_approximation (A + B) F (k + j) hF
    _ = ‖(A - Ak) + (B - Bj)‖ := congrArg norm heq
    _ ≤ ‖A - Ak‖ + ‖B - Bj‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (finiteSingularTruncation_error_le A k) (finiteSingularTruncation_error_le B j)

/-- The actual finite singular-value exceedance count at a real threshold. -/
def finiteSingularCount (A : H →L[ℝ] H) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin (Module.finrank ℝ H) => t < A.toLinearMap.singularValues i).card

omit [CompleteSpace H] in
theorem finiteSingularCount_antitone (A : H →L[ℝ] H) : Antitone (finiteSingularCount A) := by
  classical
  intro s t hst
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hst.trans_lt hi

omit [CompleteSpace H] in
/-- The sorted counting function and the next singular value are exact
inverses at every nonnegative threshold, including beyond the dimension. -/
theorem finiteSingularCount_le_iff (A : H →L[ℝ] H) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    finiteSingularCount A t ≤ k ↔ A.toLinearMap.singularValues k ≤ t := by
  classical
  let s := Finset.univ.filter fun i : Fin (Module.finrank ℝ H) => t < A.toLinearMap.singularValues i
  constructor
  · intro hcount
    by_contra hn
    have htk : t < A.toLinearMap.singularValues k := lt_of_not_ge hn
    have hk : k < Module.finrank ℝ H := by
      by_contra hk
      rw [A.toLinearMap.singularValues_of_finrank_le (by omega)] at htk
      linarith
    let g : Fin (k + 1) → s := fun i => ⟨⟨i.val, by omega⟩, by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact htk.trans_le (A.toLinearMap.singularValues_antitone (by omega))⟩
    have hg : Function.Injective g := by
      intro i j hij
      apply Fin.ext
      exact congrArg (fun z : s => z.val.val) hij
    have hcard := Fintype.card_le_of_injective g hg
    have hcontra : k + 1 ≤ finiteSingularCount A t := by
      simpa only [Fintype.card_fin, Fintype.card_coe, s, finiteSingularCount] using hcard
    omega
  · intro hsing
    apply (Finset.card_le_card (show s ⊆ finiteSingularPrefix (H := H) k from ?_)).trans
      (finiteSingularPrefix_card_le k)
    intro i hi
    apply (mem_finiteSingularPrefix k i).mpr
    have hti : t < A.toLinearMap.singularValues i := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    by_contra hn
    have hle := A.toLinearMap.singularValues_antitone (show k ≤ i.val by omega)
    exact (not_lt_of_ge (hle.trans hsing)) hti

/-- Genuine distribution subadditivity with independently chosen positive
thresholds. No spectral tail inequality is supplied as a certificate. -/
theorem finiteSingularCount_add_le (A B : H →L[ℝ] H) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    finiteSingularCount (A + B) (s + t) ≤ finiteSingularCount A s + finiteSingularCount B t := by
  apply (finiteSingularCount_le_iff (A + B) (add_nonneg hs ht) _).mpr
  exact (finiteSingularValue_add_le A B _ _).trans (add_le_add
    ((finiteSingularCount_le_iff A hs _).mp le_rfl)
    ((finiteSingularCount_le_iff B ht _).mp le_rfl))

/-- The actual spectral counting function has its genuine moment bound,
for every positive real exponent, including trace and Hilbert--Schmidt ones. -/
theorem finiteSingularCount_mul_rpow_le {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) {t p : ℝ} (ht : 0 ≤ t) (hp : 0 < p) :
    (finiteSingularCount A t : ℝ) * t ^ p ≤
      hsSchattenNorm b (finiteOperatorColumns b A) p ^ p := by
  classical
  let s := Finset.univ.filter fun i : Fin (Module.finrank ℝ H) => t < A.toLinearMap.singularValues i
  rw [finiteSchatten_rpow_eq_sum_singularValues b A hp]
  calc
    _ = ∑ _i ∈ s, t ^ p := by simp only [Finset.sum_const, nsmul_eq_mul, s, finiteSingularCount]
    _ ≤ ∑ i ∈ s, A.toLinearMap.singularValues i ^ p := by
      apply Finset.sum_le_sum
      intro i hi
      have hti : t < A.toLinearMap.singularValues i := (Finset.mem_filter.mp hi).2
      exact Real.rpow_le_rpow ht hti.le hp.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => Real.rpow_nonneg (A.toLinearMap.singularValues_nonneg i) p)

/-- Exact layer-cake representation of every positive finite Schatten
power, using the actual singular exceedance count and genuine integration. -/
theorem finiteSchatten_rpow_eq_lintegral_count {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (hsSchattenNorm b (finiteOperatorColumns b A) p ^ p) =
      ENNReal.ofReal p * ∫⁻ t : ℝ in Set.Ioi 0,
        (finiteSingularCount A t : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 1)) := by
  classical
  let f : Fin (Module.finrank ℝ H) → ℝ := fun i => A.toLinearMap.singularValues i
  have hcount (t : ℝ) : (Measure.count : Measure (Fin (Module.finrank ℝ H)))
      {i | t < f i} = (finiteSingularCount A t : ℝ≥0∞) := by
    have hset : {i | t < f i} =
        (↑(Finset.univ.filter fun i : Fin (Module.finrank ℝ H) => t < f i) : Set _) := by
      ext i
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hset, Measure.count_apply_finset]
    rfl
  have ht := lintegral_rpow_eq_lintegral_meas_lt_mul Measure.count (f := f)
    (Filter.Eventually.of_forall fun i => A.toLinearMap.singularValues_nonneg (i : Fin (Module.finrank ℝ H)))
    (measurable_of_finite f).aemeasurable hp
  simp only [hcount, lintegral_count, tsum_fintype] at ht
  rw [finiteSchatten_rpow_eq_sum_singularValues b A hp]
  have hsum := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (fun (i : Fin (Module.finrank ℝ H)) _ => Real.rpow_nonneg (A.toLinearMap.singularValues_nonneg i) p)
  rw [hsum]
  exact ht

end
end KernelSeq
