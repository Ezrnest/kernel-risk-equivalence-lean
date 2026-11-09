import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith

/-!
# Scalar regularization weights and summability
-/

namespace KernelFoundations

/-- Every spectral value has a regularization weight in (0,1]. -/
theorem regularization_weight_mem {lam M t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M) :
    0 < lam / (t + lam) ∧ lam / (t + lam) ≤ 1 := by
  have hden : 0 < t + lam := add_pos_of_nonneg_of_pos ht.1 hlam
  exact ⟨div_pos hlam hden, (div_le_one hden).2 (by linarith [ht.1])⟩

/-- The regularized spectral target series is summable by direct comparison
with the unweighted square-summable coefficient sequence. -/
theorem summable_regularized_coefficients {J : Type*} {lam M α : ℝ}
    (t f : J → ℝ) (hlam : 0 < lam) (hα : 0 ≤ α)
    (ht : ∀ j, t j ∈ Set.Icc (0 : ℝ) M)
    (hf : Summable (fun j => f j ^ 2)) :
    Summable (fun j => (lam / (t j + lam)) ^ α * f j ^ 2) := by
  apply Summable.of_nonneg_of_le _ _ hf
  · intro j
    exact mul_nonneg (Real.rpow_nonneg (regularization_weight_mem hlam (ht j)).1.le _)
      (sq_nonneg _)
  · intro j
    have hb := regularization_weight_mem hlam (ht j)
    have hpow := Real.rpow_le_one hb.1.le hb.2 hα
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (sq_nonneg (f j))

end KernelFoundations
