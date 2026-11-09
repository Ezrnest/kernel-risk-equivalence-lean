import KernelSeq.ResidualFilter
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Iterated ridge as an actual admissible residual filter

The iterated ridge inverse is a finite geometric sum. The definition supplies
the removable value at zero.  Both spectral admissibility and the exact
scale-regular contract are proved, uniformly in the spectral bound and λ.
-/

namespace KernelSeq.ResidualFilter

open scoped BigOperators

noncomputable section

/-- The ν-fold iterated-ridge inverse, including its actual value at zero. -/
def iteratedRidge (lam : ℝ) (ν : ℕ) (t : ℝ) : ℝ :=
  (t + lam)⁻¹ * ∑ j ∈ Finset.range ν, (lam / (t + lam)) ^ j

theorem iteratedRidge_zero {lam : ℝ} (hlam : 0 < lam) (ν : ℕ) :
    iteratedRidge lam ν 0 = (ν : ℝ) / lam := by
  simp [iteratedRidge, div_self hlam.ne', div_eq_mul_inv, mul_comm]

theorem iteratedRidge_shrinkage {lam t : ℝ} (hden : t + lam ≠ 0) (ν : ℕ) :
    shrinkage (iteratedRidge lam ν) t = 1 - (lam / (t + lam)) ^ ν := by
  have h := geom_sum_mul (lam / (t + lam)) ν
  have ht : t * (t + lam)⁻¹ = 1 - lam / (t + lam) := by
    field_simp
    ring
  unfold shrinkage iteratedRidge
  rw [← mul_assoc, ht]
  nlinarith [h]

theorem iteratedRidge_residual {lam t : ℝ} (hden : t + lam ≠ 0) (ν : ℕ) :
    residual (iteratedRidge lam ν) t = (lam / (t + lam)) ^ ν := by
  rw [residual, iteratedRidge_shrinkage hden]
  ring

theorem iteratedRidge_inverseProfile {lam : ℝ} (hlam : 0 < lam) (ν : ℕ) (u : ℝ) :
    inverseProfile lam (iteratedRidge lam ν) u =
      ∑ j ∈ Finset.range ν, (Real.exp (-u)) ^ j := by
  have hd : spectralCoordinate lam u + lam = lam * Real.exp u := by
    unfold spectralCoordinate
    ring
  have hd0 : spectralCoordinate lam u + lam ≠ 0 := by
    rw [hd]
    positivity
  have hr : lam / (spectralCoordinate lam u + lam) = Real.exp (-u) := by
    rw [hd, Real.exp_neg, div_mul_cancel_left₀ hlam.ne']
  simp only [inverseProfile, iteratedRidge, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul, hr]

theorem iteratedRidge_weightedResidual {lam : ℝ} (hlam : 0 < lam) (ν : ℕ) (u : ℝ) :
    weightedResidual lam (ν : ℝ) (iteratedRidge lam ν) u = 1 := by
  have hd : spectralCoordinate lam u + lam = lam * Real.exp u := by
    unfold spectralCoordinate
    ring
  have hd0 : spectralCoordinate lam u + lam ≠ 0 := by rw [hd]; positivity
  rw [weightedResidual, iteratedRidge_residual hd0, Real.rpow_natCast]
  rw [← mul_pow]
  have : ((spectralCoordinate lam u + lam) / lam) *
      (lam / (spectralCoordinate lam u + lam)) = 1 := by
    field_simp
  rw [this, one_pow]

theorem iteratedRidge_spectralFilter {lam M : ℝ} (hlam : 0 < lam) (ν : ℕ) :
    SpectralFilter M (iteratedRidge lam ν) := by
  constructor
  · apply Continuous.measurable
    unfold iteratedRidge
    have hd : ∀ t : Set.Icc (0 : ℝ) M, (t : ℝ) + lam ≠ 0 :=
      fun t => ne_of_gt (add_pos_of_nonneg_of_pos t.property.1 hlam)
    exact ((continuous_subtype_val.add continuous_const).inv₀ hd).mul
      (continuous_finsetSum _ fun j _ =>
        (continuous_const.div (continuous_subtype_val.add continuous_const) hd).pow j)
  · intro t ht
    apply mul_nonneg (inv_nonneg.mpr (add_nonneg ht.1 hlam.le))
    exact Finset.sum_nonneg fun j _ => pow_nonneg (div_nonneg hlam.le (add_nonneg ht.1 hlam.le)) j
  · intro t ht
    have hd : 0 < t + lam := add_pos_of_nonneg_of_pos ht.1 hlam
    have hr0 : 0 ≤ lam / (t + lam) := div_nonneg hlam.le hd.le
    have hr1 : lam / (t + lam) ≤ 1 := (div_le_one hd).2 (le_add_of_nonneg_left ht.1)
    rw [iteratedRidge_shrinkage hd.ne']
    exact ⟨sub_nonneg.mpr (pow_le_one₀ hr0 hr1), sub_le_self _ (pow_nonneg hr0 _)⟩

/-- Exact residual order ν and a constant ν+1, independent of λ and M. -/
theorem iteratedRidge_contract {lam M : ℝ} (hlam : 0 < lam) {ν : ℕ} (hν : 0 < ν) :
    Contract lam M (ν : ℝ) ((ν : ℝ) + 1) (iteratedRidge lam ν) := by
  constructor
  · exact Nat.cast_pos.mpr hν
  · intro u hu
    rw [iteratedRidge_inverseProfile hlam, iteratedRidge_weightedResidual hlam]
    have he0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
    have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.1)
    rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg he0 j), abs_one]
    have hs : ∑ j ∈ Finset.range ν, Real.exp (-u) ^ j ≤ (ν : ℝ) := by
      calc
        _ ≤ ∑ _j ∈ Finset.range ν, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => pow_le_one₀ he0 he1
        _ = _ := by simp
    linarith
  · intro u _ v _
    rw [iteratedRidge_weightedResidual hlam, iteratedRidge_weightedResidual hlam]
    simp only [sub_self, abs_zero]
    positivity

end
end KernelSeq.ResidualFilter
