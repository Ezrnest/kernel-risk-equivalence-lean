import KernelSeq.SpectralSumCounting
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Actual spectral sums as counting integrals

Absolute continuity and an integrable absolute counting kernel imply genuine
summability and the exact count-integral identity. The half-closed primitive
interval `Ioc 0 a` matches the non-strict spectral count directly, so atoms at
individual eigenvalue thresholds cause no diagonal exception.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

theorem spectralCounting_kernel_hasSum {w : ℕ → ℝ} (hs : Summable w)
    {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) (v : ℝ) :
    HasSum (fun j => if u ≤ w j / lam then v else 0)
      (spectralCounting w (lam * u) * v) := by
  classical
  have hfin := finite_spectrum_above hs (mul_pos hlam hu)
  let s := hfin.toFinset
  have hmem (j : ℕ) : j ∈ s ↔ u ≤ w j / lam := by
    simp only [s, Finite.mem_toFinset, mem_setOf_eq]
    rw [le_div_iff₀ hlam, mul_comm]
  have hh : HasSum (fun j => if u ≤ w j / lam then v else 0)
      (∑ j ∈ s, if u ≤ w j / lam then v else 0) :=
    hasSum_sum_of_ne_finset_zero (s := s)
      (fun j hj => if_neg (fun h => hj ((hmem j).2 h)))
  have heq : (∑ j ∈ s, if u ≤ w j / lam then v else 0) = spectralCounting w (lam * u) * v := by
    rw [spectralCounting_eq_ncard hs (mul_pos hlam hu), Set.ncard_eq_toFinset_card _ hfin]
    calc
      _ = ∑ _j ∈ s, v := Finset.sum_congr rfl (fun j hj => if_pos ((hmem j).1 hj))
      _ = _ := by simp [s]
  rwa [heq] at hh

/-- This is the actual signed Fubini identity, together with summability.
The counting integrability premise is supplied from the exact counting and
original derivative assumptions in the final spectral-sum theorem. -/
theorem hasSum_spectral_values_of_integrable_count_deriv {w : ℕ → ℝ}
    (hs : Summable w) (hw : ∀ j, 0 ≤ w j) {lam : ℝ} (hlam : 0 < lam)
    (G : ℝ → ℝ) (hG0 : G 0 = 0)
    (hac : ∀ R, 0 ≤ R → AbsolutelyContinuousOnInterval G 0 R)
    (hi : IntegrableOn (fun u => spectralCounting w (lam * u) * |deriv G u|) (Ioi 0)) :
    HasSum (fun j => G (w j / lam))
      (∫ u in Ioi (0 : ℝ), spectralCounting w (lam * u) * deriv G u) := by
  let F : ℕ → ℝ → ℝ := fun j => (Iic (w j / lam)).indicator (deriv G)
  have hFm : ∀ j, AEStronglyMeasurable (F j) (volume.restrict (Ioi (0 : ℝ))) := by
    intro j
    exact ((measurable_deriv G).indicator measurableSet_Iic).aestronglyMeasurable
  have hnorm (u : ℝ) (hu : 0 < u) : HasSum (fun j => ‖F j u‖)
      (spectralCounting w (lam * u) * |deriv G u|) := by
    convert spectralCounting_kernel_hasSum hs hlam hu |deriv G u| using 1
    funext j
    simp only [F, Set.indicator, mem_Iic, Real.norm_eq_abs]
    split_ifs <;> simp
  have hnormInt : Integrable (fun u => ∑' j, ‖F j u‖) (volume.restrict (Ioi (0 : ℝ))) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hnorm u hu).tsum_eq.symm
  have hhas : HasSum (fun j => ∫ u in Ioi (0 : ℝ), F j u)
      (∫ u in Ioi (0 : ℝ), spectralCounting w (lam * u) * deriv G u) := by
    apply hasSum_integral_of_dominated_convergence (fun j u => ‖F j u‖) hFm
      (fun _ => Eventually.of_forall fun _ => le_rfl) ?_ hnormInt ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (hnorm u hu).summable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simpa only [F, Set.indicator, mem_Iic] using
        spectralCounting_kernel_hasSum hs hlam hu (deriv G u)
  have hInt (j : ℕ) : (∫ u in Ioi (0 : ℝ), F j u) = G (w j / lam) := by
    change (∫ u in Ioi (0 : ℝ), (Iic (w j / lam)).indicator (deriv G) u) = _
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hset : Iic (w j / lam) ∩ Ioi (0 : ℝ) = Ioc 0 (w j / lam) := by
      ext u
      simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]
      tauto
    rw [hset, ← intervalIntegral.integral_of_le (div_nonneg (hw j) hlam.le),
      (hac _ (div_nonneg (hw j) hlam.le)).integral_deriv_eq_sub, hG0, sub_zero]
  simpa only [hInt] using hhas

theorem spectral_sum_eq_counting_integral {w : ℕ → ℝ}
    (hs : Summable w) (hw : ∀ j, 0 ≤ w j) {lam : ℝ} (hlam : 0 < lam)
    (G : ℝ → ℝ) (hG0 : G 0 = 0)
    (hac : ∀ R, 0 ≤ R → AbsolutelyContinuousOnInterval G 0 R)
    (hi : IntegrableOn (fun u => spectralCounting w (lam * u) * |deriv G u|) (Ioi 0)) :
    (∑' j, G (w j / lam)) = ∫ u in Ioi (0 : ℝ), spectralCounting w (lam * u) * deriv G u :=
  (hasSum_spectral_values_of_integrable_count_deriv hs hw hlam G hG0 hac hi).tsum_eq

end
end KernelSeq
