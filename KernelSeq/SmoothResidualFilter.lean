import KernelSeq.ResidualFilter
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Lattice

/-!
# The absolutely continuous sufficient condition for residual filters

The derivative hypothesis is only almost everywhere on the original closed
spectral interval.  The proof integrates the weighted residual in the spectral
coordinate and then evaluates its logarithmic primitive; it does not assume
absolute continuity of a change of variables or the desired Lipschitz bound.
-/

namespace KernelSeq.ResidualFilter
open MeasureTheory Set
open scoped Interval
noncomputable section

private theorem continuousOn_le_of_ae_le_Icc {f g : ℝ → ℝ} {M : ℝ} (hM : 0 < M)
    (hf : ContinuousOn f (Icc 0 M)) (hg : ContinuousOn g (Icc 0 M))
    (hfg : ∀ᵐ t ∂volume.restrict (Icc 0 M), f t ≤ g t) :
    ∀ t ∈ Icc 0 M, f t ≤ g t := by
  have he : f =ᵐ[volume.restrict (Icc 0 M)] fun t => min (f t) (g t) :=
    hfg.mono fun _ ht => (min_eq_left ht).symm
  have hmin : ContinuousOn (fun t => min (f t) (g t)) (Icc 0 M) :=
    continuous_min.comp_continuousOn (hf.prodMk hg)
  have hh := MeasureTheory.Measure.eqOn_of_ae_eq he hf hmin (by
    rw [interior_Icc, closure_Ioo hM.ne])
  intro t ht
  have := hh ht
  exact min_eq_left_iff.mp this.symm

/-- In the positive-length case, the a.e. smooth residual bound holds at
both endpoints as well, by absolute continuity. -/
theorem smooth_residual_bound {lam M ρ B : ℝ} {φ : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M)
    (hac : AbsolutelyContinuousOnInterval (residual φ) 0 M)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 M),
      |residual φ t| + (t + lam) * |deriv (residual φ) t| ≤
        B * (lam / (t + lam)) ^ ρ) :
    ∀ t ∈ Icc 0 M, |residual φ t| ≤ B * (lam / (t + lam)) ^ ρ := by
  apply continuousOn_le_of_ae_le_Icc hM
    (hac.continuousOn.mono (by rw [uIcc_of_le hM.le])).abs
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const
    · exact continuousOn_const.div (continuousOn_id.add continuousOn_const)
        (fun t ht => ne_of_gt (add_pos_of_nonneg_of_pos ht.1 hlam))
    · intro t ht
      exact Or.inl (ne_of_gt (div_pos hlam (add_pos_of_nonneg_of_pos ht.1 hlam)))
  · filter_upwards [hbound, ae_restrict_mem measurableSet_Icc] with t ht htm
    exact (le_add_of_nonneg_right (mul_nonneg (add_nonneg htm.1 hlam.le) (abs_nonneg _))).trans ht

private theorem ac_log_bound {g : ℝ → ℝ} {lam M C : ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M)
    (hac : AbsolutelyContinuousOnInterval g 0 M)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 M), |deriv g t| ≤ C / (t + lam))
    {s t : ℝ} (hs : s ∈ Icc 0 M) (ht : t ∈ Icc 0 M) (hst : s ≤ t) :
    |g t - g s| ≤ C * (Real.log (t + lam) - Real.log (s + lam)) := by
  have hsub : uIcc s t ⊆ uIcc 0 M := by
    rw [uIcc_of_le hst, uIcc_of_le hM]
    intro x hx
    exact ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
  have hac' := hac.mono hsub
  have hd : ∀ x ∈ uIcc s t, x + lam ≠ 0 := by
    intro x hx
    exact ne_of_gt (add_pos_of_nonneg_of_pos ((uIcc_of_le hM ▸ hsub hx).1) hlam)
  have hc : ContinuousOn (fun x : ℝ => C / (x + lam)) (uIcc s t) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const) hd
  have hi : IntervalIntegrable (fun x : ℝ => C / (x + lam)) volume s t := hc.intervalIntegrable
  have hle : ∀ᵐ x ∂volume.restrict (Icc s t), |deriv g x| ≤ C / (x + lam) :=
    ae_restrict_of_ae_restrict_of_subset (by
      intro x hx
      exact ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩) hbound
  have hf : ∀ x ∈ uIcc s t,
      HasDerivAt (fun x : ℝ => C * Real.log (x + lam)) (C / (x + lam)) x := by
    intro x hx
    simpa only [id_eq, div_eq_mul_inv, one_mul] using
      ((((hasDerivAt_id x).add_const lam).log (hd x hx)).const_mul C)
  calc
    |g t - g s| = ‖∫ x in s..t, deriv g x‖ := by
      rw [hac'.integral_deriv_eq_sub, Real.norm_eq_abs]
    _ ≤ ∫ x in s..t, ‖deriv g x‖ := intervalIntegral.norm_integral_le_integral_norm hst
    _ ≤ ∫ x in s..t, C / (x + lam) :=
      intervalIntegral.integral_mono_ae_restrict hst hac'.intervalIntegrable_deriv.norm hi
        (by
          filter_upwards [hle] with x hx
          simpa only [Real.norm_eq_abs] using hx)
    _ = C * (Real.log (t + lam) - Real.log (s + lam)) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hf hi]
      ring

private theorem hasDerivAt_spectralWeight {lam ρ t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => ((s + lam) / lam) ^ ρ)
      (ρ * ((t + lam) / lam) ^ ρ / (t + lam)) t := by
  have hb : 0 < (t + lam) / lam := div_pos (add_pos_of_nonneg_of_pos ht hlam) hlam
  have hh : HasDerivAt (fun s : ℝ => ((s + lam) / lam) ^ ρ)
      ((1 / lam) * ρ * ((t + lam) / lam) ^ (ρ - 1)) t :=
    (((hasDerivAt_id t).add_const lam).div_const lam).rpow_const (Or.inl hb.ne')
  convert hh using 1
  rw [Real.rpow_sub_one hb.ne']
  field_simp

private theorem spectralWeight_ac {lam M ρ : ℝ} (hlam : 0 < lam) (hM : 0 ≤ M) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ((t + lam) / lam) ^ ρ) 0 M := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  apply ContDiffOn.rpow_const_of_ne
  · fun_prop
  · intro t ht
    exact ne_of_gt (div_pos (add_pos_of_nonneg_of_pos ((uIcc_of_le hM ▸ ht).1) hlam) hlam)

private theorem smooth_weighted_log_bound {lam M ρ B : ℝ} {φ : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hac : AbsolutelyContinuousOnInterval (residual φ) 0 M)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 M),
      |residual φ t| + (t + lam) * |deriv (residual φ) t| ≤
        B * (lam / (t + lam)) ^ ρ)
    {s t : ℝ} (hs : s ∈ Icc 0 M) (ht : t ∈ Icc 0 M) (hst : s ≤ t) :
    |((t + lam) / lam) ^ ρ * residual φ t -
        ((s + lam) / lam) ^ ρ * residual φ s| ≤
      (B * max ρ 1) * (Real.log (t + lam) - Real.log (s + lam)) := by
  let w := fun x : ℝ => ((x + lam) / lam) ^ ρ
  have hacw := spectralWeight_ac (ρ := ρ) hlam hM
  apply ac_log_bound hlam hM (hacw.mul hac) (s := s) (t := t) ?_ hs ht hst
  have hdiff : ∀ᵐ x ∂volume.restrict (Icc 0 M), DifferentiableAt ℝ (residual φ) x := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    simpa only [uIcc_of_le hM] using hac.ae_differentiableAt
  filter_upwards [hbound, hdiff, ae_restrict_mem measurableSet_Icc] with x hx hdx hxm
  have hd : 0 < x + lam := add_pos_of_nonneg_of_pos hxm.1 hlam
  have hw : 0 ≤ w x := Real.rpow_nonneg (by positivity) _
  have hp : w x * (lam / (x + lam)) ^ ρ = 1 := by
    rw [← Real.mul_rpow (div_nonneg hd.le hlam.le) (div_nonneg hlam.le hd.le)]
    have : ((x + lam) / lam) * (lam / (x + lam)) = 1 := by field_simp
    rw [this, Real.one_rpow]
  have hderiv := ((hasDerivAt_spectralWeight (ρ := ρ) hlam hxm.1).mul hdx.hasDerivAt).deriv
  change |deriv ((fun s => ((s + lam) / lam) ^ ρ) * residual φ) x| ≤ _
  rw [hderiv]
  have hab : |ρ * w x / (x + lam) * residual φ x + w x * deriv (residual φ) x| ≤
      w x / (x + lam) * (max ρ 1 *
        (|residual φ x| + (x + lam) * |deriv (residual φ) x|)) := by
    calc
      _ ≤ |ρ * w x / (x + lam) * residual φ x| + |w x * deriv (residual φ) x| := abs_add_le _ _
      _ = w x / (x + lam) * (ρ * |residual φ x| + (x + lam) * |deriv (residual φ) x|) := by
        rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hρ, abs_of_nonneg hw,
          abs_of_pos hd, abs_mul, abs_of_nonneg hw]
        field_simp
      _ ≤ _ := by
        gcongr
        nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left ρ 1)) (abs_nonneg (residual φ x)),
          mul_nonneg (sub_nonneg.mpr (le_max_right ρ 1))
            (mul_nonneg hd.le (abs_nonneg (deriv (residual φ) x)))]
  calc
    _ ≤ _ := hab
    _ ≤ w x / (x + lam) * (max ρ 1 * (B * (lam / (x + lam)) ^ ρ)) := by
      gcongr
    _ = B * max ρ 1 / (x + lam) := by
      calc
        _ = (B * max ρ 1 / (x + lam)) * (w x * (lam / (x + lam)) ^ ρ) := by ring
        _ = _ := by rw [hp, mul_one]

/-- The derivative bound gives the same constant in the residual contract on
a nondegenerate spectral interval. Only the residual is absolutely continuous. The inverse
profile is not assumed continuous or Lipschitz. -/
theorem contract_of_smooth_condition {lam M ρ B : ℝ} {φ : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M) (hρ : 0 < ρ)
    (hf : SpectralFilter M φ)
    (hac : AbsolutelyContinuousOnInterval (residual φ) 0 M)
    (hinv : ∀ t ∈ Icc 0 M, (t + lam) * φ t ≤ B)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 M),
      |residual φ t| + (t + lam) * |deriv (residual φ) t| ≤
        B * (lam / (t + lam)) ^ ρ) :
    Contract lam M ρ (B * max 2 ρ) φ := by
  have hψ := smooth_residual_bound hlam hM hac hbound
  have hB1 : 1 ≤ B := by
    simpa [residual, shrinkage, div_self hlam.ne'] using hψ 0 ⟨le_rfl, hM.le⟩
  have hB : 0 ≤ B := zero_le_one.trans hB1
  have hwbound (u : ℝ) (hu : u ∈ logDomain lam M) : |weightedResidual lam ρ φ u| ≤ B := by
    let t := spectralCoordinate lam u
    have ht := spectralCoordinate_mem hlam hM.le hu
    have hd : 0 < t + lam := add_pos_of_nonneg_of_pos ht.1 hlam
    have hw : 0 ≤ ((t + lam) / lam) ^ ρ := Real.rpow_nonneg (by positivity) _
    have hp : ((t + lam) / lam) ^ ρ * (lam / (t + lam)) ^ ρ = 1 := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      have : ((t + lam) / lam) * (lam / (t + lam)) = 1 := by field_simp
      rw [this, Real.one_rpow]
    change |((t + lam) / lam) ^ ρ * residual φ t| ≤ B
    rw [abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ ((t + lam) / lam) ^ ρ * (B * (lam / (t + lam)) ^ ρ) :=
        mul_le_mul_of_nonneg_left (hψ t ht) hw
      _ = B := by rw [mul_left_comm, hp, mul_one]
  have hlog (u : ℝ) : Real.log (spectralCoordinate lam u + lam) = Real.log lam + u := by
    have hd : spectralCoordinate lam u + lam = lam * Real.exp u := by unfold spectralCoordinate; ring
    rw [hd, Real.log_mul hlam.ne' (Real.exp_ne_zero _), Real.log_exp]
  have hlip (u v : ℝ) (hu : u ∈ logDomain lam M) (hv : v ∈ logDomain lam M) (huv : u ≤ v) :
      |weightedResidual lam ρ φ v - weightedResidual lam ρ φ u| ≤
        (B * max 2 ρ) * (v - u) := by
    have hst : spectralCoordinate lam u ≤ spectralCoordinate lam v := by
      unfold spectralCoordinate
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_le_exp.mpr huv) 1) hlam.le
    have hh := smooth_weighted_log_bound hlam hM.le hρ.le hac hbound
      (spectralCoordinate_mem hlam hM.le hu) (spectralCoordinate_mem hlam hM.le hv) hst
    change |weightedResidual lam ρ φ v - weightedResidual lam ρ φ u| ≤ _ at hh
    rw [hlog, hlog] at hh
    have hm : max ρ 1 ≤ max 2 ρ := max_le (le_max_right _ _) ((by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _))
    calc
      _ ≤ (B * max ρ 1) * (v - u) := by convert hh using 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hB) (sub_nonneg.mpr huv)
  constructor
  · exact hρ
  · intro u hu
    have ht := spectralCoordinate_mem hlam hM.le hu
    have hF0 : 0 ≤ inverseProfile lam φ u :=
      mul_nonneg (add_nonneg ht.1 hlam.le) (hf.nonneg _ ht)
    have hF := hinv _ ht
    change inverseProfile lam φ u ≤ B at hF
    rw [abs_of_nonneg hF0]
    calc
      _ ≤ B + B := add_le_add hF (hwbound u hu)
      _ ≤ B * max 2 ρ := by nlinarith [le_max_left (2 : ℝ) ρ]
  · intro u hu v hv
    rcases le_total u v with huv | hvu
    · simpa only [abs_sub_comm (weightedResidual lam ρ φ u), abs_of_nonpos (sub_nonpos.mpr huv), neg_sub]
        using hlip u v hu hv huv
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hvu)] using hlip v u hv hu hvu

/-- A version covering also the degenerate interval `M=0`, without an
additional hypothesis on the input constant B.  Enlarging B to `max B 1`
is harmless in the existential smooth-filter condition. On a singleton an
a.e. condition alone cannot control the value of the residual at zero. -/
theorem contract_of_smooth_condition_nonnegative_interval {lam M ρ B : ℝ} {φ : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hf : SpectralFilter M φ)
    (hac : AbsolutelyContinuousOnInterval (residual φ) 0 M)
    (hinv : ∀ t ∈ Icc 0 M, (t + lam) * φ t ≤ B)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 M),
      |residual φ t| + (t + lam) * |deriv (residual φ) t| ≤
        B * (lam / (t + lam)) ^ ρ) :
    Contract lam M ρ (max B 1 * max 2 ρ) φ := by
  rcases lt_or_eq_of_le hM with hMp | hM0
  · apply contract_of_smooth_condition hlam hMp hρ hf hac
    · intro t ht
      exact (hinv t ht).trans (le_max_left _ _)
    · filter_upwards [hbound, ae_restrict_mem measurableSet_Icc] with t ht htm
      exact ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (div_nonneg hlam.le (add_nonneg htm.1 hlam.le)) _))
  · subst M
    have hB : (1 : ℝ) ≤ max B 1 := le_max_right _ _
    have hmax : (2 : ℝ) ≤ max 2 ρ := le_max_left _ _
    constructor
    · exact hρ
    · intro u hu
      have hu0 : u = 0 := le_antisymm (by simpa [logDomain] using hu.2) hu.1
      subst u
      have hφ : 0 ≤ lam * φ 0 := mul_nonneg hlam.le (hf.nonneg 0 ⟨le_rfl, le_rfl⟩)
      have hi : lam * φ 0 ≤ B := by simpa using hinv 0 ⟨le_rfl, le_rfl⟩
      simp only [inverseProfile, weightedResidual, spectralCoordinate, Real.exp_zero,
        sub_self, mul_zero, zero_add, div_self hlam.ne', Real.one_rpow,
        residual, shrinkage, zero_mul, sub_zero, one_mul, abs_one, abs_of_nonneg hφ]
      nlinarith [le_max_left B 1]
    · intro u _ v _
      have hu0 : u = 0 := by
        have hu := ‹u ∈ logDomain lam 0›
        exact le_antisymm (by simpa [logDomain] using hu.2) hu.1
      have hv0 : v = 0 := by
        have hv := ‹v ∈ logDomain lam 0›
        exact le_antisymm (by simpa [logDomain] using hv.2) hv.1
      subst u
      subst v
      simp

end
end KernelSeq.ResidualFilter
