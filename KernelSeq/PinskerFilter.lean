import KernelSeq.AuxiliaryFilter
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Pinsker spectral filters

The profile is the manuscript's exact positive-part Pinsker shrinkage, including
zero and the spectral threshold. The residual order is `min (s/2) 1`.
-/

namespace KernelSeq.ResidualFilter

noncomputable section

/-- A global formula for the Pinsker inverse filter. On `t ≤ lam` its numerator
vanishes; in particular the value at zero is zero. -/
def pinsker (lam s t : ℝ) : ℝ := (1 - (lam / max t lam) ^ (s / 2)) / t

def pinskerOrder (s : ℝ) : ℝ := min (s / 2) 1

theorem pinsker_eq_zero_of_le {lam s t : ℝ} (hlam : 0 < lam) (ht : t ≤ lam) :
    pinsker lam s t = 0 := by
  simp [pinsker, max_eq_right ht, div_self hlam.ne']

theorem pinsker_eq_of_lt {lam s t : ℝ} (ht : lam < t) :
    pinsker lam s t = (1 - (lam / t) ^ (s / 2)) / t := by
  simp [pinsker, max_eq_left ht.le]

theorem pinsker_shrinkage {lam s : ℝ} (hlam : 0 < lam) (t : ℝ) :
    shrinkage (pinsker lam s) t = 1 - (lam / max t lam) ^ (s / 2) := by
  by_cases ht : t = 0
  · subst t
    simp [shrinkage, max_eq_right hlam.le, div_self hlam.ne']
  · unfold shrinkage pinsker
    field_simp

theorem pinsker_residual {lam s : ℝ} (hlam : 0 < lam) (t : ℝ) :
    residual (pinsker lam s) t = (lam / max t lam) ^ (s / 2) := by
  rw [residual, pinsker_shrinkage hlam]
  ring

theorem pinsker_shrinkage_eq {lam s t : ℝ} (hlam : 0 < lam) :
    shrinkage (pinsker lam s) t =
      if t ≤ lam then 0 else 1 - (lam / t) ^ (s / 2) := by
  by_cases ht : t ≤ lam
  · simp [ht, shrinkage, pinsker_eq_zero_of_le hlam ht]
  · rw [if_neg ht, pinsker_shrinkage hlam, max_eq_left (le_of_not_ge ht)]

theorem pinsker_order_bounds {s : ℝ} (hs : 1 ≤ s) :
    1 / 2 ≤ pinskerOrder s ∧ pinskerOrder s ≤ 1 ∧ pinskerOrder s ≤ s / 2 := by
  unfold pinskerOrder
  exact ⟨le_min (by linarith) (by norm_num), min_le_right _ _, min_le_left _ _⟩

/-- Genuine Borel admissibility, independent of a continuity certificate. -/
theorem pinsker_spectralFilter {lam M s : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) :
    SpectralFilter M (pinsker lam s) := by
  have hc : Continuous (fun t : ℝ => (lam / max t lam) ^ (s / 2)) := by
    apply (continuous_const.div (continuous_id.max continuous_const)
      (fun t => ne_of_gt (hlam.trans_le (le_max_right t lam)))).rpow_const
    intro t
    right
    positivity
  constructor
  · exact ((continuous_const.sub hc).measurable.div measurable_id).comp measurable_subtype_coe
  · intro t ht
    by_cases htl : t ≤ lam
    · rw [pinsker_eq_zero_of_le hlam htl]
    · have htp : 0 < t := hlam.trans (lt_of_not_ge htl)
      rw [pinsker_eq_of_lt (lt_of_not_ge htl)]
      exact div_nonneg (sub_nonneg.mpr (Real.rpow_le_one (div_nonneg hlam.le htp.le)
        ((div_le_one htp).2 (le_of_not_ge htl)) (by positivity))) ht.1
  · intro t _
    rw [pinsker_shrinkage hlam]
    have hm : 0 < max t lam := hlam.trans_le (le_max_right _ _)
    have hr := Real.rpow_nonneg (div_nonneg hlam.le hm.le) (s / 2)
    have hr1 := Real.rpow_le_one (div_nonneg hlam.le hm.le)
      ((div_le_one hm).2 (le_max_right _ _)) (by positivity : 0 ≤ s / 2)
    constructor <;> linarith

theorem pinsker_inverse_size {lam s t : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) :
    |(t + lam) * pinsker lam s t| ≤ 2 := by
  by_cases htl : t ≤ lam
  · simp [pinsker_eq_zero_of_le hlam htl]
  · have htp : 0 < t := hlam.trans (lt_of_not_ge htl)
    have hratio : lam / t ≤ 1 := (div_le_one htp).2 (le_of_not_ge htl)
    have hr0 := Real.rpow_nonneg (div_nonneg hlam.le htp.le) (s / 2)
    have hr1 := Real.rpow_le_one (div_nonneg hlam.le htp.le) hratio (by positivity : 0 ≤ s / 2)
    rw [pinsker_eq_of_lt (lt_of_not_ge htl), abs_of_nonneg (by positivity)]
    have hsmall : (1 - (lam / t) ^ (s / 2)) / t ≤ 1 / t :=
      div_le_div_of_nonneg_right (by linarith) htp.le
    calc
      (t + lam) * ((1 - (lam / t) ^ (s / 2)) / t) ≤ (t + lam) * (1 / t) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ 2 := by rw [mul_one_div]; apply (div_le_iff₀ htp).2; linarith

/-- Pinsker qualification has exact constant one throughout the manuscript's
full interval `0 ≤ τ ≤ s/2`, beyond the clipped contract order. -/
theorem pinsker_qualification {lam s t τ : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t)
    (hτ : 0 ≤ τ) (hτs : τ ≤ s / 2) :
    t ^ τ * |residual (pinsker lam s) t| ≤ lam ^ τ := by
  rw [pinsker_residual hlam, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  by_cases htl : t ≤ lam
  · rw [max_eq_right htl, div_self hlam.ne', Real.one_rpow, mul_one]
    exact Real.rpow_le_rpow ht htl hτ
  · have htp : 0 < t := hlam.trans (lt_of_not_ge htl)
    rw [max_eq_left (le_of_not_ge htl)]
    have hpow := Real.rpow_le_rpow_of_exponent_ge (div_pos hlam htp)
      ((div_le_one htp).2 (le_of_not_ge htl)) hτs
    calc
      t ^ τ * (lam / t) ^ (s / 2) ≤ t ^ τ * (lam / t) ^ τ :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg ht _)
      _ = lam ^ τ := by rw [← Real.mul_rpow ht (div_nonneg hlam.le htp.le)]; congr 1; field_simp

theorem pinsker_zero {lam s : ℝ} (hlam : 0 < lam) : pinsker lam s 0 = 0 :=
  pinsker_eq_zero_of_le hlam hlam.le

theorem pinsker_at_threshold {lam s : ℝ} (hlam : 0 < lam) : pinsker lam s lam = 0 :=
  pinsker_eq_zero_of_le hlam le_rfl

theorem pinsker_residual_zero (lam s : ℝ) :
    residual (pinsker lam s) 0 = 1 := by simp [residual, shrinkage]

theorem pinsker_residual_at_threshold {lam s : ℝ} (hlam : 0 < lam) :
    residual (pinsker lam s) lam = 1 := by simp [residual, shrinkage, pinsker_at_threshold hlam]

private def pinskerHigh (r ρ u : ℝ) : ℝ :=
  Real.exp (ρ * u - r * Real.log (Real.exp u - 1))

private theorem pinskerHigh_bounds {r ρ u : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρr : ρ ≤ r) (hu : Real.log 2 ≤ u) :
    0 < pinskerHigh r ρ u ∧ pinskerHigh r ρ u ≤ 2 := by
  have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : 2 ≤ Real.exp u := by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hu
  have hz : 0 < Real.exp u - 1 := by linarith
  have hl : 0 ≤ Real.log (Real.exp u - 1) := Real.log_nonneg (by linarith)
  have hd : u - Real.log (Real.exp u - 1) ≤ Real.log 2 := by
    have h := Real.log_le_log (div_pos (Real.exp_pos u) (by norm_num : (0 : ℝ) < 2))
      (by linarith : Real.exp u / 2 ≤ Real.exp u - 1)
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] at h
    linarith
  have hmul := mul_le_mul_of_nonneg_left hd hρ0
  have hrc := mul_le_mul_of_nonneg_right hρ1 hc
  have hrs := mul_nonneg (sub_nonneg.mpr hρr) hl
  refine ⟨Real.exp_pos _, ?_⟩
  have hh : ρ * u - r * Real.log (Real.exp u - 1) ≤ Real.log 2 := by nlinarith
  simpa only [pinskerHigh, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hh

private theorem pinskerHigh_hasDerivAt {r ρ u : ℝ} (hu : Real.log 2 ≤ u) :
    HasDerivAt (pinskerHigh r ρ)
      (pinskerHigh r ρ u * (ρ - r * (Real.exp u / (Real.exp u - 1)))) u := by
  have he : 2 ≤ Real.exp u := by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hu
  have hz : Real.exp u - 1 ≠ 0 := by linarith
  change HasDerivAt (fun z => Real.exp (ρ * z - r * Real.log (Real.exp z - 1))) _ u
  simpa only [pinskerHigh, mul_one, id_eq, Pi.sub_apply] using
    (((hasDerivAt_id u).const_mul ρ).sub
      ((((Real.hasDerivAt_exp u).sub_const 1).log hz).const_mul r)).exp

private theorem pinskerHigh_lipschitz {r ρ u v : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρr : ρ ≤ r) (hu : Real.log 2 ≤ u) (hv : Real.log 2 ≤ v) :
    |pinskerHigh r ρ u - pinskerHigh r ρ v| ≤ (4 * r) * |u - v| := by
  have hr : 0 ≤ r := hρ0.trans hρr
  have hbound : ∀ z ∈ Set.Ici (Real.log (2 : ℝ)),
      ‖pinskerHigh r ρ z * (ρ - r * (Real.exp z / (Real.exp z - 1)))‖ ≤ 4 * r := by
    intro z hz
    have he : 2 ≤ Real.exp z := by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hz
    have hd : 0 < Real.exp z - 1 := by linarith
    have hrat0 : 0 ≤ Real.exp z / (Real.exp z - 1) := div_nonneg (Real.exp_pos _).le hd.le
    have hrat2 : Real.exp z / (Real.exp z - 1) ≤ 2 := (div_le_iff₀ hd).2 (by linarith)
    have hb : |ρ - r * (Real.exp z / (Real.exp z - 1))| ≤ 2 * r := by
      apply abs_le.mpr
      constructor <;> nlinarith
    have hp := pinskerHigh_bounds hρ0 hρ1 hρr hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp.1]
    calc
      _ ≤ 2 * (2 * r) := mul_le_mul hp.2 hb (abs_nonneg _) (by norm_num)
      _ = 4 * r := by ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (pinskerHigh_hasDerivAt hz).hasDerivWithinAt) hbound
    (convex_Ici (Real.log (2 : ℝ))) hv hu
  simpa only [Real.norm_eq_abs] using h

private theorem pinsker_weightedResidual_low {lam s ρ u : ℝ} (hlam : 0 < lam)
    (hu : u ≤ Real.log 2) : weightedResidual lam ρ (pinsker lam s) u = Real.exp (ρ * u) := by
  have he : Real.exp u ≤ 2 := by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hu
  have ht : spectralCoordinate lam u ≤ lam := by unfold spectralCoordinate; nlinarith
  rw [weightedResidual_eq_exp_mul hlam, residual, shrinkage, pinsker_eq_zero_of_le hlam ht]
  ring

private theorem pinsker_weightedResidual_high {lam s ρ u : ℝ} (hlam : 0 < lam)
    (hu : Real.log 2 ≤ u) :
    weightedResidual lam ρ (pinsker lam s) u = pinskerHigh (s / 2) ρ u := by
  have he : 2 ≤ Real.exp u := by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hu
  have ht : lam ≤ spectralCoordinate lam u := by unfold spectralCoordinate; nlinarith
  have hz : 0 < Real.exp u - 1 := by linarith
  have hdiv : lam / spectralCoordinate lam u = (Real.exp u - 1)⁻¹ := by
    unfold spectralCoordinate
    field_simp
  rw [weightedResidual_eq_exp_mul hlam, pinsker_residual hlam, max_eq_left ht, hdiv,
    Real.rpow_def_of_pos (inv_pos.mpr hz), Real.log_inv, pinskerHigh, ← Real.exp_add]
  congr 1
  ring

private theorem pinsker_low_lipschitz {ρ u v : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hu : u ∈ Set.Icc (0 : ℝ) (Real.log 2)) (hv : v ∈ Set.Icc (0 : ℝ) (Real.log 2)) :
    |Real.exp (ρ * u) - Real.exp (ρ * v)| ≤ (2 * ρ) * |u - v| := by
  have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hru : ρ * u ≤ Real.log 2 :=
    (mul_le_mul_of_nonneg_left hu.2 hρ0).trans (by nlinarith)
  have hrv : ρ * v ≤ Real.log 2 :=
    (mul_le_mul_of_nonneg_left hv.2 hρ0).trans (by nlinarith)
  have h := abs_exp_sub_exp_le_upper hru hrv
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2), ← mul_sub, abs_mul, abs_of_nonneg hρ0] at h
  nlinarith [abs_nonneg (u - v)]

theorem pinsker_weightedResidual_mem {lam s u : ℝ} (hlam : 0 < lam) (hs : 1 ≤ s) (hu : 0 ≤ u) :
    weightedResidual lam (pinskerOrder s) (pinsker lam s) u ∈ Set.Icc (0 : ℝ) 2 := by
  have hρ := pinsker_order_bounds hs
  have hρ0 : 0 ≤ pinskerOrder s := by linarith [hρ.1]
  by_cases huc : u ≤ Real.log 2
  · rw [pinsker_weightedResidual_low hlam huc]
    have hru : pinskerOrder s * u ≤ Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_left huc hρ0
      have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith [hρ.2.1]
    exact ⟨(Real.exp_pos _).le, by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hru⟩
  · rw [pinsker_weightedResidual_high hlam (le_of_not_ge huc)]
    have h := pinskerHigh_bounds hρ0 hρ.2.1 hρ.2.2 (le_of_not_ge huc)
    exact ⟨h.1.le, h.2⟩

/-- The exact Pinsker profile satisfies the original contract uniformly in both
regularization and spectral upper bound; `s ≥ 1` is the manuscript's range. -/
theorem pinsker_contract {lam M s : ℝ} (hlam : 0 < lam) (hs : 1 ≤ s) :
    Contract lam M (pinskerOrder s) (4 * (1 + s / 2)) (pinsker lam s) := by
  have hρ := pinsker_order_bounds hs
  have hρ0 : 0 ≤ pinskerOrder s := by linarith [hρ.1]
  have hr : 0 ≤ s / 2 := by linarith
  have hC0 : 0 ≤ 4 * (1 + s / 2) := by positivity
  have hlowC : 2 * pinskerOrder s ≤ 4 * (1 + s / 2) := by linarith [hρ.2.2]
  have hhighC : 4 * (s / 2) ≤ 4 * (1 + s / 2) := by linarith
  constructor
  · linarith [hρ.1]
  · intro u hu
    have hP := pinsker_weightedResidual_mem hlam hs hu.1
    have hF := pinsker_inverse_size (t := spectralCoordinate lam u) hlam (by linarith : 0 ≤ s)
    rw [abs_of_nonneg hP.1]
    change |(spectralCoordinate lam u + lam) * pinsker lam s (spectralCoordinate lam u)| +
      weightedResidual lam (pinskerOrder s) (pinsker lam s) u ≤ _
    linarith [hP.2]
  · intro u hu v hv
    have hsameLow : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ Real.log 2 → b ≤ Real.log 2 →
        |weightedResidual lam (pinskerOrder s) (pinsker lam s) a -
          weightedResidual lam (pinskerOrder s) (pinsker lam s) b| ≤
          (4 * (1 + s / 2)) * |a - b| := by
      intro a b ha hb hac hbc
      rw [pinsker_weightedResidual_low hlam hac, pinsker_weightedResidual_low hlam hbc]
      exact (pinsker_low_lipschitz hρ0 hρ.2.1 ⟨ha, hac⟩ ⟨hb, hbc⟩).trans
        (mul_le_mul_of_nonneg_right hlowC (abs_nonneg _))
    have hsameHigh : ∀ a b : ℝ, Real.log 2 ≤ a → Real.log 2 ≤ b →
        |weightedResidual lam (pinskerOrder s) (pinsker lam s) a -
          weightedResidual lam (pinskerOrder s) (pinsker lam s) b| ≤
          (4 * (1 + s / 2)) * |a - b| := by
      intro a b ha hb
      rw [pinsker_weightedResidual_high hlam ha, pinsker_weightedResidual_high hlam hb]
      exact (pinskerHigh_lipschitz hρ0 hρ.2.1 hρ.2.2 ha hb).trans
        (mul_le_mul_of_nonneg_right hhighC (abs_nonneg _))
    have hcross : ∀ a b : ℝ, 0 ≤ a → a ≤ Real.log 2 → Real.log 2 ≤ b →
        |weightedResidual lam (pinskerOrder s) (pinsker lam s) a -
          weightedResidual lam (pinskerOrder s) (pinsker lam s) b| ≤
          (4 * (1 + s / 2)) * |a - b| := by
      intro a b ha hac hbc
      have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      calc
        _ ≤ |weightedResidual lam (pinskerOrder s) (pinsker lam s) a -
              weightedResidual lam (pinskerOrder s) (pinsker lam s) (Real.log 2)| +
            |weightedResidual lam (pinskerOrder s) (pinsker lam s) (Real.log 2) -
              weightedResidual lam (pinskerOrder s) (pinsker lam s) b| := abs_sub_le _ _ _
        _ ≤ (4 * (1 + s / 2)) * |a - Real.log 2| +
            (4 * (1 + s / 2)) * |Real.log 2 - b| :=
          add_le_add (hsameLow a _ ha hc hac le_rfl) (hsameHigh _ b le_rfl hbc)
        _ = (4 * (1 + s / 2)) * |a - b| := by
          rw [abs_of_nonpos (sub_nonpos.mpr hac), abs_of_nonpos (sub_nonpos.mpr hbc),
            abs_of_nonpos (sub_nonpos.mpr (hac.trans hbc))]
          ring
    rcases le_total u (Real.log 2) with huc | hcu
    · rcases le_total v (Real.log 2) with hvc | hcv
      · exact hsameLow u v hu.1 hv.1 huc hvc
      · exact hcross u v hu.1 huc hcv
    · rcases le_total v (Real.log 2) with hvc | hcv
      · simpa only [abs_sub_comm] using hcross v u hv.1 hvc hcu
      · exact hsameHigh u v hcu hcv

end
end KernelSeq.ResidualFilter
