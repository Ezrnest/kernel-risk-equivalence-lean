import KernelSeq.ResidualFilter
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# An explicit auxiliary cutoff filter

This module constructs the auxiliary residual filter using a piecewise linear
Lipschitz cutoff. Smoothness of the cutoff itself is not needed for the
stated downstream Lipschitz/DOI arguments. This file proves cutoff geometry,
Borel admissibility, inverse size, uniform sum size and residual Lipschitz
regularity. The auxiliary residual contract is proved from those estimates.
The inverse-profile Lipschitz estimate is the separate remaining conclusion.
-/

namespace KernelSeq.ResidualFilter

noncomputable section

/-- A fixed cutoff, zero through `1/3` and one from `2/3` onward. -/
def cutoff (s : ℝ) : ℝ := max 0 (min 1 (3 * s - 1))

theorem cutoff_mem (s : ℝ) : cutoff s ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem cutoff_eq_zero {s : ℝ} (hs : s ≤ 1 / 3) : cutoff s = 0 := by
  unfold cutoff
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)

theorem cutoff_eq_one {s : ℝ} (hs : 2 / 3 ≤ s) : cutoff s = 1 := by
  unfold cutoff
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem cutoff_abs_sub_le (s t : ℝ) : |cutoff s - cutoff t| ≤ 3 * |s - t| := by
  have hmax := abs_max_sub_max_le_max (0 : ℝ) (min 1 (3 * s - 1)) 0 (min 1 (3 * t - 1))
  have hmin := abs_min_sub_min_le_max (1 : ℝ) (3 * s - 1) 1 (3 * t - 1)
  rw [sub_self, abs_zero,
    max_eq_right (abs_nonneg (min 1 (3 * s - 1) - min 1 (3 * t - 1)))] at hmax
  rw [sub_self, abs_zero,
    max_eq_right (abs_nonneg ((3 * s - 1) - (3 * t - 1)))] at hmin
  calc
    _ ≤ |min 1 (3 * s - 1) - min 1 (3 * t - 1)| := hmax
    _ ≤ |(3 * s - 1) - (3 * t - 1)| := hmin
    _ = 3 * |s - t| := by
      rw [show (3 * s - 1) - (3 * t - 1) = 3 * (s - t) by ring, abs_mul]
      norm_num

theorem continuous_cutoff : Continuous cutoff := by
  unfold cutoff
  fun_prop

/-- The cutoff-modified inverse filter. -/
def auxiliaryFilter (lam τ : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  cutoff (t / (lam * τ)) * φ t

/-- Exact shrinkage factorization, valid without commutativity assumptions on operators
because this theorem is purely scalar. -/
theorem auxiliary_shrinkage (lam τ : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    shrinkage (auxiliaryFilter lam τ φ) t = cutoff (t / (lam * τ)) * shrinkage φ t := by
  unfold shrinkage auxiliaryFilter
  ring

/-- The residual perturbation is a cutoff times the original shrinkage. -/
theorem auxiliary_residual (lam τ : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    residual (auxiliaryFilter lam τ φ) t =
      residual φ t + (1 - cutoff (t / (lam * τ))) * shrinkage φ t := by
  unfold residual
  rw [auxiliary_shrinkage]
  ring

theorem auxiliary_eq_zero {lam τ t : ℝ} (hlam : 0 < lam) (hτ : 0 < τ)
    (φ : ℝ → ℝ) (ht : t ≤ lam * τ / 3) : auxiliaryFilter lam τ φ t = 0 := by
  have hs : t / (lam * τ) ≤ 1 / 3 :=
    (div_le_iff₀ (mul_pos hlam hτ)).2 (by linarith)
  simp only [auxiliaryFilter, cutoff_eq_zero hs, zero_mul]

theorem auxiliary_eq_original {lam τ t : ℝ} (hlam : 0 < lam) (hτ : 0 < τ)
    (φ : ℝ → ℝ) (ht : 2 * lam * τ / 3 ≤ t) : auxiliaryFilter lam τ φ t = φ t := by
  have hs : 2 / 3 ≤ t / (lam * τ) :=
    (le_div_iff₀ (mul_pos hlam hτ)).2 (by linarith)
  simp only [auxiliaryFilter, cutoff_eq_one hs, one_mul]

/-- The cutoff preserves the preliminary spectral algorithm assumptions. -/
theorem SpectralFilter.auxiliary {M lam τ : ℝ} {φ : ℝ → ℝ}
    (h : SpectralFilter M φ) : SpectralFilter M (auxiliaryFilter lam τ φ) := by
  constructor
  · have hc : Continuous (fun t : Set.Icc (0 : ℝ) M => cutoff ((t : ℝ) / (lam * τ))) :=
      continuous_cutoff.comp (continuous_subtype_val.div_const _)
    exact hc.measurable.mul h.measurable
  · intro t ht
    exact mul_nonneg (cutoff_mem _).1 (h.nonneg t ht)
  · intro t ht
    rw [auxiliary_shrinkage]
    have hc := cutoff_mem (t / (lam * τ))
    have hq := h.shrinkage_mem t ht
    constructor
    · exact mul_nonneg hc.1 hq.1
    · exact (mul_le_mul hc.2 hq.2 hq.1 (by norm_num)).trans_eq (by norm_num)

/-- The regularized inverse size does not increase after cutting off the origin. -/
theorem Contract.auxiliary_inverse_size {lam M ρ A τ : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |(t + lam) * auxiliaryFilter lam τ φ t| ≤ A := by
  have hc := cutoff_mem (t / (lam * τ))
  have hid : (t + lam) * auxiliaryFilter lam τ φ t =
      cutoff (t / (lam * τ)) * ((t + lam) * φ t) := by
    unfold auxiliaryFilter
    ring
  rw [hid, abs_mul, abs_of_nonneg hc.1]
  exact (mul_le_mul_of_nonneg_right hc.2 (abs_nonneg _)).trans
    (by simpa only [one_mul] using (h.spectral_size hlam ht).1)

/-- Exact weighted-residual identity used to prove auxiliary residual regularity. -/
theorem auxiliary_weightedResidual (lam ρ τ : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    weightedResidual lam ρ (auxiliaryFilter lam τ φ) u =
      weightedResidual lam ρ φ u +
      (1 - cutoff (spectralCoordinate lam u / (lam * τ))) *
        ((spectralCoordinate lam u + lam) / lam) ^ ρ *
        shrinkage φ (spectralCoordinate lam u) := by
  unfold weightedResidual
  rw [auxiliary_residual]
  ring

/-- The transformed inverse is multiplied by the same cutoff. -/
theorem auxiliary_inverseProfile (lam τ : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    inverseProfile lam (auxiliaryFilter lam τ φ) u =
      cutoff (spectralCoordinate lam u / (lam * τ)) * inverseProfile lam φ u := by
  unfold inverseProfile auxiliaryFilter
  ring

/-- A convex-combination form of the exact weighted-residual identity. -/
theorem auxiliary_weightedResidual_convex (lam ρ τ : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    weightedResidual lam ρ (auxiliaryFilter lam τ φ) u =
      cutoff (spectralCoordinate lam u / (lam * τ)) * weightedResidual lam ρ φ u +
      (1 - cutoff (spectralCoordinate lam u / (lam * τ))) *
        ((spectralCoordinate lam u + lam) / lam) ^ ρ := by
  unfold weightedResidual residual
  rw [auxiliary_shrinkage]
  ring

/-- The auxiliary transformed SUM-size bound is uniform in the cutoff scale.
This proves the size half of the auxiliary residual contract with an explicit
constant. The residual and inverse Lipschitz estimates remain separate. -/
theorem Contract.auxiliary_sum_size {lam M ρ A τ : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) (hτ : 0 < τ) (hτone : τ ≤ 1)
    {u : ℝ} (hu : u ∈ logDomain lam M) :
    |inverseProfile lam (auxiliaryFilter lam τ φ) u| +
      |weightedResidual lam ρ (auxiliaryFilter lam τ φ) u| ≤ A + (5 / 3 : ℝ) ^ ρ := by
  let t := spectralCoordinate lam u
  have ht : 0 ≤ t := spectralCoordinate_nonneg hlam.le hu.1
  by_cases hhigh : 2 * lam * τ / 3 ≤ t
  · have hc : cutoff (t / (lam * τ)) = 1 :=
      cutoff_eq_one ((le_div_iff₀ (mul_pos hlam hτ)).2 (by linarith))
    rw [auxiliary_inverseProfile, auxiliary_weightedResidual_convex]
    change |cutoff (t / (lam * τ)) * inverseProfile lam φ u| +
      |cutoff (t / (lam * τ)) * weightedResidual lam ρ φ u +
        (1 - cutoff (t / (lam * τ))) * ((t + lam) / lam) ^ ρ| ≤ _
    rw [hc]
    simp only [one_mul, sub_self, zero_mul, add_zero]
    exact (h.size u hu).trans (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  · have hlτ : lam * τ ≤ lam := by nlinarith
    have hratio : (t + lam) / lam ≤ 5 / 3 := (div_le_iff₀ hlam).2 (by linarith)
    have hrnonneg : 0 ≤ (t + lam) / lam := div_nonneg (add_nonneg ht hlam.le) hlam.le
    have hrpow := Real.rpow_le_rpow hrnonneg hratio h.rho_pos.le
    have hrpow0 := Real.rpow_nonneg hrnonneg ρ
    have hc := cutoff_mem (t / (lam * τ))
    have hs := h.size u hu
    have hA : 0 ≤ A := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hs
    have hscaled := mul_le_mul_of_nonneg_left hs hc.1
    have hscaledA := mul_le_mul_of_nonneg_right hc.2 hA
    have hscaledR := mul_le_mul (show 1 - cutoff (t / (lam * τ)) ≤ 1 by linarith [hc.1])
      hrpow hrpow0 (by norm_num : (0 : ℝ) ≤ 1)
    rw [auxiliary_inverseProfile, auxiliary_weightedResidual_convex]
    change |cutoff (t / (lam * τ)) * inverseProfile lam φ u| +
      |cutoff (t / (lam * τ)) * weightedResidual lam ρ φ u +
        (1 - cutoff (t / (lam * τ))) * ((t + lam) / lam) ^ ρ| ≤ _
    calc
      _ ≤ cutoff (t / (lam * τ)) * |inverseProfile lam φ u| +
          (cutoff (t / (lam * τ)) * |weightedResidual lam ρ φ u| +
            (1 - cutoff (t / (lam * τ))) * ((t + lam) / lam) ^ ρ) := by
        rw [abs_mul, abs_of_nonneg hc.1]
        apply add_le_add le_rfl
        have htri := abs_add_le
          (cutoff (t / (lam * τ)) * weightedResidual lam ρ φ u)
          ((1 - cutoff (t / (lam * τ))) * ((t + lam) / lam) ^ ρ)
        simpa only [abs_mul, abs_of_nonneg hc.1,
          abs_of_nonneg (sub_nonneg.mpr hc.2), abs_of_nonneg hrpow0] using htri
      _ ≤ _ := by nlinarith

/-- Exponential is Lipschitz on every interval bounded above. -/
theorem abs_exp_sub_exp_le_upper {u v b : ℝ} (hu : u ≤ b) (hv : v ≤ b) :
    |Real.exp u - Real.exp v| ≤ Real.exp b * |u - v| := by
  have h := abs_exp_sub_exp_le (sub_nonpos.mpr hu) (sub_nonpos.mpr hv)
  have heu : Real.exp u = Real.exp b * Real.exp (u - b) := by
    rw [← Real.exp_add]; congr 1; ring
  have hev : Real.exp v = Real.exp b * Real.exp (v - b) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    _ = Real.exp b * |Real.exp (u - b) - Real.exp (v - b)| := by
      rw [heu, hev, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos b)]
    _ ≤ Real.exp b * |(u - b) - (v - b)| :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by congr 2; ring

/-- Cutoff as a function of logarithmic spectral coordinates. -/
def logCutoff (τ u : ℝ) : ℝ := cutoff ((Real.exp u - 1) / τ)

theorem cutoff_spectralCoordinate {lam τ u : ℝ} (hlam : lam ≠ 0) :
    cutoff (spectralCoordinate lam u / (lam * τ)) = logCutoff τ u := by
  unfold spectralCoordinate logCutoff
  congr 1
  field_simp

/-- The upper edge of the cutoff transition. -/
def cutoffUpper (τ : ℝ) : ℝ := Real.log (1 + 2 * τ / 3)

/-- Above the transition edge the logarithmic cutoff is one. -/
theorem logCutoff_eq_one {τ u : ℝ} (hτ : 0 < τ) (hu : cutoffUpper τ ≤ u) :
    logCutoff τ u = 1 := by
  apply cutoff_eq_one
  apply (le_div_iff₀ hτ).2
  have he := Real.exp_le_exp.mpr hu
  rw [cutoffUpper, Real.exp_log (by positivity : 0 < 1 + 2 * τ / 3)] at he
  linarith

/-- Clipping the log coordinate at the end of the transition leaves the cutoff unchanged. -/
theorem logCutoff_clip {τ : ℝ} (hτ : 0 < τ) (u : ℝ) :
    logCutoff τ u = logCutoff τ (min u (cutoffUpper τ)) := by
  by_cases hu : u ≤ cutoffUpper τ
  · rw [min_eq_left hu]
  · rw [min_eq_right (le_of_not_ge hu), logCutoff_eq_one hτ (le_of_not_ge hu),
      logCutoff_eq_one hτ le_rfl]

/-- A uniform `5/τ` Lipschitz estimate for the cutoff in log coordinates. -/
theorem logCutoff_lipschitz {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (u v : ℝ) :
    |logCutoff τ u - logCutoff τ v| ≤ (5 / τ) * |u - v| := by
  let b := cutoffUpper τ
  have he : Real.exp b = 1 + 2 * τ / 3 :=
    Real.exp_log (by positivity : 0 < 1 + 2 * τ / 3)
  have hdist : |min u b - min v b| ≤ |u - v| := by
    have hh := abs_min_sub_min_le_max u b v b
    simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (u - v))] using hh
  have hexp := abs_exp_sub_exp_le_upper (min_le_right u b) (min_le_right v b)
  have hcoeff : 3 / τ * Real.exp b ≤ 5 / τ := by
    rw [he]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) hτ.le
  rw [logCutoff_clip hτ u, logCutoff_clip hτ v]
  calc
    _ ≤ 3 * |(Real.exp (min u b) - 1) / τ - (Real.exp (min v b) - 1) / τ| :=
      cutoff_abs_sub_le _ _
    _ = (3 / τ) * |Real.exp (min u b) - Real.exp (min v b)| := by
      rw [← sub_div, abs_div, abs_of_pos hτ]
      have hh : (Real.exp (min u b) - 1) - (Real.exp (min v b) - 1) =
          Real.exp (min u b) - Real.exp (min v b) := by ring
      rw [hh]; ring
    _ ≤ (3 / τ) * (Real.exp b * |min u b - min v b|) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (3 / τ) * (Real.exp b * |u - v|) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdist (Real.exp_pos _).le) (by positivity)
    _ ≤ (5 / τ) * |u - v| := by
      nlinarith [mul_le_mul_of_nonneg_right hcoeff (abs_nonneg (u - v))]

theorem cutoffUpper_nonneg {τ : ℝ} (hτ : 0 < τ) : 0 ≤ cutoffUpper τ := by
  apply Real.log_nonneg
  linarith

theorem cutoffUpper_le {τ : ℝ} (hτ : 0 < τ) : cutoffUpper τ ≤ 2 * τ / 3 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 2 * τ / 3)
  dsimp [cutoffUpper]
  linarith

/-- A Lipschitz function vanishing at the origin remains uniformly Lipschitz
after truncating it to the cutoff transition; the small support cancels `1/τ`. -/
theorem localized_product_lipschitz {τ J C : ℝ} (H : ℝ → ℝ)
    (hτ : 0 < τ) (hτone : τ ≤ 1) (hC : 0 ≤ C) (hH0 : H 0 = 0)
    (hH : ∀ u ∈ Set.Icc (0 : ℝ) J, ∀ v ∈ Set.Icc (0 : ℝ) J,
      u ≤ cutoffUpper τ → v ≤ cutoffUpper τ → |H u - H v| ≤ C * |u - v|)
    {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) J) (hv : v ∈ Set.Icc (0 : ℝ) J) :
    |(1 - logCutoff τ u) * H u - (1 - logCutoff τ v) * H v| ≤
      (5 * C) * |u - v| := by
  let b := cutoffUpper τ
  have hb0 : 0 ≤ b := cutoffUpper_nonneg hτ
  have hbτ : b ≤ 2 * τ / 3 := cutoffUpper_le hτ
  have hlow : ∀ u ∈ Set.Icc (0 : ℝ) J, ∀ v ∈ Set.Icc (0 : ℝ) J,
      u ≤ b → v ≤ b →
      |(1 - logCutoff τ u) * H u - (1 - logCutoff τ v) * H v| ≤
        (5 * C) * |u - v| := by
    intro u hu v hv hub hvb
    have h0J : (0 : ℝ) ∈ Set.Icc (0 : ℝ) J := ⟨le_rfl, hu.1.trans hu.2⟩
    have hHv := hH v hv 0 h0J hvb hb0
    simp only [hH0, sub_zero, abs_of_nonneg hv.1] at hHv
    have hHvτ : |H v| ≤ C * (2 * τ / 3) :=
      hHv.trans (mul_le_mul_of_nonneg_left (hvb.trans hbτ) hC)
    have hdiff := hH u hu v hv hub hvb
    have hcut := logCutoff_lipschitz hτ hτone u v
    have hcu := cutoff_mem ((Real.exp u - 1) / τ)
    have hcv := cutoff_mem ((Real.exp v - 1) / τ)
    change logCutoff τ u ∈ Set.Icc (0 : ℝ) 1 at hcu
    change logCutoff τ v ∈ Set.Icc (0 : ℝ) 1 at hcv
    have hid : (1 - logCutoff τ u) * H u - (1 - logCutoff τ v) * H v =
        (1 - logCutoff τ u) * (H u - H v) +
          (logCutoff τ v - logCutoff τ u) * H v := by ring
    rw [hid]
    calc
      _ ≤ |(1 - logCutoff τ u) * (H u - H v)| +
          |(logCutoff τ v - logCutoff τ u) * H v| := abs_add_le _ _
      _ = (1 - logCutoff τ u) * |H u - H v| +
          |logCutoff τ u - logCutoff τ v| * |H v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hcu.2),
          abs_sub_comm (logCutoff τ v) (logCutoff τ u)]
      _ ≤ 1 * (C * |u - v|) + ((5 / τ) * |u - v|) * (C * (2 * τ / 3)) := by
        apply add_le_add
        · exact mul_le_mul (by linarith [hcu.1]) hdiff (abs_nonneg _) (by norm_num)
        · exact mul_le_mul hcut hHvτ (abs_nonneg _) (by positivity)
      _ = (13 / 3 : ℝ) * C * |u - v| := by field_simp; ring
      _ ≤ _ := by nlinarith [mul_nonneg hC (abs_nonneg (u - v))]
  have hordered : ∀ u ∈ Set.Icc (0 : ℝ) J, ∀ v ∈ Set.Icc (0 : ℝ) J,
      u ≤ v →
      |(1 - logCutoff τ u) * H u - (1 - logCutoff τ v) * H v| ≤
        (5 * C) * |u - v| := by
    intro u hu v hv huv
    by_cases hbu : b ≤ u
    · rw [logCutoff_eq_one hτ hbu, logCutoff_eq_one hτ (hbu.trans huv)]
      simp only [sub_self, zero_mul, abs_zero]
      positivity
    · by_cases hvb : v ≤ b
      · exact hlow u hu v hv (le_of_not_ge hbu) hvb
      · have hub : u ≤ b := le_of_not_ge hbu
        have hbv : b ≤ v := le_of_not_ge hvb
        have hbJ : b ∈ Set.Icc (0 : ℝ) J := ⟨hb0, hbv.trans hv.2⟩
        have hh := hlow u hu b hbJ hub le_rfl
        rw [logCutoff_eq_one hτ le_rfl] at hh
        rw [logCutoff_eq_one hτ hbv]
        simp only [sub_self, zero_mul, sub_zero] at hh ⊢
        apply hh.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [abs_of_nonpos (sub_nonpos.mpr hub), abs_of_nonpos (sub_nonpos.mpr huv)]
        linarith
  rcases le_total u v with huv | hvu
  · exact hordered u hu v hv huv
  · simpa only [abs_sub_comm] using hordered v hv u hu hvu

/-- The weighted residual equals one at the origin for every inverse filter. -/
theorem weightedResidual_zero {lam : ℝ} (hlam : lam ≠ 0)
    (ρ : ℝ) (φ : ℝ → ℝ) : weightedResidual lam ρ φ 0 = 1 := by
  simp [weightedResidual, spectralCoordinate, residual, shrinkage, hlam]

/-- Exact exponential form of the auxiliary residual correction. -/
theorem auxiliary_weightedResidual_correction {lam : ℝ} (hlam : 0 < lam)
    (ρ τ : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    weightedResidual lam ρ (auxiliaryFilter lam τ φ) u =
      weightedResidual lam ρ φ u + (1 - logCutoff τ u) *
        (Real.exp (ρ * u) - weightedResidual lam ρ φ u) := by
  rw [auxiliary_weightedResidual_convex, cutoff_spectralCoordinate hlam.ne']
  have hr : ((spectralCoordinate lam u + lam) / lam) ^ ρ = Real.exp (ρ * u) := by
    have hratio : (spectralCoordinate lam u + lam) / lam = Real.exp u := by
      unfold spectralCoordinate
      field_simp
      ring
    rw [hratio, ← Real.exp_mul]
    congr 1; ring
  rw [hr]
  ring

/-- Uniform Lipschitz regularity of the auxiliary weighted residual.
The displayed constant depends only on the original residual constants. -/
theorem Contract.auxiliary_residual_lipschitz {lam M ρ A τ : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) (hτ : 0 < τ) (hτone : τ ≤ 1)
    {u v : ℝ} (hu : u ∈ logDomain lam M) (hv : v ∈ logDomain lam M) :
    |weightedResidual lam ρ (auxiliaryFilter lam τ φ) u -
      weightedResidual lam ρ (auxiliaryFilter lam τ φ) v| ≤
      (A + 5 * (ρ * Real.exp ρ + A)) * |u - v| := by
  let H : ℝ → ℝ := fun z => Real.exp (ρ * z) - weightedResidual lam ρ φ z
  let C : ℝ := ρ * Real.exp ρ + A
  have hs := h.size u hu
  have hA : 0 ≤ A := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hs
  have hC : 0 ≤ C := add_nonneg (mul_nonneg h.rho_pos.le (Real.exp_pos _).le) hA
  have hH0 : H 0 = 0 := by simp [H, weightedResidual_zero hlam.ne']
  have hH : ∀ a ∈ logDomain lam M, ∀ b ∈ logDomain lam M,
      a ≤ cutoffUpper τ → b ≤ cutoffUpper τ → |H a - H b| ≤ C * |a - b| := by
    intro a ha b hb hab hbb
    have ha1 : a ≤ 1 := (hab.trans (cutoffUpper_le hτ)).trans (by linarith)
    have hb1 : b ≤ 1 := (hbb.trans (cutoffUpper_le hτ)).trans (by linarith)
    have he := abs_exp_sub_exp_le_upper
      (show ρ * a ≤ ρ by nlinarith [h.rho_pos])
      (show ρ * b ≤ ρ by nlinarith [h.rho_pos])
    have hexp : |Real.exp (ρ * a) - Real.exp (ρ * b)| ≤
        (ρ * Real.exp ρ) * |a - b| := by
      have hh : |ρ * a - ρ * b| = ρ * |a - b| := by
        rw [← mul_sub, abs_mul, abs_of_pos h.rho_pos]
      rw [hh] at he
      nlinarith
    have hp := h.residual_lipschitz a ha b hb
    calc
      _ = |(Real.exp (ρ * a) - Real.exp (ρ * b)) -
          (weightedResidual lam ρ φ a - weightedResidual lam ρ φ b)| := by
        dsimp [H]; congr 1; ring
      _ ≤ |Real.exp (ρ * a) - Real.exp (ρ * b)| +
          |weightedResidual lam ρ φ a - weightedResidual lam ρ φ b| := abs_sub _ _
      _ ≤ C * |a - b| := by dsimp [C]; nlinarith
  have hcor := localized_product_lipschitz H hτ hτone hC hH0 hH hu hv
  rw [auxiliary_weightedResidual_correction hlam, auxiliary_weightedResidual_correction hlam]
  have hid :
      (weightedResidual lam ρ φ u + (1 - logCutoff τ u) * H u) -
      (weightedResidual lam ρ φ v + (1 - logCutoff τ v) * H v) =
      (weightedResidual lam ρ φ u - weightedResidual lam ρ φ v) +
      ((1 - logCutoff τ u) * H u - (1 - logCutoff τ v) * H v) := by ring
  change |(weightedResidual lam ρ φ u + (1 - logCutoff τ u) * H u) -
      (weightedResidual lam ρ φ v + (1 - logCutoff τ v) * H v)| ≤ _
  rw [hid]
  exact (abs_add_le _ _).trans (by nlinarith [h.residual_lipschitz u hu v hv])

/-- An explicit residual-regularity constant independent of both regularization
and cutoff scale. The inverse-profile Lipschitz constant is a separate bound. -/
def auxiliaryConstant (ρ A : ℝ) : ℝ :=
  max (A + (5 / 3 : ℝ) ^ ρ) (A + 5 * (ρ * Real.exp ρ + A))

/-- The auxiliary family satisfies the original residual contract with the
same residual order and a uniform enlarged constant. -/
theorem Contract.auxiliary_contract {lam M ρ A τ : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) (hτ : 0 < τ) (hτone : τ ≤ 1) :
    Contract lam M ρ (auxiliaryConstant ρ A) (auxiliaryFilter lam τ φ) := by
  refine ⟨h.rho_pos, ?_, ?_⟩
  · intro u hu
    exact (h.auxiliary_sum_size hlam hτ hτone hu).trans (le_max_left _ _)
  · intro u hu v hv
    exact (h.auxiliary_residual_lipschitz hlam hτ hτone hu hv).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

end
end KernelSeq.ResidualFilter
