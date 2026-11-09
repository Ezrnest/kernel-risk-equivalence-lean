import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scale-regular residual filters

Scalar profiles, the inverse size bound, and the weighted-residual Lipschitz
condition. `M` is the spectral upper bound
(the manuscript uses `κ²`). No continuity or Lipschitz assumption on the inverse
profile is imposed. Spectral-filter admissibility is kept separate from residual
regularity, as in the manuscript.
-/

namespace KernelSeq.ResidualFilter

noncomputable section

/-- Fraction retained by the estimator. -/
def shrinkage (φ : ℝ → ℝ) (t : ℝ) : ℝ := t * φ t
/-- Residual fraction. -/
def residual (φ : ℝ → ℝ) (t : ℝ) : ℝ := 1 - shrinkage φ t
/-- Original spectrum in logarithmic coordinates. -/
def spectralCoordinate (lam u : ℝ) : ℝ := lam * (Real.exp u - 1)
/-- Interval `J_lam` for the logarithmic coordinate. -/
def logDomain (lam M : ℝ) : Set ℝ := Set.Icc 0 (Real.log (1 + M / lam))
/-- Regularized inverse in logarithmic coordinates. -/
def inverseProfile (lam : ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  (spectralCoordinate lam u + lam) * φ (spectralCoordinate lam u)
/-- Weighted residual in logarithmic coordinates. -/
def weightedResidual (lam ρ : ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ((spectralCoordinate lam u + lam) / lam) ^ ρ * residual φ (spectralCoordinate lam u)

/-- Borel measurability and shrinkage range on the actual spectral interval. -/
structure SpectralFilter (M : ℝ) (φ : ℝ → ℝ) : Prop where
  measurable : Measurable (fun t : Set.Icc (0 : ℝ) M => φ t)
  nonneg : ∀ t ∈ Set.Icc (0 : ℝ) M, 0 ≤ φ t
  shrinkage_mem : ∀ t ∈ Set.Icc (0 : ℝ) M, shrinkage φ t ∈ Set.Icc (0 : ℝ) 1

/-- Precisely the sum-size bound and Lipschitz bound on the weighted residual.
The same `ρ` and `A` are to be used along a regularization family. -/
structure Contract (lam M ρ A : ℝ) (φ : ℝ → ℝ) : Prop where
  rho_pos : 0 < ρ
  size : ∀ u ∈ logDomain lam M, |inverseProfile lam φ u| + |weightedResidual lam ρ φ u| ≤ A
  residual_lipschitz : ∀ u ∈ logDomain lam M, ∀ v ∈ logDomain lam M,
    |weightedResidual lam ρ φ u - weightedResidual lam ρ φ v| ≤ A * |u - v|

/-- Changing to the logarithmic coordinate covers every admissible eigenvalue. -/
theorem log_coordinate_mem {lam M t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M) :
    Real.log (1 + t / lam) ∈ logDomain lam M := by
  have htdiv : 0 ≤ t / lam := div_nonneg ht.1 hlam.le
  have hpos : 0 < 1 + t / lam := by linarith
  constructor
  · exact Real.log_nonneg (by linarith)
  · exact Real.log_le_log hpos (add_le_add le_rfl (div_le_div_of_nonneg_right ht.2 hlam.le))

theorem spectralCoordinate_log {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    spectralCoordinate lam (Real.log (1 + t / lam)) = t := by
  rw [spectralCoordinate, Real.exp_log (by positivity : 0 < 1 + t / lam)]
  field_simp
  ring

/-- Nonnegative logarithmic coordinates produce nonnegative eigenvalues. -/
theorem spectralCoordinate_nonneg {lam u : ℝ} (hlam : 0 ≤ lam) (hu : 0 ≤ u) :
    0 ≤ spectralCoordinate lam u := by
  exact mul_nonneg hlam (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hu))

/-- The logarithmic interval also maps into the original spectral interval. -/
theorem spectralCoordinate_mem {lam M u : ℝ} (hlam : 0 < lam) (hM : 0 ≤ M)
    (hu : u ∈ logDomain lam M) : spectralCoordinate lam u ∈ Set.Icc (0 : ℝ) M := by
  refine ⟨spectralCoordinate_nonneg hlam.le hu.1, ?_⟩
  have h := Real.exp_le_exp.mpr hu.2
  rw [Real.exp_log (by positivity : 0 < 1 + M / lam)] at h
  have hm := mul_le_mul_of_nonneg_left h hlam.le
  have hcancel : lam * (M / lam) = M := by field_simp
  unfold spectralCoordinate
  nlinarith

/-- Weighted residual and inverse-size bounds transported to the original spectrum. -/
theorem Contract.spectral_size {lam M ρ A : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |(t + lam) * φ t| ≤ A ∧ ((t + lam) / lam) ^ ρ * |residual φ t| ≤ A := by
  have hs := h.size _ (log_coordinate_mem hlam ht)
  simp only [inverseProfile, weightedResidual, spectralCoordinate_log hlam ht.1] at hs
  have hp : 0 ≤ ((t + lam) / lam) ^ ρ :=
    Real.rpow_nonneg (div_nonneg (add_nonneg ht.1 hlam.le) hlam.le) _
  constructor
  · exact le_trans (le_add_of_nonneg_right (abs_nonneg _)) hs
  · have hP : |((t + lam) / lam) ^ ρ * residual φ t| ≤ A :=
      le_trans (le_add_of_nonneg_left (abs_nonneg _)) hs
    simpa only [abs_mul, abs_of_nonneg hp] using hP

/-- The manuscript's regularized inverse bound. -/
theorem Contract.inverse_size {lam M ρ A : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) M) :
    (t + lam) * φ t ≤ A :=
  (le_abs_self _).trans (h.spectral_size hlam ht).1

/-- Residuals are nonnegative for admissible spectral filters. -/
theorem SpectralFilter.residual_nonneg {M : ℝ} {φ : ℝ → ℝ}
    (h : SpectralFilter M φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) M) :
    0 ≤ residual φ t := by
  exact sub_nonneg.mpr (h.shrinkage_mem t ht).2

/-- An admissible shrinkage in [0,1] has a residual in [0,1]. -/
theorem SpectralFilter.residual_mem {M : ℝ} {φ : ℝ → ℝ}
    (h : SpectralFilter M φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) M) :
    residual φ t ∈ Set.Icc (0 : ℝ) 1 := by
  have hq := h.shrinkage_mem t ht
  unfold residual
  constructor <;> linarith [hq.1, hq.2]

/-- Residual decay in the original spectral coordinate. -/
theorem Contract.residual_size {lam M ρ A : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |residual φ t| ≤ A * (lam / (t + lam)) ^ ρ := by
  have hsize := (h.spectral_size hlam ht).2
  have hpow : 0 < ((t + lam) / lam) ^ ρ := Real.rpow_pos_of_pos (div_pos (add_pos_of_nonneg_of_pos ht.1 hlam) hlam) _
  have hid : (lam / (t + lam)) ^ ρ = (((t + lam) / lam) ^ ρ)⁻¹ := by
    rw [← Real.inv_rpow (div_nonneg (add_nonneg ht.1 hlam.le) hlam.le)]
    congr 1
    field_simp
  rw [hid, ← div_eq_mul_inv]
  exact (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hsize)

/-- Qualification at every order between zero and the residual order. -/
theorem Contract.qualification {lam M ρ A : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) {t τ : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) M) (hτ : 0 ≤ τ) (hτρ : τ ≤ ρ) :
    t ^ τ * |residual φ t| ≤ A * lam ^ τ := by
  have hR : 1 ≤ (t + lam) / lam := (le_div_iff₀ hlam).2 (by linarith [ht.1])
  have horder := Real.rpow_le_rpow_of_exponent_le hR hτρ
  have hsize : ((t + lam) / lam) ^ τ * |residual φ t| ≤ A :=
    (mul_le_mul_of_nonneg_right horder (abs_nonneg _)).trans (h.spectral_size hlam ht).2
  have htpow : t ^ τ ≤ (t + lam) ^ τ :=
    Real.rpow_le_rpow ht.1 (by linarith) hτ
  have hpoweq : lam ^ τ * (((t + lam) / lam) ^ τ) = (t + lam) ^ τ := by
    rw [Real.div_rpow (by linarith [ht.1]) hlam.le]
    field_simp
  calc
    t ^ τ * |residual φ t| ≤ (t + lam) ^ τ * |residual φ t| :=
      mul_le_mul_of_nonneg_right htpow (abs_nonneg _)
    _ = lam ^ τ * ((((t + lam) / lam) ^ τ) * |residual φ t|) := by rw [← hpoweq]; ring
    _ ≤ lam ^ τ * A := mul_le_mul_of_nonneg_left hsize (Real.rpow_nonneg hlam.le _)
    _ = A * lam ^ τ := by ring

/-- Kernel ridge regression inverse filter. -/
def ridge (lam t : ℝ) : ℝ := 1 / (t + lam)

theorem ridge_residual {lam t : ℝ} (hden : t + lam ≠ 0) :
    residual (ridge lam) t = lam / (t + lam) := by
  unfold residual shrinkage ridge
  field_simp
  ring

theorem ridge_inverseProfile {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    inverseProfile lam (ridge lam) u = 1 := by
  unfold inverseProfile ridge spectralCoordinate
  have hden : lam * (Real.exp u - 1) + lam ≠ 0 := by
    have he : 0 < lam * Real.exp u := mul_pos hlam (Real.exp_pos _)
    nlinarith
  exact mul_one_div_cancel hden

theorem ridge_weightedResidual {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    weightedResidual lam 1 (ridge lam) u = 1 := by
  have hden : spectralCoordinate lam u + lam ≠ 0 := by
    unfold spectralCoordinate
    have he : 0 < lam * Real.exp u := mul_pos hlam (Real.exp_pos _)
    nlinarith
  rw [weightedResidual, Real.rpow_one, ridge_residual hden]
  field_simp

/-- KRR satisfies the exact sum-size assumption with `ρ=1` and `A=2`.
The constant is independent of both lam and the spectral upper bound. -/
theorem ridge_contract {lam M : ℝ} (hlam : 0 < lam) : Contract lam M 1 2 (ridge lam) := by
  constructor
  · norm_num
  · intro u _
    rw [ridge_inverseProfile hlam, ridge_weightedResidual hlam]
    norm_num
  · intro u _ v _
    rw [ridge_weightedResidual hlam, ridge_weightedResidual hlam]
    simp only [sub_self, abs_zero]
    positivity

/-- KRR is an admissible Borel spectral filter on every nonnegative interval. -/
theorem ridge_spectralFilter {lam M : ℝ} (hlam : 0 < lam) : SpectralFilter M (ridge lam) := by
  constructor
  · apply Continuous.measurable
    apply continuous_const.div (continuous_subtype_val.add continuous_const)
    intro t
    exact ne_of_gt (add_pos_of_nonneg_of_pos t.property.1 hlam)
  · intro t ht
    exact one_div_nonneg.mpr (add_nonneg ht.1 hlam.le)
  · intro t ht
    unfold shrinkage ridge
    have hden : 0 < t + lam := add_pos_of_nonneg_of_pos ht.1 hlam
    constructor
    · exact mul_nonneg ht.1 (one_div_nonneg.mpr hden.le)
    · rw [mul_one_div]
      exact (div_le_one hden).2 (by linarith)

/-- Exponentials are 1-Lipschitz on the nonpositive half-line. -/
theorem abs_exp_sub_exp_le {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  suffices h : ∀ a b : ℝ, a ≤ 0 → b ≤ 0 → a ≤ b →
      Real.exp b - Real.exp a ≤ b - a by
    rcases le_total a b with hab | hba
    · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hab)),
        abs_of_nonpos (sub_nonpos.mpr hab)]
      simpa only [neg_sub] using h a b ha hb hab
    · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba)),
        abs_of_nonneg (sub_nonneg.mpr hba)]
      exact h b a hb ha hba
  intro a b ha hb hab
  have hexp := Real.exp_pos b
  have hbound := Real.exp_le_one_iff.mpr hb
  have hlinear := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a - b)) hexp.le
  have hmul : Real.exp b * Real.exp (a - b) = Real.exp a := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hmul] at hlinear
  nlinarith [mul_nonneg (sub_nonneg.mpr hbound) (sub_nonneg.mpr hab)]

/-- Exponential residual weight is uniformly Lipschitz on nonnegative coordinates. -/
theorem exp_neg_mul_lipschitz {ρ u v : ℝ} (hρ : 0 ≤ ρ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-ρ * u) - Real.exp (-ρ * v)| ≤ ρ * |u - v| := by
  have h := abs_exp_sub_exp_le (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) hu)
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) hv)
  calc
    _ ≤ |(-ρ) * u - (-ρ) * v| := h
    _ = ρ * |u - v| := by rw [← mul_sub, abs_mul, abs_neg, abs_of_nonneg hρ]

/-- In logarithmic coordinates the weighted residual uses an exponential weight. -/
theorem weightedResidual_eq_exp_mul {lam : ℝ} (hlam : 0 < lam)
    (ρ : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    weightedResidual lam ρ φ u = Real.exp (ρ * u) * residual φ (spectralCoordinate lam u) := by
  have hratio : (spectralCoordinate lam u + lam) / lam = Real.exp u := by
    unfold spectralCoordinate
    field_simp
    ring
  rw [weightedResidual, hratio, ← Real.exp_mul]
  congr 2
  ring

/-- The log-shrinkage profile is recovered from the weighted residual. -/
theorem shrinkage_eq_one_sub_exp_mul {lam : ℝ} (hlam : 0 < lam)
    (ρ : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    shrinkage φ (spectralCoordinate lam u) =
      1 - Real.exp (-ρ * u) * weightedResidual lam ρ φ u := by
  rw [weightedResidual_eq_exp_mul hlam]
  have hprod : Real.exp (-ρ * u) * Real.exp (ρ * u) = 1 := by
    rw [← Real.exp_add, show -ρ * u + ρ * u = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hprod]
  unfold residual
  ring

/-- The transformed shrinkage is Lipschitz with a constant uniform in lam.
Only weighted-residual regularity is used; inverse-profile continuity is unnecessary. -/
theorem Contract.shrinkage_lipschitz {lam M ρ A : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam)
    {u v : ℝ} (hu : u ∈ logDomain lam M) (hv : v ∈ logDomain lam M) :
    |shrinkage φ (spectralCoordinate lam u) - shrinkage φ (spectralCoordinate lam v)| ≤
      A * (1 + ρ) * |u - v| := by
  have hPv : |weightedResidual lam ρ φ v| ≤ A :=
    le_trans (le_add_of_nonneg_left (abs_nonneg _)) (h.size v hv)
  have hau : |Real.exp (-ρ * u)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h.rho_pos.le) hu.1)
  have hab := exp_neg_mul_lipschitz h.rho_pos.le hu.1 hv.1
  have hPdiff := h.residual_lipschitz u hu v hv
  rw [shrinkage_eq_one_sub_exp_mul hlam, shrinkage_eq_one_sub_exp_mul hlam]
  have heq :
      (1 - Real.exp (-ρ * u) * weightedResidual lam ρ φ u) -
      (1 - Real.exp (-ρ * v) * weightedResidual lam ρ φ v) =
      -(Real.exp (-ρ * u) * (weightedResidual lam ρ φ u - weightedResidual lam ρ φ v) +
        (Real.exp (-ρ * u) - Real.exp (-ρ * v)) * weightedResidual lam ρ φ v) := by ring
  rw [heq, abs_neg]
  calc
    _ ≤ |Real.exp (-ρ * u) * (weightedResidual lam ρ φ u - weightedResidual lam ρ φ v)| +
        |(Real.exp (-ρ * u) - Real.exp (-ρ * v)) * weightedResidual lam ρ φ v| := abs_add_le _ _
    _ = |Real.exp (-ρ * u)| * |weightedResidual lam ρ φ u - weightedResidual lam ρ φ v| +
        |Real.exp (-ρ * u) - Real.exp (-ρ * v)| * |weightedResidual lam ρ φ v| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (A * |u - v|) + (ρ * |u - v|) * A := by
      apply add_le_add
      · exact mul_le_mul hau hPdiff (abs_nonneg _) (by norm_num)
      · exact mul_le_mul hab hPv (abs_nonneg _) (mul_nonneg h.rho_pos.le (abs_nonneg _))
    _ = A * (1 + ρ) * |u - v| := by ring

end
end KernelSeq.ResidualFilter
