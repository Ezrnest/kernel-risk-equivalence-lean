import KernelSeq.AuxiliaryFilter

/-!
# Lipschitz inverse profile of the auxiliary filter

Completes the inverse-profile estimate for the auxiliary residual filter. The original
inverse profile need not be continuous at zero. Only the original weighted-residual contract is used.
-/

namespace KernelSeq.ResidualFilter

noncomputable section

/-- The lower edge of the cutoff transition in logarithmic coordinates. -/
def cutoffLower (τ : ℝ) : ℝ := Real.log (1 + τ / 3)

/-- The denominator relating log-shrinkage to the inverse profile. -/
def logDenominator (u : ℝ) : ℝ := 1 - Real.exp (-u)

theorem cutoffLower_pos {τ : ℝ} (hτ : 0 < τ) : 0 < cutoffLower τ :=
  Real.log_pos (by linarith)

theorem logCutoff_eq_zero {τ u : ℝ} (hτ : 0 < τ) (hu : u ≤ cutoffLower τ) :
    logCutoff τ u = 0 := by
  apply cutoff_eq_zero
  apply (div_le_iff₀ hτ).2
  have he := Real.exp_le_exp.mpr hu
  rw [cutoffLower, Real.exp_log (by positivity : 0 < 1 + τ / 3)] at he
  linarith

/-- Away from the cutoff origin, the denominator is at least `τ/4`. -/
theorem logDenominator_lower {τ u : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1)
    (hu : cutoffLower τ ≤ u) : τ / 4 ≤ logDenominator u := by
  have hmono : Real.exp (-u) ≤ Real.exp (-cutoffLower τ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hid : logDenominator (cutoffLower τ) = τ / (3 + τ) := by
    unfold logDenominator cutoffLower
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 + τ / 3)]
    field_simp
    ring
  have hbase : τ / 4 ≤ τ / (3 + τ) :=
    div_le_div_of_nonneg_left hτ.le (by positivity) (by linarith)
  rw [← hid] at hbase
  unfold logDenominator at hbase ⊢
  linarith

/-- Shrinkage equals the inverse profile multiplied by the log denominator. -/
theorem shrinkage_eq_logDenominator_mul {lam : ℝ} (hlam : 0 < lam)
    (φ : ℝ → ℝ) (u : ℝ) :
    shrinkage φ (spectralCoordinate lam u) = logDenominator u * inverseProfile lam φ u := by
  unfold shrinkage logDenominator inverseProfile spectralCoordinate
  rw [Real.exp_neg]
  field_simp
  ring

/-- The logarithmic denominator is 1-Lipschitz on nonnegative inputs. -/
theorem logDenominator_lipschitz {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |logDenominator u - logDenominator v| ≤ |u - v| := by
  have h := exp_neg_mul_lipschitz (by norm_num : (0 : ℝ) ≤ 1) hu hv
  have hid : logDenominator u - logDenominator v = Real.exp (-v) - Real.exp (-u) := by
    unfold logDenominator
    ring
  rw [hid, abs_sub_comm]
  simpa only [neg_one_mul, one_mul] using h

/-- Quotient comparison for the original inverse profile away from zero. -/
theorem Contract.inverseProfile_lipschitz_above_cutoff
    {lam M ρ A τ : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) (hτ : 0 < τ) (hτone : τ ≤ 1)
    {u v : ℝ} (hu : u ∈ logDomain lam M) (hv : v ∈ logDomain lam M)
    (hua : cutoffLower τ ≤ u) (hva : cutoffLower τ ≤ v) :
    |inverseProfile lam φ u - inverseProfile lam φ v| ≤
      (4 * (A * (1 + ρ) + A) / τ) * |u - v| := by
  have hgu := logDenominator_lower hτ hτone hua
  have hgv := logDenominator_lower hτ hτone hva
  have hgu0 : 0 < logDenominator u := lt_of_lt_of_le (by positivity : 0 < τ / 4) hgu
  have hFv : |inverseProfile lam φ v| ≤ A :=
    le_trans (le_add_of_nonneg_right (abs_nonneg _)) (h.size v hv)
  have hQ := h.shrinkage_lipschitz hlam hu hv
  have hgd := logDenominator_lipschitz hv.1 hu.1
  have hid : logDenominator u * (inverseProfile lam φ u - inverseProfile lam φ v) =
      (shrinkage φ (spectralCoordinate lam u) - shrinkage φ (spectralCoordinate lam v)) +
        (logDenominator v - logDenominator u) * inverseProfile lam φ v := by
    rw [shrinkage_eq_logDenominator_mul hlam, shrinkage_eq_logDenominator_mul hlam]
    ring
  have hstep := abs_add_le
    (shrinkage φ (spectralCoordinate lam u) - shrinkage φ (spectralCoordinate lam v))
    ((logDenominator v - logDenominator u) * inverseProfile lam φ v)
  rw [← hid, abs_mul, abs_of_pos hgu0, abs_mul] at hstep
  have hprod := mul_le_mul hgd hFv (abs_nonneg _) (abs_nonneg (v - u))
  rw [abs_sub_comm v u] at hprod
  have hscaled := mul_le_mul_of_nonneg_right hgu
    (abs_nonneg (inverseProfile lam φ u - inverseProfile lam φ v))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hτ).2
  nlinarith

/-- The auxiliary inverse is zero throughout the lower cutoff region. -/
theorem auxiliary_inverseProfile_eq_zero {lam τ u : ℝ} (hlam : 0 < lam)
    (hτ : 0 < τ) (φ : ℝ → ℝ) (hu : u ≤ cutoffLower τ) :
    inverseProfile lam (auxiliaryFilter lam τ φ) u = 0 := by
  rw [auxiliary_inverseProfile, cutoff_spectralCoordinate hlam.ne', logCutoff_eq_zero hτ hu,
    zero_mul]

/-- The auxiliary inverse profile has the required `C/τ` Lipschitz bound.
The explicit constant `C = A * (13 + 4*ρ)` is independent of lam, τ and M. -/
theorem Contract.auxiliary_inverse_lipschitz {lam M ρ A τ : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) (hτ : 0 < τ) (hτone : τ ≤ 1)
    {u v : ℝ} (hu : u ∈ logDomain lam M) (hv : v ∈ logDomain lam M) :
    |inverseProfile lam (auxiliaryFilter lam τ φ) u -
      inverseProfile lam (auxiliaryFilter lam τ φ) v| ≤
      (A * (13 + 4 * ρ) / τ) * |u - v| := by
  let C := A * (13 + 4 * ρ) / τ
  have hA : 0 ≤ A :=
    (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (h.size u hu)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg hA (by linarith [h.rho_pos])) hτ.le
  have hhigh : ∀ a ∈ logDomain lam M, ∀ b ∈ logDomain lam M,
      cutoffLower τ ≤ a → cutoffLower τ ≤ b →
      |inverseProfile lam (auxiliaryFilter lam τ φ) a -
        inverseProfile lam (auxiliaryFilter lam τ φ) b| ≤ C * |a - b| := by
    intro a ha b hb haa hba
    have hF := h.inverseProfile_lipschitz_above_cutoff hlam hτ hτone ha hb haa hba
    have hFb : |inverseProfile lam φ b| ≤ A :=
      le_trans (le_add_of_nonneg_right (abs_nonneg _)) (h.size b hb)
    have hc := logCutoff_lipschitz hτ hτone a b
    have hca := cutoff_mem ((Real.exp a - 1) / τ)
    change logCutoff τ a ∈ Set.Icc (0 : ℝ) 1 at hca
    rw [auxiliary_inverseProfile, auxiliary_inverseProfile,
      cutoff_spectralCoordinate hlam.ne', cutoff_spectralCoordinate hlam.ne']
    have hid : logCutoff τ a * inverseProfile lam φ a -
        logCutoff τ b * inverseProfile lam φ b =
        logCutoff τ a * (inverseProfile lam φ a - inverseProfile lam φ b) +
          (logCutoff τ a - logCutoff τ b) * inverseProfile lam φ b := by ring
    rw [hid]
    calc
      _ ≤ |logCutoff τ a * (inverseProfile lam φ a - inverseProfile lam φ b)| +
          |(logCutoff τ a - logCutoff τ b) * inverseProfile lam φ b| := abs_add_le _ _
      _ = logCutoff τ a * |inverseProfile lam φ a - inverseProfile lam φ b| +
          |logCutoff τ a - logCutoff τ b| * |inverseProfile lam φ b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hca.1]
      _ ≤ 1 * ((4 * (A * (1 + ρ) + A) / τ) * |a - b|) +
          ((5 / τ) * |a - b|) * A := by
        apply add_le_add
        · exact mul_le_mul hca.2 hF (abs_nonneg _) (by norm_num)
        · exact mul_le_mul hc hFb (abs_nonneg _) (by positivity)
      _ = C * |a - b| := by dsimp [C]; ring
  have hordered : ∀ a ∈ logDomain lam M, ∀ b ∈ logDomain lam M, a ≤ b →
      |inverseProfile lam (auxiliaryFilter lam τ φ) a -
        inverseProfile lam (auxiliaryFilter lam τ φ) b| ≤ C * |a - b| := by
    intro a ha b hb hab
    by_cases hba : b ≤ cutoffLower τ
    · rw [auxiliary_inverseProfile_eq_zero hlam hτ φ hba,
        auxiliary_inverseProfile_eq_zero hlam hτ φ (hab.trans hba)]
      simp only [sub_self, abs_zero]
      positivity
    · by_cases haa : cutoffLower τ ≤ a
      · exact hhigh a ha b hb haa (le_of_not_ge hba)
      · have hau : a ≤ cutoffLower τ := le_of_not_ge haa
        have hub : cutoffLower τ ≤ b := le_of_not_ge hba
        have haJ : cutoffLower τ ∈ logDomain lam M :=
          ⟨(cutoffLower_pos hτ).le, hub.trans hb.2⟩
        have hh := hhigh (cutoffLower τ) haJ b hb le_rfl hub
        rw [auxiliary_inverseProfile_eq_zero hlam hτ φ le_rfl] at hh
        rw [auxiliary_inverseProfile_eq_zero hlam hτ φ hau]
        apply hh.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [abs_of_nonpos (sub_nonpos.mpr hub), abs_of_nonpos (sub_nonpos.mpr hab)]
        linarith
  rcases le_total u v with huv | hvu
  · exact hordered u hu v hv huv
  · simpa only [abs_sub_comm] using hordered v hv u hu hvu

end
end KernelSeq.ResidualFilter
