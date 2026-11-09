import KernelSeq.CompactDOI
import KernelSeq.SpectralWeights

/-!
# The logarithmic interaction-kernel factorization

Scalar factorization of the interaction multiplier in logarithmic coordinates. The
general finite-dimensional Lipschitz/HMS estimates remain external leaves; this file
does not replace the interaction bound by an assumed multiplier certificate.
-/

namespace KernelSeq

noncomputable section

def interactionTheta (α z : ℝ) : ℝ :=
  if z = 0 then 1 else z * Real.exp ((1 - α / 2) * z) / (Real.exp z - 1)

def interactionChi (α z : ℝ) : ℝ :=
  if z = 0 then α / 2 - 1 else (1 - Real.exp ((1 - α / 2) * z)) / (Real.exp z - 1)

def interactionChiOffDiagonal (α t s : ℝ) : ℝ :=
  if t = s then 0 else interactionChi α (t - s)

def logInteractionInverseProfile (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp t * φ (Real.exp t - 1)

def logInteractionResidualProfile (α : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (α * t / 2) * ResidualFilter.residual φ (Real.exp t - 1)

theorem logInteractionInverseProfile_eq (φ : ℝ → ℝ) (t : ℝ) :
    logInteractionInverseProfile φ t = ResidualFilter.inverseProfile 1 φ t := by
  simp only [logInteractionInverseProfile, ResidualFilter.inverseProfile,
    ResidualFilter.spectralCoordinate, one_mul, sub_add_cancel]

theorem exp_sub_one_ne_zero {z : ℝ} (hz : z ≠ 0) : Real.exp z - 1 ≠ 0 := by
  exact sub_ne_zero.mpr (fun h => hz (Real.exp_injective (h.trans Real.exp_zero.symm)))

/-- The algebraic cancellation behind the three-term multiplier decomposition.
The right-hand denominator convention also handles `P_s = -1`. -/
theorem interaction_log_factorization_core (α z Ft Fs Pt Ps : ℝ) (hz : z ≠ 0) :
    (1 / (1 + Ps)) *
      (-Ft * interactionTheta α z * ((Pt - Ps) / z) +
        Pt * interactionTheta α z * ((Ft - Fs) / z) + Ft * Ps * interactionChi α z) =
      (Ft * Ps - Real.exp ((1 - α / 2) * z) * Pt * Fs) /
        ((Real.exp z - 1) * (1 + Ps)) := by
  by_cases hPs : 1 + Ps = 0
  · simp only [hPs, div_zero, zero_mul, mul_zero]
  · rw [interactionTheta, if_neg hz, interactionChi, if_neg hz]
    field_simp [hz, exp_sub_one_ne_zero hz, hPs]
    ring

theorem residualWeight_exp_coordinate (α : ℝ) (φ : ℝ → ℝ) (s : ℝ) :
    residualWeight 1 α φ (Real.exp s - 1) =
      (1 + logInteractionResidualProfile α φ s) / Real.exp (α * s / 2) := by
  have hr : (1 / Real.exp s) ^ (α / 2) = (Real.exp (α * s / 2))⁻¹ := by
    rw [one_div, Real.inv_rpow (Real.exp_pos s).le, Real.rpow_def_of_pos (Real.exp_pos s), Real.log_exp]
    congr 2
    ring
  rw [residualWeight, sub_add_cancel, hr, logInteractionResidualProfile]
  field_simp [Real.exp_ne_zero]
  ring

/-- The two exponential weights in the transformed numerator have the same
common scalar factor after passing to the logarithmic difference. -/
theorem logInteraction_exp_balance (α t s : ℝ) :
    Real.exp ((1 - α / 2) * (t - s)) * Real.exp (α * t / 2) * Real.exp s =
      Real.exp t * Real.exp (α * s / 2) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The actual dimensionless normalized interaction symbol, with the common
eigenvalue entries set to zero. -/
def logarithmicInteractionKernel (α : ℝ) (φ : ℝ → ℝ) (u v : ℝ) : ℝ :=
  if u = v then 0 else (1 + u) * (1 + v) *
    (φ u * ResidualFilter.residual φ v - ResidualFilter.residual φ u * φ v) /
      ((u - v) * residualWeight 1 α φ v)

/-- The full actual three-term logarithmic factorization, including equal
spectral values. This is scalar algebra, without a multiplier-norm premise. -/
theorem logarithmicInteractionKernel_factorization (α : ℝ) (φ : ℝ → ℝ) (t s : ℝ) :
    logarithmicInteractionKernel α φ (Real.exp t - 1) (Real.exp s - 1) =
      (1 / (1 + logInteractionResidualProfile α φ s)) *
        (-logInteractionInverseProfile φ t * interactionTheta α (t - s) *
            dividedDifference (logInteractionResidualProfile α φ) t s +
          logInteractionResidualProfile α φ t * interactionTheta α (t - s) *
            dividedDifference (logInteractionInverseProfile φ) t s +
          logInteractionInverseProfile φ t * logInteractionResidualProfile α φ s *
            interactionChiOffDiagonal α t s) := by
  classical
  by_cases hts : t = s
  · subst s
    simp [logarithmicInteractionKernel, dividedDifference, interactionChiOffDiagonal]
  have hz : t - s ≠ 0 := sub_ne_zero.mpr hts
  have huv : Real.exp t - 1 ≠ Real.exp s - 1 := by
    intro h
    apply hts
    exact Real.exp_injective (by linarith)
  simp only [dividedDifference, interactionChiOffDiagonal, if_neg hts]
  rw [interaction_log_factorization_core α (t - s)
    (logInteractionInverseProfile φ t) (logInteractionInverseProfile φ s)
    (logInteractionResidualProfile α φ t) (logInteractionResidualProfile α φ s) hz]
  rw [logarithmicInteractionKernel, if_neg huv, residualWeight_exp_coordinate]
  have hd : (Real.exp t - 1) - (Real.exp s - 1) =
      Real.exp s * (Real.exp (t - s) - 1) := by
    rw [Real.exp_sub]
    field_simp [Real.exp_ne_zero]
    ring
  rw [hd, show 1 + (Real.exp t - 1) = Real.exp t by ring,
    show 1 + (Real.exp s - 1) = Real.exp s by ring]
  by_cases hPs : 1 + logInteractionResidualProfile α φ s = 0
  · simp only [hPs, zero_div, mul_zero, div_zero]
  · have hPs' : 1 + Real.exp (α * s / 2) * ResidualFilter.residual φ (Real.exp s - 1) ≠ 0 :=
      hPs
    simp only [logInteractionInverseProfile, logInteractionResidualProfile]
    have hn : Real.exp ((1 - α / 2) * (t - s)) *
        (Real.exp (α * t / 2) * ResidualFilter.residual φ (Real.exp t - 1)) *
        (Real.exp s * φ (Real.exp s - 1)) =
      Real.exp t * Real.exp (α * s / 2) * ResidualFilter.residual φ (Real.exp t - 1) *
        φ (Real.exp s - 1) := by
      calc
        _ = (Real.exp ((1 - α / 2) * (t - s)) * Real.exp (α * t / 2) * Real.exp s) *
            ResidualFilter.residual φ (Real.exp t - 1) * φ (Real.exp s - 1) := by ring
        _ = _ := by rw [logInteraction_exp_balance]
    rw [hn]
    field_simp [Real.exp_ne_zero, exp_sub_one_ne_zero hz, hPs']

end

end KernelSeq
