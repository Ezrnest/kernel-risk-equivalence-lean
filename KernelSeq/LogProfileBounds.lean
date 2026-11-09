import KernelSeq.LogInteractionFactorization
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Bounds and genuine global extensions of the logarithmic profiles

The residual profile used by the interaction factorization inherits its size
and Lipschitz bounds from the manuscript's residual-only contract. Clamping
extends interval profiles to all real inputs without changing those bounds.
No differentiability of the filter or of its auxiliary cutoff is assumed.
-/

namespace KernelSeq

noncomputable section

theorem logInteractionResidualProfile_eq_weighted (α ρ : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    logInteractionResidualProfile α φ u =
      Real.exp (-(ρ - α / 2) * u) * ResidualFilter.weightedResidual 1 ρ φ u := by
  rw [ResidualFilter.weightedResidual_eq_exp_mul (by norm_num : (0 : ℝ) < 1)]
  simp only [ResidualFilter.spectralCoordinate, one_mul, logInteractionResidualProfile]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem logInteractionInverseProfile_abs_le {M ρ A : ℝ} {φ : ℝ → ℝ}
    (h : ResidualFilter.Contract 1 M ρ A φ) {u : ℝ}
    (hu : u ∈ ResidualFilter.logDomain 1 M) :
    |logInteractionInverseProfile φ u| ≤ A := by
  rw [logInteractionInverseProfile_eq]
  exact (le_add_of_nonneg_right (abs_nonneg _)).trans (h.size u hu)

theorem logInteractionResidualProfile_abs_le {M ρ A α : ℝ} {φ : ℝ → ℝ}
    (h : ResidualFilter.Contract 1 M ρ A φ) (hα : α / 2 ≤ ρ) {u : ℝ}
    (hu : u ∈ ResidualFilter.logDomain 1 M) :
    |logInteractionResidualProfile α φ u| ≤ A := by
  have hP : |ResidualFilter.weightedResidual 1 ρ φ u| ≤ A :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans (h.size u hu)
  have he : |Real.exp (-(ρ - α / 2) * u)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hu.1
  rw [logInteractionResidualProfile_eq_weighted α ρ, abs_mul]
  exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by simpa using hP)

theorem logInteractionInverseProfile_nonneg {M : ℝ} {φ : ℝ → ℝ}
    (h : ResidualFilter.SpectralFilter M φ) (hM : 0 ≤ M) {u : ℝ}
    (hu : u ∈ ResidualFilter.logDomain 1 M) :
    0 ≤ logInteractionInverseProfile φ u := by
  have ht := ResidualFilter.spectralCoordinate_mem (by norm_num : (0 : ℝ) < 1) hM hu
  simp only [ResidualFilter.spectralCoordinate, one_mul] at ht
  exact mul_nonneg (Real.exp_pos _).le (h.nonneg _ ht)

theorem logInteractionResidualProfile_nonneg {M α : ℝ} {φ : ℝ → ℝ}
    (h : ResidualFilter.SpectralFilter M φ) (hM : 0 ≤ M) {u : ℝ}
    (hu : u ∈ ResidualFilter.logDomain 1 M) :
    0 ≤ logInteractionResidualProfile α φ u := by
  have ht := ResidualFilter.spectralCoordinate_mem (by norm_num : (0 : ℝ) < 1) hM hu
  simp only [ResidualFilter.spectralCoordinate, one_mul] at ht
  exact mul_nonneg (Real.exp_pos _).le (h.residual_nonneg ht)

theorem logInteractionResidualProfile_lipschitz {M ρ A α : ℝ} {φ : ℝ → ℝ}
    (h : ResidualFilter.Contract 1 M ρ A φ) (hα : α / 2 ≤ ρ) {u v : ℝ}
    (hu : u ∈ ResidualFilter.logDomain 1 M) (hv : v ∈ ResidualFilter.logDomain 1 M) :
    |logInteractionResidualProfile α φ u - logInteractionResidualProfile α φ v| ≤
      A * (1 + ρ - α / 2) * |u - v| := by
  have hβ : 0 ≤ ρ - α / 2 := by linarith
  have hPv : |ResidualFilter.weightedResidual 1 ρ φ v| ≤ A :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans (h.size v hv)
  have heu : |Real.exp (-(ρ - α / 2) * u)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) hu.1)
  have hed := ResidualFilter.exp_neg_mul_lipschitz hβ hu.1 hv.1
  have hPd := h.residual_lipschitz u hu v hv
  rw [logInteractionResidualProfile_eq_weighted α ρ,
    logInteractionResidualProfile_eq_weighted α ρ]
  have hid :
      Real.exp (-(ρ - α / 2) * u) * ResidualFilter.weightedResidual 1 ρ φ u -
        Real.exp (-(ρ - α / 2) * v) * ResidualFilter.weightedResidual 1 ρ φ v =
      Real.exp (-(ρ - α / 2) * u) *
          (ResidualFilter.weightedResidual 1 ρ φ u - ResidualFilter.weightedResidual 1 ρ φ v) +
        (Real.exp (-(ρ - α / 2) * u) - Real.exp (-(ρ - α / 2) * v)) *
          ResidualFilter.weightedResidual 1 ρ φ v := by ring
  rw [hid]
  calc
    _ ≤ |Real.exp (-(ρ - α / 2) * u) *
          (ResidualFilter.weightedResidual 1 ρ φ u - ResidualFilter.weightedResidual 1 ρ φ v)| +
        |(Real.exp (-(ρ - α / 2) * u) - Real.exp (-(ρ - α / 2) * v)) *
          ResidualFilter.weightedResidual 1 ρ φ v| := abs_add_le _ _
    _ = |Real.exp (-(ρ - α / 2) * u)| *
          |ResidualFilter.weightedResidual 1 ρ φ u - ResidualFilter.weightedResidual 1 ρ φ v| +
        |Real.exp (-(ρ - α / 2) * u) - Real.exp (-(ρ - α / 2) * v)| *
          |ResidualFilter.weightedResidual 1 ρ φ v| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (A * |u - v|) + ((ρ - α / 2) * |u - v|) * A := by
      apply add_le_add
      · exact mul_le_mul heu hPd (abs_nonneg _) (by norm_num)
      · exact mul_le_mul hed hPv (abs_nonneg _) (mul_nonneg hβ (abs_nonneg _))
    _ = _ := by ring

/-- Nearest-point clamping onto the real logarithmic interval. -/
def logProfileClamp (M : ℝ) (hM : 0 ≤ M) (u : ℝ) : ℝ :=
  Set.projIcc 0 (Real.log (1 + M)) (Real.log_nonneg (by linarith)) u

theorem logProfileClamp_mem (M : ℝ) (hM : 0 ≤ M) (u : ℝ) :
    logProfileClamp M hM u ∈ ResidualFilter.logDomain 1 M := by
  simpa only [ResidualFilter.logDomain, div_one, logProfileClamp] using
    (Set.projIcc 0 (Real.log (1 + M)) (Real.log_nonneg (by linarith)) u).property

theorem logProfileClamp_eq {M : ℝ} (hM : 0 ≤ M) {u : ℝ}
    (hu : u ∈ ResidualFilter.logDomain 1 M) : logProfileClamp M hM u = u := by
  unfold logProfileClamp
  rw [Set.projIcc_of_mem]
  simpa only [ResidualFilter.logDomain, div_one] using hu

theorem logProfileClamp_lipschitz (M : ℝ) (hM : 0 ≤ M) (u v : ℝ) :
    |logProfileClamp M hM u - logProfileClamp M hM v| ≤ |u - v| := by
  have hh := (LipschitzWith.projIcc
    (Real.log_nonneg (show 1 ≤ 1 + M by linarith))).dist_le_mul u v
  simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, logProfileClamp] using hh

/-- A genuine global extension, preserving each actual spectral-grid value. -/
def extendedLogProfile (M : ℝ) (hM : 0 ≤ M) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  f (logProfileClamp M hM u)

theorem extendedLogProfile_eq {M : ℝ} (hM : 0 ≤ M) (f : ℝ → ℝ) {u : ℝ}
    (hu : u ∈ ResidualFilter.logDomain 1 M) : extendedLogProfile M hM f u = f u := by
  rw [extendedLogProfile, logProfileClamp_eq hM hu]

theorem extendedLogProfile_abs_le {M A : ℝ} (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hf : ∀ u ∈ ResidualFilter.logDomain 1 M, |f u| ≤ A) (u : ℝ) :
    |extendedLogProfile M hM f u| ≤ A := hf _ (logProfileClamp_mem M hM u)

theorem extendedLogProfile_nonneg {M : ℝ} (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hf : ∀ u ∈ ResidualFilter.logDomain 1 M, 0 ≤ f u) (u : ℝ) :
    0 ≤ extendedLogProfile M hM f u := hf _ (logProfileClamp_mem M hM u)

theorem extendedLogProfile_lipschitz {M L : ℝ} (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hL : 0 ≤ L)
    (hf : ∀ u ∈ ResidualFilter.logDomain 1 M, ∀ v ∈ ResidualFilter.logDomain 1 M,
      |f u - f v| ≤ L * |u - v|) (u v : ℝ) :
    |extendedLogProfile M hM f u - extendedLogProfile M hM f v| ≤ L * |u - v| :=
  (hf _ (logProfileClamp_mem M hM u) _ (logProfileClamp_mem M hM v)).trans
    (mul_le_mul_of_nonneg_left (logProfileClamp_lipschitz M hM u v) hL)

end
end KernelSeq
