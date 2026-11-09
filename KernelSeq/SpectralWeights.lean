import KernelSeq.ResidualFilter
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Source weights at the spectral coefficient level

The weighted target estimate for Lipschitz bias comparison is
`∑ a(t_j)^2 f_j^2 ≤ (A+1)^2 ∑ (lam/(t_j+lam))^α f_j^2`.
All summability is derived from square-summability of the actual coefficients.
Identifying these series with operator functional calculus and Hilbert norms
(Parseval) is deliberately a separate, upstream spectral theorem application.
-/

namespace KernelSeq

open ResidualFilter

noncomputable section

/-- The positive residual weight `a_{lam,α}(t)` in the manuscript. -/
def residualWeight (lam α : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  residual φ t + (lam / (t + lam)) ^ (α / 2)

/-- Every spectral value has a regularization weight in (0,1]. -/
theorem regularization_weight_mem {lam M t : ℝ} (hlam : 0 < lam)
    (ht : t ∈ Set.Icc (0 : ℝ) M) :
    0 < lam / (t + lam) ∧ lam / (t + lam) ≤ 1 := by
  have hden : 0 < t + lam := add_pos_of_nonneg_of_pos ht.1 hlam
  exact ⟨div_pos hlam hden, (div_le_one hden).2 (by linarith [ht.1])⟩

/-- Residual admissibility implies that the source weight is nonnegative. -/
theorem residualWeight_nonneg {lam M α t : ℝ} {φ : ℝ → ℝ}
    (hf : SpectralFilter M φ) (hlam : 0 < lam) (ht : t ∈ Set.Icc (0 : ℝ) M) :
    0 ≤ residualWeight lam α φ t := by
  exact add_nonneg (hf.residual_nonneg ht)
    (Real.rpow_nonneg (regularization_weight_mem hlam ht).1.le _)

/-- Scalar estimate with the exact manuscript constant, uniform in t and lam.
The upper restriction α≤1 is not needed for this scalar step; α/2≤ρ suffices. -/
theorem residualWeight_sq_le {lam M ρ A α t : ℝ} {φ : ℝ → ℝ}
    (hf : SpectralFilter M φ) (h : Contract lam M ρ A φ)
    (hlam : 0 < lam) (ht : t ∈ Set.Icc (0 : ℝ) M)
    (hαρ : α / 2 ≤ ρ) :
    residualWeight lam α φ t ^ 2 ≤
      (A + 1) ^ 2 * (lam / (t + lam)) ^ α := by
  have hb := regularization_weight_mem hlam ht
  have hA : 0 ≤ A := (abs_nonneg _).trans (h.spectral_size hlam ht).1
  have hres := h.residual_size hlam ht
  rw [abs_of_nonneg (hf.residual_nonneg ht)] at hres
  have horder := Real.rpow_le_rpow_of_exponent_ge hb.1 hb.2 hαρ
  have hweight : residualWeight lam α φ t ≤
      (A + 1) * (lam / (t + lam)) ^ (α / 2) := by
    unfold residualWeight
    have hmul := mul_le_mul_of_nonneg_left horder hA
    linarith
  have ha := residualWeight_nonneg (α := α) hf hlam ht
  have hupper : 0 ≤ (A + 1) * (lam / (t + lam)) ^ (α / 2) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hb.1.le _)
  have hsquare := (sq_le_sq₀ ha hupper).2 hweight
  have hpow : ((lam / (t + lam)) ^ (α / 2)) ^ 2 = (lam / (t + lam)) ^ α := by
    rw [← Real.rpow_two, ← Real.rpow_mul hb.1.le]
    congr 1
    ring
  simpa only [mul_pow, hpow] using hsquare

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

/-- Summability of the squared residual-weighted target coefficients is proved,
not assumed as an additional source condition. -/
theorem summable_residualWeight_coefficients {J : Type*} {lam M ρ A α : ℝ}
    {φ : ℝ → ℝ} (t f : J → ℝ)
    (hfilter : SpectralFilter M φ) (h : Contract lam M ρ A φ)
    (hlam : 0 < lam) (hα : 0 ≤ α) (hαρ : α / 2 ≤ ρ)
    (ht : ∀ j, t j ∈ Set.Icc (0 : ℝ) M)
    (hf : Summable (fun j => f j ^ 2)) :
    Summable (fun j => residualWeight lam α φ (t j) ^ 2 * f j ^ 2) := by
  have hsum := (summable_regularized_coefficients t f hlam hα ht hf).mul_left ((A + 1) ^ 2)
  apply Summable.of_nonneg_of_le _ _ hsum
  · intro j
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro j
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (residualWeight_sq_le hfilter h hlam (ht j) hαρ) (sq_nonneg (f j))

/-- The source-weight bound at the actual infinite spectral-sum level.
The index type may be empty, finite, or infinite; no attained maximum or
finite-dimensional ambient space is assumed. -/
theorem tsum_residualWeight_coefficients_le {J : Type*} {lam M ρ A α : ℝ}
    {φ : ℝ → ℝ} (t f : J → ℝ)
    (hfilter : SpectralFilter M φ) (h : Contract lam M ρ A φ)
    (hlam : 0 < lam) (hα : 0 ≤ α) (hαρ : α / 2 ≤ ρ)
    (ht : ∀ j, t j ∈ Set.Icc (0 : ℝ) M)
    (hf : Summable (fun j => f j ^ 2)) :
    (∑' j, residualWeight lam α φ (t j) ^ 2 * f j ^ 2) ≤
      (A + 1) ^ 2 * ∑' j, (lam / (t j + lam)) ^ α * f j ^ 2 := by
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    (summable_residualWeight_coefficients t f hfilter h hlam hα hαρ ht hf)
    ((summable_regularized_coefficients t f hlam hα ht hf).mul_left _)
  intro j
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (residualWeight_sq_le hfilter h hlam (ht j) hαρ) (sq_nonneg (f j))

/-- The exact exponent `α_ψ = min {2ρ,1}` used in the bias comparison. -/
theorem tsum_residualWeight_coefficients_le_residual_order {J : Type*}
    {lam M ρ A : ℝ} {φ : ℝ → ℝ} (t f : J → ℝ)
    (hfilter : SpectralFilter M φ) (h : Contract lam M ρ A φ)
    (hlam : 0 < lam) (ht : ∀ j, t j ∈ Set.Icc (0 : ℝ) M)
    (hf : Summable (fun j => f j ^ 2)) :
    (∑' j, residualWeight lam (min (2 * ρ) 1) φ (t j) ^ 2 * f j ^ 2) ≤
      (A + 1) ^ 2 * ∑' j, (lam / (t j + lam)) ^ (min (2 * ρ) 1) * f j ^ 2 := by
  apply tsum_residualWeight_coefficients_le t f hfilter h hlam _ _ ht hf
  · exact le_min (by linarith [h.rho_pos]) (by norm_num)
  · linarith [min_le_left (2 * ρ) (1 : ℝ)]

end
end KernelSeq
