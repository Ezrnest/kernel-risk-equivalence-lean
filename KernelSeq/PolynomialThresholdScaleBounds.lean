import KernelSeq.PolynomialScaleBounds
import KernelSeq.PolynomialSpectrumThreshold

/-!
# Actual dimension bounds from asymptotic polynomial spectra

The common threshold is a spectral-index threshold, not an additional sample
size or source restriction. The initial eigenvalue prefix is handled by the
original kernel bound; the lower dimension uses only the tail indices.
-/

open MeasureTheory Filter Topology Asymptotics

namespace KernelSeq
noncomputable section

theorem polynomial_count_large_threshold_of_small_regularization {lam c D β : ℝ}
    (J0 : ℕ) (hlam : 0 < lam) (_hc : 0 < c) (hD : 0 < D) (hβ : 0 < β)
    (hsmall : lam ≤ c / (D * (2 * ((J0 : ℝ) + 1)) ^ β)) :
    2 * ((J0 : ℝ) + 1) ≤ (c / (lam * D)) ^ (1 / β) := by
  let B : ℝ := 2 * ((J0 : ℝ) + 1)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hp : 0 < B ^ β := Real.rpow_pos_of_pos hB _
  have hmul := (le_div_iff₀ (mul_pos hD hp)).mp hsmall
  have hbase : B ^ β ≤ c / (lam * D) := by
    apply (le_div_iff₀ (mul_pos hlam hD)).mpr
    nlinarith
  have hh := Real.rpow_le_rpow hp.le hbase (one_div_pos.mpr hβ).le
  have he : (B ^ β) ^ (1 / β) = B := by
    rw [← Real.rpow_mul hB.le]
    have : β * (1 / β) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rwa [he] at hh

variable {J : Type*} {l : Filter J} [NeBot l] {κ ρ A : ℝ}

omit [NeBot l] in
theorem polynomial_threshold_effective_dimension_isBigO (m : J → SpectralScaleModel κ ρ A)
    (e : ∀ i, (m i).SpectrumEnumeration) (J0 : ℕ) {β C p : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpβ : 1 < β * p)
    (hupper : ∀ᶠ i in l, ∀ j : ℕ, J0 ≤ j →
      (m i).eigenvalue (e i) j ≤ C * ((j : ℝ) + 1) ^ (-β)) :
    (fun i => (m i).N) =O[l] (fun i => (m i).lam ^ (-p)) := by
  apply IsBigO.of_bound (polynomialEnvelopeGlobalConstant C (κ ^ 2) β J0 ^ p * polynomialMomentConstant β p)
  filter_upwards [hupper] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (m i).N_nonneg, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (m i).lambda_pos.le (-p))]
  exact featureEffectiveDimension_le_polynomial_threshold
    (m i).feature (m i).feature_memLp (e i) J0 (m i).lambda_pos hC
    (m i).population_bound hβ hp hp1 hpβ hi

theorem polynomial_threshold_filter_dimension_lower_eventually (m : J → SpectralScaleModel κ ρ A)
    (e : ∀ i, (m i).SpectrumEnumeration) (J0 : ℕ) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hlam : Tendsto (fun i => (m i).lam) l (𝓝 0))
    (hlower : ∀ᶠ i in l, ∀ j : ℕ, J0 ≤ j →
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).eigenvalue (e i) j) :
    ∀ᶠ i in l, (1 / 8 : ℝ) * (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β) *
      (m i).lam ^ (-(1 / β)) ≤ (m i).Q := by
  obtain ⟨i0, _⟩ := hlower.exists
  have hA := (m i0).filter_contract.constant_nonneg (m i0).lambda_pos (sq_nonneg κ)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  have hδ : 0 < c / (ResidualFilter.resolvedScaleFactor ρ A * (2 * ((J0 : ℝ) + 1)) ^ β) := by positivity
  filter_upwards [hlower, hlam.eventually (gt_mem_nhds hδ)] with i hi hli
  apply featureFilterDimension_ge_polynomial_threshold (m i).feature (m i).feature_memLp
    (e i) J0 (m i).φ (m i).lambda_pos (m i).population_bound (m i).spectral_filter
    (m i).filter_contract hc hβ hi
  exact polynomial_count_large_threshold_of_small_regularization J0 (m i).lambda_pos hc hD hβ hli.le

theorem polynomial_threshold_filter_dimension_pos_eventually (m : J → SpectralScaleModel κ ρ A)
    (e : ∀ i, (m i).SpectrumEnumeration) (J0 : ℕ) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hlam : Tendsto (fun i => (m i).lam) l (𝓝 0))
    (hlower : ∀ᶠ i in l, ∀ j : ℕ, J0 ≤ j →
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).eigenvalue (e i) j) :
    ∀ᶠ i in l, 0 < (m i).Q := by
  obtain ⟨i0, _⟩ := hlower.exists
  have hA := (m i0).filter_contract.constant_nonneg (m i0).lambda_pos (sq_nonneg κ)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  filter_upwards [polynomial_threshold_filter_dimension_lower_eventually m e J0 hβ hc hlam hlower] with i hi
  have hli := (m i).lambda_pos
  exact (by positivity : 0 < (1 / 8 : ℝ) *
    (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β) * (m i).lam ^ (-(1 / β))).trans_le hi

theorem polynomial_threshold_inverse_filter_dimension_isBigO (m : J → SpectralScaleModel κ ρ A)
    (e : ∀ i, (m i).SpectrumEnumeration) (J0 : ℕ) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hlam : Tendsto (fun i => (m i).lam) l (𝓝 0))
    (hlower : ∀ᶠ i in l, ∀ j : ℕ, J0 ≤ j →
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).eigenvalue (e i) j) :
    (fun i => ((m i).Q)⁻¹) =O[l] (fun i => (m i).lam ^ (1 / β)) := by
  obtain ⟨i0, _⟩ := hlower.exists
  have hA := (m i0).filter_contract.constant_nonneg (m i0).lambda_pos (sq_nonneg κ)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  let b := (1 / 8 : ℝ) * (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β)
  have hb : 0 < b := by dsimp only [b]; positivity
  apply IsBigO.of_bound b⁻¹
  filter_upwards [polynomial_threshold_filter_dimension_lower_eventually m e J0 hβ hc hlam hlower] with i hi
  have hbase : 0 < b * (m i).lam ^ (-(1 / β)) := mul_pos hb (Real.rpow_pos_of_pos (m i).lambda_pos _)
  have hQ : 0 < (m i).Q := hbase.trans_le hi
  have hinv := one_div_le_one_div_of_le hbase hi
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hQ), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (m i).lambda_pos.le (1 / β))]
  simpa only [one_div, mul_inv_rev, Real.rpow_neg (m i).lambda_pos.le, inv_inv, mul_comm] using hinv

end
end KernelSeq
