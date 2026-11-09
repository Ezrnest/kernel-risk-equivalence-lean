import KernelSeq.SpectralScaleModel
import KernelSeq.PowerExponentChoice
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Derived polynomial-spectrum bounds on actual scale rows

Only primitive eigenvalue envelopes, source membership and the prescribed
regularization comparison enter here. Moment and dimension estimates are
supplied by the preceding actual-spectrum proofs.
-/

open MeasureTheory Filter Topology Asymptotics

namespace KernelSeq
noncomputable section

theorem polynomial_count_large_of_small_regularization {lam c D β : ℝ}
    (hlam : 0 < lam) (_hc : 0 < c) (hD : 0 < D) (hβ : 0 < β)
    (hsmall : lam ≤ c / (D * (2 : ℝ) ^ β)) :
    2 ≤ (c / (lam * D)) ^ (1 / β) := by
  have hp : 0 < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  have hmul := (le_div_iff₀ (mul_pos hD hp)).mp hsmall
  have hbase : (2 : ℝ) ^ β ≤ c / (lam * D) := by
    apply (le_div_iff₀ (mul_pos hlam hD)).mpr
    nlinarith
  have hh := Real.rpow_le_rpow hp.le hbase (one_div_pos.mpr hβ).le
  have he : ((2 : ℝ) ^ β) ^ (1 / β) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have : β * (1 / β) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rwa [he] at hh

variable {J : Type*} {l : Filter J} [NeBot l] {κ ρ A : ℝ}

omit [NeBot l] in
theorem scale_regularization_tendsto_zero (m : J → SpectralScaleModel κ ρ A)
    {θ : ℝ} (hθ : 0 < θ)
    (hn : Tendsto (fun i => ((m i).n : ℝ)) l atTop)
    (hreg : (fun i => (m i).lam) =Θ[l] (fun i => ((m i).n : ℝ) ^ (-θ))) :
    Tendsto (fun i => (m i).lam) l (𝓝 0) :=
  hreg.tendsto_zero_iff.mpr ((tendsto_rpow_neg_atTop hθ).comp hn)

omit [NeBot l] in
theorem polynomial_effective_dimension_isBigO (m : J → SpectralScaleModel κ ρ A)
    (e : ∀ i, (m i).SpectrumEnumeration) {β C p : ℝ}
    (hC : 0 ≤ C) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpβ : 1 < β * p)
    (hupper : ∀ᶠ i in l, ∀ j : ℕ, (m i).eigenvalue (e i) j ≤ C * ((j : ℝ) + 1) ^ (-β)) :
    (fun i => (m i).N) =O[l] (fun i => (m i).lam ^ (-p)) := by
  apply IsBigO.of_bound (C ^ p * polynomialMomentConstant β p)
  filter_upwards [hupper] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (m i).N_nonneg, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (m i).lambda_pos.le (-p))]
  exact featureEffectiveDimension_le_polynomial (m i).feature (m i).feature_memLp (e i)
    (m i).lambda_pos hC hp hp1 hpβ hi

theorem polynomial_filter_dimension_lower_eventually (m : J → SpectralScaleModel κ ρ A)
    (e : ∀ i, (m i).SpectrumEnumeration) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hlam : Tendsto (fun i => (m i).lam) l (𝓝 0))
    (hlower : ∀ᶠ i in l, ∀ j : ℕ,
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).eigenvalue (e i) j) :
    ∀ᶠ i in l, (1 / 8 : ℝ) * (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β) *
      (m i).lam ^ (-(1 / β)) ≤ (m i).Q := by
  obtain ⟨i0, _⟩ := hlower.exists
  have hA := (m i0).filter_contract.constant_nonneg (m i0).lambda_pos (sq_nonneg κ)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  have hδ : 0 < c / (ResidualFilter.resolvedScaleFactor ρ A * (2 : ℝ) ^ β) := by positivity
  filter_upwards [hlower, hlam.eventually (gt_mem_nhds hδ)] with i hi hli
  apply featureFilterDimension_ge_polynomial (m i).feature (m i).feature_memLp (e i)
    (m i).φ (m i).lambda_pos (m i).population_bound (m i).spectral_filter
    (m i).filter_contract hc hβ hi
  exact polynomial_count_large_of_small_regularization (m i).lambda_pos hc hD hβ hli.le

theorem polynomial_filter_dimension_pos_eventually (m : J → SpectralScaleModel κ ρ A)
    (e : ∀ i, (m i).SpectrumEnumeration) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hlam : Tendsto (fun i => (m i).lam) l (𝓝 0))
    (hlower : ∀ᶠ i in l, ∀ j : ℕ,
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).eigenvalue (e i) j) :
    ∀ᶠ i in l, 0 < (m i).Q := by
  obtain ⟨i0, _⟩ := hlower.exists
  have hA := (m i0).filter_contract.constant_nonneg (m i0).lambda_pos (sq_nonneg κ)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  filter_upwards [polynomial_filter_dimension_lower_eventually m e hβ hc hlam hlower] with i hi
  have hli := (m i).lambda_pos
  exact (by positivity : 0 < (1 / 8 : ℝ) *
    (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β) * (m i).lam ^ (-(1 / β))).trans_le hi

theorem polynomial_inverse_filter_dimension_isBigO (m : J → SpectralScaleModel κ ρ A)
    (e : ∀ i, (m i).SpectrumEnumeration) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hlam : Tendsto (fun i => (m i).lam) l (𝓝 0))
    (hlower : ∀ᶠ i in l, ∀ j : ℕ,
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).eigenvalue (e i) j) :
    (fun i => ((m i).Q)⁻¹) =O[l] (fun i => (m i).lam ^ (1 / β)) := by
  obtain ⟨i0, _⟩ := hlower.exists
  have hA := (m i0).filter_contract.constant_nonneg (m i0).lambda_pos (sq_nonneg κ)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  let b := (1 / 8 : ℝ) * (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β)
  have hb : 0 < b := by dsimp only [b]; positivity
  apply IsBigO.of_bound b⁻¹
  filter_upwards [polynomial_filter_dimension_lower_eventually m e hβ hc hlam hlower] with i hi
  have hbase : 0 < b * (m i).lam ^ (-(1 / β)) := mul_pos hb (Real.rpow_pos_of_pos (m i).lambda_pos _)
  have hQ : 0 < (m i).Q := hbase.trans_le hi
  have hinv := one_div_le_one_div_of_le hbase hi
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hQ), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (m i).lambda_pos.le (1 / β))]
  simpa only [one_div, mul_inv_rev, Real.rpow_neg (m i).lambda_pos.le, inv_inv, mul_comm] using hinv

omit [NeBot l] in
theorem source_ball_energy_isBigO (m : J → SpectralScaleModel κ ρ A)
    {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hsource : ∀ᶠ i in l, (m i).f ∈ (m i).SourceBall s hs R) :
    (fun i => (m i).S) =O[l] (fun i => (m i).lam ^ (min s (residualComparisonOrder ρ))) := by
  apply IsBigO.of_bound ((1 + κ ^ 2) ^ (s - min s (residualComparisonOrder ρ)) * R ^ 2)
  filter_upwards [hsource] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (m i).S_nonneg, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (m i).lambda_pos.le _)]
  exact (m i).sourceEnergy_le hs hR hi

omit [NeBot l] in
theorem favourable_leverage_isBigO (m : J → SpectralScaleModel κ ρ A)
    {p K : ℝ}
    (hN : (fun i => (m i).N) =O[l] (fun i => (m i).lam ^ (-p)))
    (hL : ∀ᶠ i in l, (m i).L ≤ K * (m i).N) :
    (fun i => (m i).L) =O[l] (fun i => (m i).lam ^ (-p)) := by
  have hLN : (fun i => (m i).L) =O[l] (fun i => (m i).N) := by
    apply IsBigO.of_bound K
    filter_upwards [hL] with i hi
    simpa only [Real.norm_eq_abs, abs_of_nonneg (m i).L_nonneg,
      abs_of_nonneg (m i).N_nonneg] using hi
  exact hLN.trans hN

omit [NeBot l] in
theorem universal_leverage_isBigO (m : J → SpectralScaleModel κ ρ A) :
    (fun i => (m i).L) =O[l] (fun i => (m i).lam ^ (-(1 : ℝ))) := by
  apply IsBigO.of_bound (κ ^ 2)
  filter_upwards [] with i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (m i).L_nonneg,
    Real.rpow_neg_one, abs_of_pos (inv_pos.mpr (m i).lambda_pos), div_eq_mul_inv] using
    (m i).L_le_universal

end
end KernelSeq
