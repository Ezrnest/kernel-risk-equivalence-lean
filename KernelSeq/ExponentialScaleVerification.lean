import KernelSeq.ExponentialSpectrum
import KernelSeq.PolynomialScaleBounds
import KernelSeq.PowerExponentChoice
import KernelSeq.PowerScaleVerification

/-!
# Original exponential-spectrum scale verification

The assumptions are bounds on the actual positive covariance eigenvalues,
source-ball membership, a power regularization schedule and favourable
leverage. The arbitrarily small fractional moment is selected internally.
No moment, effective dimension, filter dimension or scale limit is an input.
The spectral envelope may start after a common finite threshold.
-/

open MeasureTheory Filter Topology Asymptotics

namespace KernelSeq
noncomputable section

variable {J : Type*} {l : Filter J} [NeBot l] {κ ρ A : ℝ}

omit [NeBot l] in
theorem exponential_effective_dimension_isBigO
    (m : J → SpectralScaleModel κ ρ A) (e : ∀ i, (m i).SpectrumEnumeration) (J0 : ℕ)
    {C c0 ν p : ℝ} (hC : 0≤C) (hc0 : 0<c0) (hν : 0<ν) (hp : 0<p) (hp1 : p≤1)
    (hupper : ∀ᶠ i in l, ∀ j : ℕ, J0≤j →
      (m i).eigenvalue (e i) j≤C*Real.exp (-c0*((j:ℝ)+1)^ν)) :
    (fun i => (m i).N) =O[l] (fun i => (m i).lam^(-p)) := by
  apply IsBigO.of_bound ((exponentialEnvelopeGlobalConstant C (κ^2) c0 ν J0)^p *
    stretchedExponentialMomentConstant c0 ν p)
  filter_upwards [hupper] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (m i).N_nonneg, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (m i).lambda_pos.le (-p))]
  exact featureEffectiveDimension_le_exponential_threshold (m i).feature (m i).feature_memLp
    (e i) J0 (m i).lambda_pos hC (m i).population_bound hc0 hν hp hp1 hi

theorem exponential_filter_dimension_lower_eventually
    (m : J → SpectralScaleModel κ ρ A) (e : ∀ i, (m i).SpectrumEnumeration) (J0 : ℕ)
    {c c0 ν : ℝ} (hc : 0<c)
    (hlam : Tendsto (fun i => (m i).lam) l (𝓝 0))
    (hlower : ∀ᶠ i in l, ∀ j : ℕ, J0≤j →
      c*Real.exp (-c0*((j:ℝ)+1)^ν)≤(m i).eigenvalue (e i) j) :
    ∀ᶠ i in l, (1/4:ℝ)≤(m i).Q := by
  obtain ⟨i0, _⟩ := hlower.exists
  have hA := (m i0).filter_contract.constant_nonneg (m i0).lambda_pos (sq_nonneg κ)
  have hcut := exponentialResolvedCutoff_pos (ρ := ρ) (c0 := c0) (ν := ν) hA hc J0
  filter_upwards [hlower, hlam.eventually (gt_mem_nhds hcut)] with i hi hli
  exact featureFilterDimension_ge_quarter_of_lambda_le_exponential_cutoff
    (m i).feature (m i).feature_memLp (e i) J0 (m i).φ (m i).lambda_pos (m i).population_bound
    (m i).spectral_filter (m i).filter_contract hi hli.le

theorem exponential_inverse_filter_dimension_isBigO
    (m : J → SpectralScaleModel κ ρ A) (e : ∀ i, (m i).SpectrumEnumeration) (J0 : ℕ)
    {c c0 ν : ℝ} (hc : 0<c)
    (hlam : Tendsto (fun i => (m i).lam) l (𝓝 0))
    (hlower : ∀ᶠ i in l, ∀ j : ℕ, J0≤j →
      c*Real.exp (-c0*((j:ℝ)+1)^ν)≤(m i).eigenvalue (e i) j) :
    (fun i => ((m i).Q)⁻¹) =O[l] (fun i => (m i).lam^(0:ℝ)) := by
  apply IsBigO.of_bound 4
  filter_upwards [exponential_filter_dimension_lower_eventually m e J0 hc hlam hlower] with i hi
  have hQ : 0<(m i).Q := (by norm_num : (0:ℝ)<1/4).trans_le hi
  have hinv : ((m i).Q)⁻¹≤4 := by
    simpa only [one_div, inv_div, inv_one, mul_one, inv_inv] using
      one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/4) hi
  simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hQ), Real.rpow_zero, norm_one, mul_one] using hinv

/-- The original exponential-spectrum region permits every `theta > 0`.
All three exact scales are proved from the original actual-model hypotheses,
and common constants/common spectral threshold give uniform applications. -/
theorem exponential_sourceBall_original_scales
    (m : J → SpectralScaleModel κ ρ A) (e : ∀ i, (m i).SpectrumEnumeration) (J0 : ℕ)
    {θ s R c C c0 ν K : ℝ} (hθ : 0<θ) (hs : 0<s) (hR : 0<R)
    (hc : 0<c) (hC : 0<C) (hc0 : 0<c0) (hν : 0<ν)
    (hn : Tendsto (fun i => ((m i).n:ℝ)) l atTop)
    (hreg : (fun i => (m i).lam) =Θ[l] (fun i => ((m i).n:ℝ)^(-θ)))
    (hspectrum : ∀ᶠ i in l, ∀ j : ℕ, J0≤j →
      c*Real.exp (-c0*((j:ℝ)+1)^ν)≤(m i).eigenvalue (e i) j ∧
      (m i).eigenvalue (e i) j≤C*Real.exp (-c0*((j:ℝ)+1)^ν))
    (hsource : ∀ᶠ i in l, (m i).f∈(m i).SourceBall s hs.le R)
    (hleverage : ∀ᶠ i in l, (m i).L≤K*(m i).N) :
    (∀ᶠ i in l, 0<(m i).Q) ∧
      Tendsto (fun i => (m i).compatibility) l (𝓝 0) ∧
      Tendsto (fun i => (m i).sourceBalance) l (𝓝 0) ∧
      Tendsto (fun i => (m i).expectationScale) l (𝓝 0) := by
  obtain ⟨i0, _⟩ := hsource.exists
  have hα : 0<residualComparisonOrder ρ := residualComparisonOrder_pos (m i0).filter_contract.rho_pos
  let a := min s (residualComparisonOrder ρ)
  have ha : 0<a := lt_min hs hα
  obtain ⟨p, hp, hp1, hcomp, hbalance, hLP⟩ := exists_exponential_moment_exponent hθ ha
  have hupper := hspectrum.mono fun i hi j hj => (hi j hj).2
  have hlower := hspectrum.mono fun i hi j hj => (hi j hj).1
  have hlam := scale_regularization_tendsto_zero m hθ hn hreg
  have hN := exponential_effective_dimension_isBigO m e J0 hC.le hc0 hν hp hp1 hupper
  have hQlower := exponential_filter_dimension_lower_eventually m e J0 hc hlam hlower
  have hQpos : ∀ᶠ i in l, 0<(m i).Q :=
    hQlower.mono fun i hi => (by norm_num : (0:ℝ)<1/4).trans_le hi
  have hQ := exponential_inverse_filter_dimension_isBigO m e J0 hc hlam hlower
  have hL := favourable_leverage_isBigO m hN hleverage
  have hS := source_ball_energy_isBigO m hs.le hR.le hsource
  have hrow : ∀ᶠ i in l, 0<(m i).lam ∧ 0≤(m i).N ∧ 0<(m i).Q ∧ 0≤(m i).L := by
    filter_upwards [hQpos] with i hi
    exact ⟨(m i).lambda_pos, (m i).N_nonneg, hi, (m i).L_nonneg⟩
  have h := original_three_scales_of_power_bounds
    (fun i => ((m i).n:ℝ)) (fun i => (m i).lam) (fun i => (m i).N)
    (fun i => (m i).Q) (fun i => (m i).L) (fun i => (m i).S) hn hθ hp.le
    hrow hreg hN hQ hL hS (by nlinarith) (by simpa only [add_zero] using hbalance) hLP
  refine ⟨hQpos, ?_⟩
  simpa only [SpectralScaleModel.compatibility, SpectralScaleModel.sourceBalance,
    SpectralScaleModel.expectationScale] using h

end
end KernelSeq
