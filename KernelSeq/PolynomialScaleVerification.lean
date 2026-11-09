import KernelSeq.PolynomialScaleBounds
import KernelSeq.PowerScaleVerification

/-!
# Original polynomial-spectrum scale regions

The hypotheses are bounds on the actual eigenvalues, the actual power-source
ball, regularization comparison and the manuscript leverage condition. All
fractional moments, dimensions, source energy and logarithmic estimates are
supplied internally. The parameter set may be encoded in the index filter,
so common input constants give the original uniform conclusions as well.
-/

open MeasureTheory Filter Topology Asymptotics

namespace KernelSeq
noncomputable section

variable {J : Type*} {l : Filter J} [NeBot l] {κ ρ A : ℝ}

/-- Polynomial eigenvalue decay with favourable leverage: precisely the
original region `0 < theta < beta`, for every positive source smoothness. -/
theorem polynomial_sourceBall_original_scales
    (m : J → SpectralScaleModel κ ρ A) (e : ∀ i, (m i).SpectrumEnumeration)
    {β θ s R c C K : ℝ} (hβ : 1 < β) (hθ : 0 < θ) (hθβ : θ < β)
    (hs : 0 < s) (hR : 0 < R) (hc : 0 < c) (hC : 0 < C)
    (hn : Tendsto (fun i => ((m i).n : ℝ)) l atTop)
    (hreg : (fun i => (m i).lam) =Θ[l] (fun i => ((m i).n : ℝ) ^ (-θ)))
    (hspectrum : ∀ᶠ i in l, ∀ j : ℕ,
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).eigenvalue (e i) j ∧
      (m i).eigenvalue (e i) j ≤ C * ((j : ℝ) + 1) ^ (-β))
    (hsource : ∀ᶠ i in l, (m i).f ∈ (m i).SourceBall s hs.le R)
    (hleverage : ∀ᶠ i in l, (m i).L ≤ K * (m i).N) :
    (∀ᶠ i in l, 0 < (m i).Q) ∧
      Tendsto (fun i => (m i).compatibility) l (𝓝 0) ∧
      Tendsto (fun i => (m i).sourceBalance) l (𝓝 0) ∧
      Tendsto (fun i => (m i).expectationScale) l (𝓝 0) := by
  obtain ⟨i0, _⟩ := hsource.exists
  have hα : 0 < residualComparisonOrder ρ :=
    residualComparisonOrder_pos (m i0).filter_contract.rho_pos
  let a := min s (residualComparisonOrder ρ)
  have ha : 0 < a := lt_min hs hα
  obtain ⟨p, hp, hp1, hpβ, hcomp, hbalance, hLP⟩ :=
    exists_favourable_polynomial_moment_exponent hβ hθ hθβ ha
  have hlower := hspectrum.mono fun i hi j => (hi j).1
  have hupper := hspectrum.mono fun i hi j => (hi j).2
  have hlam := scale_regularization_tendsto_zero m hθ hn hreg
  have hβ0 : 0 < β := by linarith
  have hQpos := polynomial_filter_dimension_pos_eventually m e hβ0 hc hlam hlower
  have hN := polynomial_effective_dimension_isBigO m e hC.le hp.le hp1 hpβ hupper
  have hQ := polynomial_inverse_filter_dimension_isBigO m e hβ0 hc hlam hlower
  have hL := favourable_leverage_isBigO m hN hleverage
  have hS := source_ball_energy_isBigO m hs.le hR.le hsource
  have hrow : ∀ᶠ i in l, 0 < (m i).lam ∧ 0 ≤ (m i).N ∧ 0 < (m i).Q ∧ 0 ≤ (m i).L := by
    filter_upwards [hQpos] with i hi
    exact ⟨(m i).lambda_pos, (m i).N_nonneg, hi, (m i).L_nonneg⟩
  have hcomp' : θ * (2 * p + p - 2 * (1 / β)) < 1 := by
    convert hcomp using 1
    ring
  have h := original_three_scales_of_power_bounds
    (fun i => ((m i).n : ℝ)) (fun i => (m i).lam) (fun i => (m i).N)
    (fun i => (m i).Q) (fun i => (m i).L) (fun i => (m i).S) hn hθ hp.le
    hrow hreg hN hQ hL hS hcomp' hbalance hLP
  refine ⟨hQpos, ?_⟩
  simpa only [SpectralScaleModel.compatibility, SpectralScaleModel.sourceBalance,
    SpectralScaleModel.expectationScale] using h

/-- Polynomial eigenvalue decay under the universal leverage bound. The
only additional smoothness restriction is the original `min(s,alpha)>1-1/beta`. -/
theorem polynomial_universal_sourceBall_original_scales
    (m : J → SpectralScaleModel κ ρ A) (e : ∀ i, (m i).SpectrumEnumeration)
    {β θ s R c C : ℝ} (hβ : 1 < β) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs : 0 < s) (hR : 0 < R) (hc : 0 < c) (hC : 0 < C)
    (hsmooth : 1 - 1 / β < min s (residualComparisonOrder ρ))
    (hn : Tendsto (fun i => ((m i).n : ℝ)) l atTop)
    (hreg : (fun i => (m i).lam) =Θ[l] (fun i => ((m i).n : ℝ) ^ (-θ)))
    (hspectrum : ∀ᶠ i in l, ∀ j : ℕ,
      c * ((j : ℝ) + 1) ^ (-β) ≤ (m i).eigenvalue (e i) j ∧
      (m i).eigenvalue (e i) j ≤ C * ((j : ℝ) + 1) ^ (-β))
    (hsource : ∀ᶠ i in l, (m i).f ∈ (m i).SourceBall s hs.le R) :
    (∀ᶠ i in l, 0 < (m i).Q) ∧
      Tendsto (fun i => (m i).compatibility) l (𝓝 0) ∧
      Tendsto (fun i => (m i).sourceBalance) l (𝓝 0) ∧
      Tendsto (fun i => (m i).expectationScale) l (𝓝 0) := by
  obtain ⟨p, hp, hp1, hpβ, hcomp, hbalance⟩ :=
    exists_universal_polynomial_moment_exponent hβ hθ hθ1 hsmooth
  have hlower := hspectrum.mono fun i hi j => (hi j).1
  have hupper := hspectrum.mono fun i hi j => (hi j).2
  have hlam := scale_regularization_tendsto_zero m hθ hn hreg
  have hβ0 : 0 < β := by linarith
  have hQpos := polynomial_filter_dimension_pos_eventually m e hβ0 hc hlam hlower
  have hN := polynomial_effective_dimension_isBigO m e hC.le hp.le hp1 hpβ hupper
  have hQ := polynomial_inverse_filter_dimension_isBigO m e hβ0 hc hlam hlower
  have hL := universal_leverage_isBigO (l := l) m
  have hS := source_ball_energy_isBigO m hs.le hR.le hsource
  have hrow : ∀ᶠ i in l, 0 < (m i).lam ∧ 0 ≤ (m i).N ∧ 0 < (m i).Q ∧ 0 ≤ (m i).L := by
    filter_upwards [hQpos] with i hi
    exact ⟨(m i).lambda_pos, (m i).N_nonneg, hi, (m i).L_nonneg⟩
  have hcomp' : θ * (2 * p + 1 - 2 * (1 / β)) < 1 := by
    convert hcomp using 1
    ring
  have h := original_three_scales_of_power_bounds
    (fun i => ((m i).n : ℝ)) (fun i => (m i).lam) (fun i => (m i).N)
    (fun i => (m i).Q) (fun i => (m i).L) (fun i => (m i).S) hn hθ hp.le
    hrow hreg hN hQ hL hS hcomp' hbalance (by simpa only [mul_one] using hθ1)
  refine ⟨hQpos, ?_⟩
  simpa only [SpectralScaleModel.compatibility, SpectralScaleModel.sourceBalance,
    SpectralScaleModel.expectationScale] using h

end
end KernelSeq
