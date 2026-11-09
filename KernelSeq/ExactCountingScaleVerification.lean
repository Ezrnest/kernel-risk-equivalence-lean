import KernelSeq.CountingSpectralMoments
import KernelSeq.SourceBall
import KernelSeq.PowerScaleVerification
import KernelSeq.PowerExponentChoice

/-!
# Original three scales under exact population counting

The feature map and design law are fixed, while the target, regularization
and sample size may vary over an arbitrary index filter (including a uniform
family filter). Exact counting supplies all spectral moment and dimension
estimates internally. No ordered eigenvalue envelope, fractional moment,
dimension estimate, or scale conclusion is a hypothesis.
-/

namespace KernelSeq

open MeasureTheory Filter Topology Asymptotics
noncomputable section

variable {X H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]
  {l : Filter J}

/-- Exact polynomial counting and the original universal-leverage source
condition imply all three manuscript scales for the actual fixed feature
model. The full original region is `0 < theta < 1` and
`min(s,alpha) > 1-1/beta`. -/
theorem exact_counting_universal_sourceBall_original_scales
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {κ ρ A β D θ s R : ℝ} (hκ : 0 ≤ κ) (hkbound : ∀ x, ‖k x‖ ≤ κ)
    (hβ : 1 < β) (hD : 0 < D) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs : 0 < s) (hR : 0 < R)
    (hsmooth : 1 - 1 / β < min s (residualComparisonOrder ρ))
    (φ : ℝ → ℝ → ℝ)
    (hfilter : ∀ lam, 0 < lam → ResidualFilter.SpectralFilter (κ ^ 2) (φ lam))
    (hcontract : ∀ lam, 0 < lam → ResidualFilter.Contract lam (κ ^ 2) ρ A (φ lam))
    (hcount : Tendsto
      (fun t => (featureSpectralCount k hk t : ℝ) / (D * t ^ (-(1 / β))))
      (𝓝[>] 0) (𝓝 1))
    (n : J → ℕ) (_hnpos : ∀ i, 0 < n i)
    (hn : Tendsto (fun i => (n i : ℝ)) l atTop)
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    (hreg : lam =Θ[l] (fun i => (n i : ℝ) ^ (-θ)))
    (f : J → Lp ℝ 2 μ)
    (hsource : ∀ i, f i ∈ featureSourceBall k hk s hs.le R) :
    let N := fun i => featureEffectiveDimension k hk (lam i)
    let Q := fun i => featureFilterDimension k hk (φ (lam i))
    let L := fun i => featureLeverageEssentialSup k hk (lam i)
    let S := fun i => featureSequenceSourceEnergy k hk (lam i) (residualComparisonOrder ρ) (f i)
    (∀ᶠ i in l, 0 < Q i) ∧
      Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / (n i : ℝ))) l (𝓝 0) ∧
      Tendsto (fun i => (n i : ℝ) * S i * originalBiasGamma (L i) (n i : ℝ) (N i) ^ 2 / Q i)
        l (𝓝 0) ∧
      Tendsto (fun i => L i / (n i : ℝ) *
        Real.log (Real.exp 1 + (n i : ℝ) / (lam i * Q i))) l (𝓝 0) := by
  let N := fun i => featureEffectiveDimension k hk (lam i)
  let Q := fun i => featureFilterDimension k hk (φ (lam i))
  let L := fun i => featureLeverageEssentialSup k hk (lam i)
  let S := fun i => featureSequenceSourceEnergy k hk (lam i) (residualComparisonOrder ρ) (f i)
  change (∀ᶠ i in l, 0 < Q i) ∧ _
  have hβ0 : 0 < β := by linarith
  have hγ : 0 < 1 / β := one_div_pos.mpr hβ0
  have hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ κ ^ 2 :=
    featureCovariance_norm_le k hk κ hκ (Eventually.of_forall hkbound)
  have hkb : ∀ᵐ x ∂μ, ‖k x‖ ^ 2 ≤ κ ^ 2 := Eventually.of_forall fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (hkbound x) 2
  have hα : 0 < residualComparisonOrder ρ :=
    residualComparisonOrder_pos (hcontract 1 (by norm_num)).rho_pos
  obtain ⟨p, hp, hp1, hpβ, hcomp, hbalance⟩ :=
    exists_universal_polynomial_moment_exponent hβ hθ hθ1 hsmooth
  have hgp : 1 / β < p := (div_lt_iff₀ hβ0).2 (by simpa only [one_mul, mul_comm] using hpβ)
  have hcountNorm : Tendsto (fun t => t ^ (1 / β) * (featureSpectralCount k hk t : ℝ))
      (𝓝[>] 0) (𝓝 D) :=
    (exact_counting_limit_iff_ratio (fun t => (featureSpectralCount k hk t : ℝ)) hD.ne').mpr hcount
  obtain ⟨C, _, hmom⟩ := exact_counting_moments_and_effective_dimension k hk e hγ.le hM hcountNorm
  have hmoment := hmom p hgp
  have hlam0 : Tendsto lam l (𝓝 0) :=
    hreg.tendsto_zero_iff.mpr ((tendsto_rpow_neg_atTop hθ).comp hn)
  have hlamGT : Tendsto lam l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlam0, Eventually.of_forall hlam⟩
  have hQinv : (fun i => (Q i)⁻¹) =O[l] (fun i => lam i ^ (1 / β)) :=
    (exact_counting_inverse_filter_dimension_isBigO k hk e φ hD hM hfilter hcontract hcountNorm).comp_tendsto hlamGT
  have hA := (hcontract 1 (by norm_num)).constant_nonneg (by norm_num) (sq_nonneg κ)
  have hc := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  have hB : 0 < D / 8 * ResidualFilter.resolvedScaleFactor ρ A ^ (-(1 / β)) := by positivity
  have hQpos : ∀ᶠ i in l, 0 < Q i := by
    filter_upwards [hlamGT.eventually
      (exact_counting_filter_dimension_lower_eventually k hk e φ hD hM hfilter hcontract hcountNorm)]
      with i hi
    exact (mul_pos hB (Real.rpow_pos_of_pos (hlam i) _)).trans_le hi
  have hN : N =O[l] (fun i => lam i ^ (-p)) := by
    apply IsBigO.of_bound (countingMomentBound C (κ ^ 2) (1 / β) p)
    filter_upwards [] with i
    rw [Real.norm_eq_abs, abs_of_nonneg (featureEffectiveDimension_nonneg k hk _ (hlam i)),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hlam i).le _)]
    exact hmoment.2.2 (lam i) (hlam i) hp1
  have hL : L =O[l] (fun i => lam i ^ (-(1 : ℝ))) := by
    apply IsBigO.of_bound (κ ^ 2)
    filter_upwards [] with i
    rw [Real.norm_eq_abs, abs_of_nonneg (featureLeverageEssentialSup_nonneg k hk (hlam i) hkb),
      Real.norm_eq_abs, Real.rpow_neg_one, abs_of_pos (inv_pos.mpr (hlam i))]
    simpa only [div_eq_mul_inv] using featureLeverageEssentialSup_le_sq_bound_div k hk (hlam i) hkb
  have hS : S =O[l] (fun i => lam i ^ (min s (residualComparisonOrder ρ))) := by
    apply IsBigO.of_bound ((1 + κ ^ 2) ^ (s - min s (residualComparisonOrder ρ)) * R ^ 2)
    filter_upwards [] with i
    rw [Real.norm_eq_abs, abs_of_nonneg (featureSequenceSourceEnergy_nonneg k hk (hlam i) (f i)),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hlam i).le _)]
    exact featureSequenceSourceEnergy_le_sourceBall k hk hs.le hα.le hR.le (hlam i) hM (hsource i)
  have hrow : ∀ᶠ i in l, 0 < lam i ∧ 0 ≤ N i ∧ 0 < Q i ∧ 0 ≤ L i := by
    filter_upwards [hQpos] with i hi
    exact ⟨hlam i, featureEffectiveDimension_nonneg k hk _ (hlam i), hi,
      featureLeverageEssentialSup_nonneg k hk (hlam i) hkb⟩
  have hscales := original_three_scales_of_power_bounds
    (fun i => (n i : ℝ)) lam N Q L S hn hθ hp.le hrow hreg hN hQinv hL hS
    (by simpa only [div_eq_mul_inv, one_mul] using hcomp) hbalance
    (by simpa only [mul_one] using hθ1)
  exact ⟨hQpos, hscales⟩

end
end KernelSeq
