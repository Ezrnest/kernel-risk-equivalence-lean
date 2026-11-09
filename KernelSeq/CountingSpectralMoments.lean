import KernelSeq.PinskerSpectralSum
import KernelSeq.SpectralMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Spectral moments derived from exact counting

The actual counting envelope supplies all moments strictly above its power
exponent. The moment and effective-dimension bounds are conclusions, not
extra spectral assumptions. A layer-cake/Fubini argument retains explicit
common constants and does not impose an ordered eigenvalue envelope.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

/-- Signed Fubini for the actual sequence and an integrable counting kernel. -/
theorem hasSum_spectral_primitive_of_integrable_count {w : ℕ → ℝ}
    (hs : Summable w) (hw : ∀ j, 0 ≤ w j) (f : ℝ → ℝ) (hfm : Measurable f)
    (hi : IntegrableOn (fun u => spectralCounting w u * |f u|) (Ioi (0 : ℝ))) :
    HasSum (fun j => ∫ u in (0 : ℝ)..w j, f u)
      (∫ u in Ioi (0 : ℝ), spectralCounting w u * f u) := by
  let F : ℕ → ℝ → ℝ := fun j => (Iic (w j)).indicator f
  have hnorm (u : ℝ) (hu : 0 < u) : HasSum (fun j => ‖F j u‖)
      (spectralCounting w u * |f u|) := by
    convert spectralCounting_kernel_hasSum hs (by norm_num : (0 : ℝ) < 1) hu |f u| using 1
    · funext j
      simp only [F, Set.indicator, mem_Iic, div_one, Real.norm_eq_abs]
      split_ifs <;> simp
    · simp
  have hnormInt : Integrable (fun u => ∑' j, ‖F j u‖) (volume.restrict (Ioi (0 : ℝ))) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hnorm u hu).tsum_eq.symm
  have hhas : HasSum (fun j => ∫ u in Ioi (0 : ℝ), F j u)
      (∫ u in Ioi (0 : ℝ), spectralCounting w u * f u) := by
    apply hasSum_integral_of_dominated_convergence (fun j u => ‖F j u‖)
      (fun j => (hfm.indicator measurableSet_Iic).aestronglyMeasurable)
      (fun _ => Eventually.of_forall fun _ => le_rfl) ?_ hnormInt ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (hnorm u hu).summable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simpa only [F, Set.indicator, mem_Iic, div_one, one_mul] using
        spectralCounting_kernel_hasSum hs (by norm_num : (0 : ℝ) < 1) hu (f u)
  have hInt (j : ℕ) : (∫ u in Ioi (0 : ℝ), F j u) = ∫ u in (0 : ℝ)..w j, f u := by
    change (∫ u in Ioi (0 : ℝ), (Iic (w j)).indicator f u) = _
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hset : Iic (w j) ∩ Ioi (0 : ℝ) = Ioc 0 (w j) := by ext u; simp; tauto
    rw [hset, intervalIntegral.integral_of_le (hw j)]
  simpa only [hInt] using hhas

def countingMomentBound (C M γ p : ℝ) : ℝ := C * p * M ^ (p - γ) / (p - γ)

private theorem power_primitive {p a : ℝ} (hp : 0 < p) :
    (∫ u in (0 : ℝ)..a, p * u ^ (p - 1)) = a ^ p := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < p - 1))]
  rw [show p - 1 + 1 = p by ring, Real.zero_rpow hp.ne', sub_zero]
  field_simp

/-- Genuine count-layercake supplies the finite power sum with its explicit
constant, including zero spectrum and a zero spectral upper bound. -/
theorem spectral_moment_le_of_counting_power_bound {w : ℕ → ℝ}
    (hs : Summable w) (hw : ∀ j, 0 ≤ w j) {C M γ p : ℝ}
    (_hC : 0 ≤ C) (hM : 0 ≤ M) (hγ : 0 ≤ γ) (hp : γ < p)
    (hwM : ∀ j, w j ≤ M)
    (hcount : ∀ t, 0 < t → t ^ γ * spectralCounting w t ≤ C) :
    Summable (fun j => w j ^ p) ∧ (∑' j, w j ^ p) ≤ countingMomentBound C M γ p := by
  have hp0 : 0 < p := hγ.trans_lt hp
  have hpg : 0 < p - γ := sub_pos.mpr hp
  by_cases hM0 : M = 0
  · have hw0 : ∀ j, w j = 0 := fun j => le_antisymm (by simpa [hM0] using hwM j) (hw j)
    simp only [hw0, Real.zero_rpow hp0.ne', summable_zero, tsum_zero, true_and]
    simp [countingMomentBound, hM0, Real.zero_rpow hpg.ne']
  · have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    let f : ℝ → ℝ := fun u => p * u ^ (p - 1)
    let B : ℝ → ℝ := (Ioc (0 : ℝ) M).indicator (fun u => C * p * u ^ (p - γ - 1))
    have hfm : Measurable f := measurable_const.mul (measurable_id.pow_const _)
    have hBI : Integrable B (volume.restrict (Ioi (0 : ℝ))) := by
      have hi : IntegrableOn (fun u : ℝ => C * p * u ^ (p - γ - 1)) (Ioc (0 : ℝ) M) := by
        exact ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p - γ - 1)).1).const_mul (C * p)
      exact (hi.integrable_indicator measurableSet_Ioc).restrict
    have hpoint (u : ℝ) (hu : 0 < u) : spectralCounting w u * |f u| ≤ B u := by
      by_cases huM : u ≤ M
      · dsimp only [B]
        rw [indicator_of_mem (show u ∈ Ioc (0 : ℝ) M from ⟨hu, huM⟩)]
        have hcnt : spectralCounting w u ≤ C * u ^ (-γ) := by
          have hh := mul_le_mul_of_nonneg_right (hcount u hu) (Real.rpow_nonneg hu.le (-γ))
          have hc : u ^ γ * u ^ (-γ) = 1 := by rw [← Real.rpow_add hu]; simp
          calc
            _ = (u ^ γ * spectralCounting w u) * u ^ (-γ) := by
              calc
                _ = spectralCounting w u * (u ^ γ * u ^ (-γ)) := by rw [hc, mul_one]
                _ = _ := by ring
            _ ≤ _ := hh
        have huf : 0 ≤ f u := mul_nonneg hp0.le (Real.rpow_nonneg hu.le _)
        rw [abs_of_nonneg huf]
        calc
          _ ≤ (C * u ^ (-γ)) * (p * u ^ (p - 1)) :=
            mul_le_mul_of_nonneg_right hcnt huf
          _ = C * p * u ^ (p - γ - 1) := by
            rw [show p - γ - 1 = -γ + (p - 1) by ring, Real.rpow_add hu]
            ring
      · have hz : spectralCounting w u = 0 := by
          have hset : {j | u ≤ w j} = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro j hj
            exact (lt_of_not_ge huM).not_ge (hj.trans (hwM j))
          simp [spectralCounting, hset]
        rw [hz, zero_mul]
        dsimp only [B]
        rw [indicator_of_notMem (by simp only [mem_Ioc]; tauto)]
    have hcountI : IntegrableOn (fun u => spectralCounting w u * |f u|) (Ioi (0 : ℝ)) := by
      have hma : Measurable (fun u => |f u|) := by simpa only [Real.norm_eq_abs] using hfm.norm
      apply hBI.mono' ((measurable_spectralCounting w).mul hma).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (spectralCounting_nonneg _ _) (abs_nonneg _))]
      exact hpoint u hu
    have hsum := hasSum_spectral_primitive_of_integrable_count hs hw f hfm hcountI
    have hsum' : HasSum (fun j => w j ^ p) (∫ u in Ioi (0 : ℝ), spectralCounting w u * f u) := by
      simpa only [f, power_primitive hp0] using hsum
    refine ⟨hsum'.summable, ?_⟩
    rw [hsum'.tsum_eq]
    have hcountSigned : IntegrableOn (fun u => spectralCounting w u * f u) (Ioi (0 : ℝ)) := by
      apply hcountI.mono' ((measurable_spectralCounting w).mul hfm).aestronglyMeasurable
      exact Eventually.of_forall (fun u => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (spectralCounting_nonneg _ _)])
    calc
      _ ≤ ∫ u in Ioi (0 : ℝ), B u := integral_mono_ae hcountSigned hBI (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact (mul_le_mul_of_nonneg_left (le_abs_self _) (spectralCounting_nonneg _ _)).trans (hpoint u hu))
      _ = countingMomentBound C M γ p := by
        dsimp only [B]
        rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
        have hset : Ioc (0 : ℝ) M ∩ Ioi 0 = Ioc 0 M := by ext u; simp
        rw [hset, ← intervalIntegral.integral_of_le hM, intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by linarith : -1 < p - γ - 1))]
        rw [show p - γ - 1 + 1 = p - γ by ring, Real.zero_rpow hpg.ne', sub_zero]
        unfold countingMomentBound
        ring

section ActualSpectrum

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

/-- From exact counting of the actual covariance, all fractional spectral
moments above `γ` and their actual effective-dimension bounds are supplied
internally. One counting-envelope constant works for every exponent. -/
theorem exact_counting_moments_and_effective_dimension
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk)) {M γ D : ℝ}
    (hγ : 0 ≤ γ) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hcount : Tendsto (fun t => t ^ γ * (featureSpectralCount k hk t : ℝ))
      (𝓝[>] 0) (𝓝 D)) :
    ∃ C : ℝ, 0 < C ∧ ∀ p, γ < p →
      Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) => i.1.1 ^ p) ∧
      featureSpectralMoment k hk p ≤ countingMomentBound C M γ p ∧
      (∀ lam, 0 < lam → p ≤ 1 → featureEffectiveDimension k hk lam ≤
        countingMomentBound C M γ p * lam ^ (-p)) := by
  have hs := summable_enumerated_covariance_eigenvalues k hk e
  have hw : ∀ j, 0 ≤ (e j).1.1 := fun j => (e j).2.le
  have hct : Tendsto (fun t => t ^ γ * spectralCounting (fun j => (e j).1.1) t)
      (𝓝[>] 0) (𝓝 D) := by
    apply hcount.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [spectralCounting_eq_featureSpectralCount k hk e ht]
  obtain ⟨C, hC, hcb⟩ := spectralCounting_global_power_bound hs hw hγ hct
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hmom := spectral_moment_le_of_counting_power_bound hs hw hC.le
    ((norm_nonneg _).trans hM) hγ hp
    (fun j => (featureCovarianceEigenvalue_mem k hk hM (e j).1).2) hcb
  have hsum : Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) => i.1.1 ^ p) :=
    e.summable_iff.mp hmom.1
  have hmoment : featureSpectralMoment k hk p ≤ countingMomentBound C M γ p := by
    rw [featureSpectralMoment_eq_enumerated k hk e]
    exact hmom.2
  refine ⟨hsum, hmoment, ?_⟩
  intro lam hlam hp1
  exact (featureEffectiveDimension_le_fractional_moment k hk hlam (hγ.trans hp.le) hp1 hsum).trans
    (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg hlam.le (-p)))

/-- Exact actual counting and the original filter contract yield the true
filter-dimension lower bound. No eigenvalue ordering or power envelope is
added to the exact counting hypothesis. -/
theorem exact_counting_filter_dimension_lower_eventually
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    (φ : ℝ → ℝ → ℝ) {M γ D ρ A : ℝ} (hD : 0 < D)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ∀ lam, 0 < lam → ResidualFilter.SpectralFilter M (φ lam))
    (hcontract : ∀ lam, 0 < lam → ResidualFilter.Contract lam M ρ A (φ lam))
    (hcount : Tendsto (fun t => t ^ γ * (featureSpectralCount k hk t : ℝ))
      (𝓝[>] 0) (𝓝 D)) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      (D / 8 * ResidualFilter.resolvedScaleFactor ρ A ^ (-γ)) * lam ^ (-γ) ≤
        featureFilterDimension k hk (φ lam) := by
  have hA := (hcontract 1 (by norm_num)).constant_nonneg (by norm_num)
    ((norm_nonneg _).trans hM)
  let c := ResidualFilter.resolvedScaleFactor ρ A
  have hc : 0 < c := ResidualFilter.resolvedScaleFactor_pos hA
  have hct : Tendsto (fun t => t ^ γ * spectralCounting (fun j => (e j).1.1) t)
      (𝓝[>] 0) (𝓝 D) := by
    apply hcount.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [spectralCounting_eq_featureSpectralCount k hk e ht]
  have hl := spectralCounting_scaled_tendsto (w := fun j => (e j).1.1) hc hct
  have hDc : 0 < D * c ^ (-γ) := mul_pos hD (Real.rpow_pos_of_pos hc _)
  have hev := hl.eventually (lt_mem_nhds (by linarith : D * c ^ (-γ) / 2 < D * c ^ (-γ)))
  filter_upwards [self_mem_nhdsWithin, hev] with lam hlam hlow
  rw [spectralCounting_eq_featureSpectralCount k hk e (mul_pos hlam hc)] at hlow
  have hq := quarter_mul_featureSpectralCount_le_filterDimension k hk (φ lam) hlam hM
    (hfilter lam hlam) (hcontract lam hlam)
  have hp : 0 < lam ^ γ := Real.rpow_pos_of_pos hlam _
  have hqm := mul_le_mul_of_nonneg_left hq hp.le
  rw [Real.rpow_neg hlam.le, ← div_eq_mul_inv]
  apply (div_le_iff₀ hp).2
  change D / 8 * c ^ (-γ) ≤ featureFilterDimension k hk (φ lam) * lam ^ γ
  nlinarith

/-- The inverse-dimension estimate needed by the scale engine follows from
the proved actual count lower bound, rather than an extra dimension premise. -/
theorem exact_counting_inverse_filter_dimension_isBigO
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    (φ : ℝ → ℝ → ℝ) {M γ D ρ A : ℝ} (hD : 0 < D)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ∀ lam, 0 < lam → ResidualFilter.SpectralFilter M (φ lam))
    (hcontract : ∀ lam, 0 < lam → ResidualFilter.Contract lam M ρ A (φ lam))
    (hcount : Tendsto (fun t => t ^ γ * (featureSpectralCount k hk t : ℝ))
      (𝓝[>] 0) (𝓝 D)) :
    (fun lam => (featureFilterDimension k hk (φ lam))⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun lam => lam ^ γ) := by
  have hA := (hcontract 1 (by norm_num)).constant_nonneg (by norm_num)
    ((norm_nonneg _).trans hM)
  have hc := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  let b := D / 8 * ResidualFilter.resolvedScaleFactor ρ A ^ (-γ)
  have hb : 0 < b := by dsimp only [b]; positivity
  apply Asymptotics.IsBigO.of_bound b⁻¹
  filter_upwards [self_mem_nhdsWithin,
    exact_counting_filter_dimension_lower_eventually k hk e φ hD hM hfilter hcontract hcount]
    with lam hlam hlow
  have hbL : 0 < b * lam ^ (-γ) := mul_pos hb (Real.rpow_pos_of_pos hlam _)
  have hQ : 0 < featureFilterDimension k hk (φ lam) := hbL.trans_le hlow
  have hi := one_div_le_one_div_of_le hbL hlow
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hQ), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlam.le _)]
  simpa only [one_div, mul_inv_rev, Real.rpow_neg hlam.le, inv_inv, mul_comm] using hi

end ActualSpectrum

end
end KernelSeq
