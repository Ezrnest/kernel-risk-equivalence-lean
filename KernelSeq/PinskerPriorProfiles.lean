import KernelSeq.PinskerVarianceAsymptotics
import KernelSeq.PinskerSpectralSumComplete

/-!
# Deterministic profiles of the Pinsker Gaussian prior

The shrinkage and source-energy profiles are the actual positive-part
functions in the prior construction. Their spectral-sum limits follow from
the original covariance counting law; no spectral moment or sum asymptotic
is supplied as an additional hypothesis.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

def pinskerPriorShrinkageProfile (s u : ℝ) : ℝ := 1 - (max u 1)^(-s/2)

def pinskerPriorEnergyProfile (s u : ℝ) : ℝ :=
  (max u 1)^(-s/2) - (max u 1)^(-s)

def pinskerPriorShrinkageConstant (s β : ℝ) : ℝ := (s*β)/(s*β+2)

def pinskerPriorEnergyConstant (s β : ℝ) : ℝ :=
  (s*β)/((s*β+1)*(s*β+2))

theorem pinskerPriorShrinkageConstant_pos {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    0 < pinskerPriorShrinkageConstant s β := by
  unfold pinskerPriorShrinkageConstant
  positivity

theorem pinskerPriorEnergyConstant_pos {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    0 < pinskerPriorEnergyConstant s β := by
  unfold pinskerPriorEnergyConstant
  positivity

theorem pinskerPriorShrinkageProfile_zero (s : ℝ) : pinskerPriorShrinkageProfile s 0 = 0 := by
  simp [pinskerPriorShrinkageProfile]

theorem pinskerPriorShrinkageProfile_of_le {s u : ℝ} (hu : u ≤ 1) :
    pinskerPriorShrinkageProfile s u = 0 := by
  simp [pinskerPriorShrinkageProfile, max_eq_right hu]

theorem pinskerPriorEnergyProfile_of_le {s u : ℝ} (hu : u ≤ 1) :
    pinskerPriorEnergyProfile s u = 0 := by
  simp [pinskerPriorEnergyProfile, max_eq_right hu]

theorem pinskerPriorShrinkageProfile_mem {s u : ℝ} (hs : 0 ≤ s) :
    pinskerPriorShrinkageProfile s u ∈ Icc (0 : ℝ) 1 := by
  have h0 := Real.rpow_nonneg (zero_le_one.trans (le_max_right u 1)) (-s/2)
  have h1 := Real.rpow_le_one_of_one_le_of_nonpos (le_max_right u 1) (by linarith : -s/2 ≤ 0)
  exact ⟨by dsimp [pinskerPriorShrinkageProfile]; linarith,
    by dsimp [pinskerPriorShrinkageProfile]; linarith⟩

theorem pinskerPriorEnergyProfile_eq_sub (s u : ℝ) :
    pinskerPriorEnergyProfile s u =
      pinskerPriorShrinkageProfile s u - pinskerVarianceProfile s u := by
  have hp : (max u 1)^(-s) = ((max u 1)^(-s/2))^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ max u 1)]
    congr 1
    norm_num
  dsimp [pinskerPriorEnergyProfile, pinskerPriorShrinkageProfile, pinskerVarianceProfile]
  rw [hp]
  ring

/-- The quarter bound is the deterministic maximal source-coordinate weight
used by the subsequent Gaussian shaving argument. -/
theorem pinskerPriorEnergyProfile_mem {s u : ℝ} (hs : 0 ≤ s) :
    pinskerPriorEnergyProfile s u ∈ Icc (0 : ℝ) (1/4) := by
  have hq := pinskerPriorShrinkageProfile_mem (u := u) hs
  rw [pinskerPriorEnergyProfile_eq_sub]
  have hv : pinskerVarianceProfile s u = (pinskerPriorShrinkageProfile s u)^2 := rfl
  rw [hv]
  constructor <;> nlinarith [hq.1, hq.2, sq_nonneg (pinskerPriorShrinkageProfile s u - 1/2)]

theorem pinskerPriorShrinkageProfile_lipschitz {s : ℝ} (hs : 0 ≤ s) :
    LipschitzWith ⟨s/2, by positivity⟩ (pinskerPriorShrinkageProfile s) := by
  have hd (z : ℝ) (hz : z ∈ Ici (1 : ℝ)) :
      HasDerivWithinAt (fun t : ℝ => t^(-s/2))
        ((-s/2)*z^(-s/2-1)) (Ici 1) z :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (zero_lt_one.trans_le hz)))).hasDerivWithinAt
  have hb (z : ℝ) (hz : z ∈ Ici (1 : ℝ)) :
      ‖(-s/2)*z^(-s/2-1)‖ ≤ s/2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith : -s/2 ≤ 0),
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hz) _)]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith : -s/2-1 ≤ 0)
    nlinarith
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.dist_eq, Real.dist_eq]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_Ici (1 : ℝ)) (le_max_right u 1) (le_max_right v 1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hm
  have he : pinskerPriorShrinkageProfile s u - pinskerPriorShrinkageProfile s v =
      (max v 1)^(-s/2) - (max u 1)^(-s/2) := by
    dsimp [pinskerPriorShrinkageProfile]
    ring
  rw [he]
  exact hm.trans (mul_le_mul_of_nonneg_left
    (by simpa only [abs_sub_comm] using abs_max_sub_max_le_abs v u 1) (by positivity))

theorem pinskerPriorShrinkageProfile_ac {s : ℝ} (hs : 0 ≤ s) (R : ℝ) :
    AbsolutelyContinuousOnInterval (pinskerPriorShrinkageProfile s) 0 R :=
  (pinskerPriorShrinkageProfile_lipschitz hs).lipschitzOnWith.absolutelyContinuousOnInterval

theorem pinskerPriorShrinkageProfile_deriv_low {s u : ℝ} (hu : u < 1) :
    deriv (pinskerPriorShrinkageProfile s) u = 0 := by
  have he : pinskerPriorShrinkageProfile s =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_lt_nhds hu] with v hv
    exact pinskerPriorShrinkageProfile_of_le hv.le
  rw [he.deriv_eq, deriv_const]

theorem pinskerPriorShrinkageProfile_deriv_high {s u : ℝ} (hu : 1 < u) :
    deriv (pinskerPriorShrinkageProfile s) u = (s/2)*u^(-s/2-1) := by
  have hpow := Real.hasDerivAt_rpow_const (p := -s/2) (Or.inl (by linarith : u ≠ 0))
  have hd : HasDerivAt (fun v : ℝ => 1-v^(-s/2)) ((s/2)*u^(-s/2-1)) u := by
    exact (hpow.const_sub 1).congr_deriv (by ring)
  have he : pinskerPriorShrinkageProfile s =ᶠ[𝓝 u] (fun v : ℝ => 1-v^(-s/2)) := by
    filter_upwards [eventually_gt_nhds hu] with v hv
    simp only [pinskerPriorShrinkageProfile, max_eq_left hv.le]
  exact he.deriv_eq.trans hd.deriv

theorem pinskerPriorShrinkageProfile_weighted_deriv_near (s γ η : ℝ) :
    IntegrableOn (fun u => u^(-γ-η)*|deriv (pinskerPriorShrinkageProfile s) u|)
      (Ioc (0 : ℝ) 1) := by
  apply (integrable_const (0 : ℝ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne (1 : ℝ))]
    with u hu hne
  rw [pinskerPriorShrinkageProfile_deriv_low (lt_of_le_of_ne hu.2 hne), abs_zero, mul_zero]

theorem pinskerPriorShrinkageProfile_weighted_deriv_far {s γ η : ℝ}
    (hs : 0 < s) (hηγ : η ≤ γ) :
    IntegrableOn (fun u => u^(-γ+η)*|deriv (pinskerPriorShrinkageProfile s) u|)
      (Ioi (1 : ℝ)) := by
  have hp : -γ+η-s/2-1 < -1 := by linarith
  apply ((integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (s/2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [pinskerPriorShrinkageProfile_deriv_high hu,
    abs_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hu0.le _)),
    mul_left_comm, ← Real.rpow_add hu0]
  congr 2
  ring

theorem pinskerPriorShrinkageProfile_integral {s γ : ℝ} (hs : 0 < s) (hγ : 0 < γ) :
    (∫ u in Ioi (0 : ℝ), u^(-γ)*deriv (pinskerPriorShrinkageProfile s) u) =
      (s/2)/(γ+s/2) := by
  have he : (fun u => u^(-γ)*deriv (pinskerPriorShrinkageProfile s) u) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (Ioi (1 : ℝ)).indicator (fun u => (s/2)*u^(-γ-s/2-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae (volume.ae_ne (1 : ℝ))]
      with u _ hne
    by_cases hu : 1 < u
    · simp only [Set.indicator, mem_Ioi, if_pos hu, pinskerPriorShrinkageProfile_deriv_high hu]
      rw [mul_left_comm, ← Real.rpow_add (zero_lt_one.trans hu)]
      congr 2
      ring
    · simp only [Set.indicator, mem_Ioi, if_neg hu,
        pinskerPriorShrinkageProfile_deriv_low (lt_of_le_of_ne (le_of_not_gt hu) hne), mul_zero]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)), integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -γ-s/2-1 < -1) zero_lt_one, Real.one_rpow]
  rw [show -γ-s/2-1+1 = -(γ+s/2) by ring]
  field_simp

theorem pinskerPriorShrinkageProfile_integral_eq_constant {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    (∫ u in Ioi (0 : ℝ), u^(-(1/β))*deriv (pinskerPriorShrinkageProfile s) u) =
      pinskerPriorShrinkageConstant s β := by
  rw [pinskerPriorShrinkageProfile_integral hs (one_div_pos.mpr hβ)]
  unfold pinskerPriorShrinkageConstant
  field_simp
  ring

theorem pinskerPriorEnergyConstant_eq_sub {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    pinskerPriorEnergyConstant s β =
      pinskerPriorShrinkageConstant s β - pinskerVarianceConstant s β := by
  unfold pinskerPriorEnergyConstant pinskerPriorShrinkageConstant pinskerVarianceConstant
  have h1 : s*β+1 ≠ 0 := ne_of_gt (by positivity)
  have h2 : s*β+2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem pinsker_shrinkage_eq_priorProfile {lam s t : ℝ} (hlam : 0 < lam) :
    ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) t =
      pinskerPriorShrinkageProfile s (t/lam) := by
  by_cases ht : t ≤ lam
  · rw [ResidualFilter.pinsker_shrinkage_eq hlam, if_pos ht,
      pinskerPriorShrinkageProfile_of_le ((div_le_one hlam).mpr ht)]
  · have hr : 1 < t/lam := (one_lt_div hlam).mpr (lt_of_not_ge ht)
    rw [ResidualFilter.pinsker_shrinkage_eq hlam, if_neg ht]
    unfold pinskerPriorShrinkageProfile
    rw [max_eq_left hr.le, show -s/2 = -(s/2) by ring,
      Real.rpow_neg_eq_inv_rpow, inv_div]

section ActualSpectrum

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Actual summability and the exact shrinkage-sum constant of the prior. -/
theorem feature_pinsker_prior_shrinkage_sum
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {β D s : ℝ} (hβ : 1 < β) (hD : 0 < D) (hs : 1 ≤ s)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) :
    (∀ lam, 0 < lam → Summable (fun j => pinskerPriorShrinkageProfile s ((e j).1.1/lam))) ∧
      Tendsto (fun lam => lam^(1/β)*∑' j, pinskerPriorShrinkageProfile s ((e j).1.1/lam))
        (𝓝[>] 0) (𝓝 (D*pinskerPriorShrinkageConstant s β)) := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hγ : 0 < 1/β := one_div_pos.mpr hβ0
  let η : ℝ := min (1/β) (1-1/β)/2
  have hη : 0 < η := by
    have hγ1 : 1/β < 1 := (div_lt_one hβ0).mpr hβ
    dsimp [η]
    exact div_pos (lt_min hγ (by linarith)) (by norm_num)
  have hηγ : η ≤ 1/β := by dsimp [η]; linarith [min_le_left (1/β) (1-1/β)]
  have hcounts : Tendsto (fun t => t^(1/β)*spectralCounting (fun j => (e j).1.1) t)
      (𝓝[>] 0) (𝓝 D) := by
    have hc := (exact_counting_limit_iff_ratio (fun t => (featureSpectralCount k hk t : ℝ)) hD.ne').mpr hcount
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [spectralCounting_eq_featureSpectralCount k hk e ht]
  have hh := pinsker_spectral_sum_complete (summable_enumerated_covariance_eigenvalues k hk e)
    (fun j => (e j).2.le) hγ hη hcounts (pinskerPriorShrinkageProfile s)
    (pinskerPriorShrinkageProfile_zero s) (fun R _ => pinskerPriorShrinkageProfile_ac hs0.le R)
    (pinskerPriorShrinkageProfile_weighted_deriv_near s (1/β) η)
    (pinskerPriorShrinkageProfile_weighted_deriv_far hs0 hηγ)
  refine ⟨hh.1, ?_⟩
  have hi := pinskerPriorShrinkageProfile_integral_eq_constant hs0 hβ0
  rw [hh.2.2.1] at hi
  have he : (D*(1/β)) * (∫ u in Ioi (0 : ℝ), pinskerPriorShrinkageProfile s u*u^(-(1/β)-1)) =
      D*pinskerPriorShrinkageConstant s β := by rw [mul_assoc, hi]
  simpa only [he] using hh.2.2.2

theorem feature_pinsker_prior_energy_sum
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {β D s : ℝ} (hβ : 1 < β) (hD : 0 < D) (hs : 1 ≤ s)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) :
    (∀ lam, 0 < lam → Summable (fun j => pinskerPriorEnergyProfile s ((e j).1.1/lam))) ∧
      Tendsto (fun lam => lam^(1/β)*∑' j, pinskerPriorEnergyProfile s ((e j).1.1/lam))
        (𝓝[>] 0) (𝓝 (D*pinskerPriorEnergyConstant s β)) := by
  have hq := feature_pinsker_prior_shrinkage_sum k hk e hβ hD hs hcount
  have hvlim := featureFilterDimension_pinsker_tendsto k hk e hβ hD hs hcount
  have hvs (lam : ℝ) (hlam : 0 < lam) :
      Summable (fun j => pinskerVarianceProfile s ((e j).1.1/lam)) := by
    have hh := summable_positive_sequence_filterDimension k hk (ResidualFilter.pinsker lam s)
      hlam (le_refl ‖populationCovariance (featureEmbedding μ k hk)‖)
      (ResidualFilter.pinsker_spectralFilter hlam (zero_le_one.trans hs))
      (ResidualFilter.pinsker_contract hlam hs)
    have he := hh.comp_injective e.injective
    exact he.congr (fun j => pinsker_shrinkage_sq_eq_varianceProfile hlam)
  have hid (lam : ℝ) (hlam : 0 < lam) :
      (∑' j, pinskerPriorEnergyProfile s ((e j).1.1/lam)) =
      (∑' j, pinskerPriorShrinkageProfile s ((e j).1.1/lam)) -
        featureFilterDimension k hk (ResidualFilter.pinsker lam s) := by
    rw [featureFilterDimension_pinsker_eq_profile_sum k hk e hlam, ← (hq.1 lam hlam).tsum_sub (hvs lam hlam)]
    exact tsum_congr (fun j => pinskerPriorEnergyProfile_eq_sub s _)
  refine ⟨fun lam hlam => ((hq.1 lam hlam).sub (hvs lam hlam)).congr
    (fun j => (pinskerPriorEnergyProfile_eq_sub s _).symm), ?_⟩
  have he : D*pinskerPriorShrinkageConstant s β - D*pinskerVarianceConstant s β =
      D*pinskerPriorEnergyConstant s β := by
    rw [pinskerPriorEnergyConstant_eq_sub (zero_lt_one.trans_le hs) (zero_lt_one.trans hβ)]
    ring
  have hh := hq.2.sub hvlim
  rw [he] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  rw [hid lam hlam, mul_sub]

end ActualSpectrum
end
end KernelSeq
