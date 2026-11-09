import KernelSeq.PinskerSpectralSum
import KernelSeq.PinskerFilter
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The exact Pinsker variance constant on the actual population spectrum

The scalar profile is constructed from the exact Pinsker shrinkage. Its local
absolute continuity, derivative integrability and weighted integral are proved
below. The only spectral asymptotic premise is the original actual counting
law, with multiplicities.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

/-- The positive-part square `(1-u^(-s/2))₊²`, with its zero value at the
origin and throughout the unresolved interval. -/
def pinskerVarianceProfile (s u : ℝ) : ℝ := (1 - (max u 1)^(-s/2))^2

theorem pinskerVarianceProfile_zero (s : ℝ) : pinskerVarianceProfile s 0 = 0 := by
  simp [pinskerVarianceProfile]

theorem pinskerVarianceProfile_of_le {s u : ℝ} (hu : u ≤ 1) :
    pinskerVarianceProfile s u = 0 := by simp [pinskerVarianceProfile, max_eq_right hu]

theorem pinskerVarianceProfile_mem {s u : ℝ} (hs : 0 ≤ s) :
    pinskerVarianceProfile s u ∈ Icc (0 : ℝ) 1 := by
  have hp : 0 ≤ (max u 1)^(-s/2) := Real.rpow_nonneg (zero_le_one.trans (le_max_right _ _)) _
  have hp1 : (max u 1)^(-s/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_max_right _ _) (by linarith)
  exact ⟨sq_nonneg _, by dsimp [pinskerVarianceProfile]; nlinarith⟩

private theorem pinsker_power_sub_le {s u v : ℝ} (hs : 0 ≤ s) :
    |(max u 1)^(-s/2) - (max v 1)^(-s/2)| ≤ (s/2) * |u-v| := by
  have hd (z : ℝ) (hz : z ∈ Ici (1 : ℝ)) :
      HasDerivWithinAt (fun t : ℝ => t^(-s/2))
        ((-s/2)*z^(-s/2-1)) (Ici 1) z :=
    (Real.hasDerivAt_rpow_const (Or.inl (by exact ne_of_gt (zero_lt_one.trans_le hz) : z ≠ 0))).hasDerivWithinAt
  have hb (z : ℝ) (hz : z ∈ Ici (1 : ℝ)) :
      ‖(-s/2)*z^(-s/2-1)‖ ≤ s/2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith : -s/2 ≤ 0),
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hz) _)]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith : -s/2-1 ≤ 0)
    nlinarith
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_Ici (1 : ℝ)) (le_max_right v 1) (le_max_right u 1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs u v 1) (by positivity))

theorem pinskerVarianceProfile_lipschitz {s : ℝ} (hs : 0 ≤ s) :
    LipschitzWith ⟨s, hs⟩ (pinskerVarianceProfile s) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.dist_eq, Real.dist_eq]
  have hu0 : 0 ≤ (max u 1)^(-s/2) := Real.rpow_nonneg (by positivity) _
  have hv0 : 0 ≤ (max v 1)^(-s/2) := Real.rpow_nonneg (by positivity) _
  have hu1 := Real.rpow_le_one_of_one_le_of_nonpos (le_max_right u 1) (by linarith : -s/2 ≤ 0)
  have hv1 := Real.rpow_le_one_of_one_le_of_nonpos (le_max_right v 1) (by linarith : -s/2 ≤ 0)
  have he : pinskerVarianceProfile s u - pinskerVarianceProfile s v =
      ((max v 1)^(-s/2) - (max u 1)^(-s/2)) *
        (2-(max u 1)^(-s/2)-(max v 1)^(-s/2)) := by
    dsimp [pinskerVarianceProfile]
    ring
  have hfac : |2-(max u 1)^(-s/2)-(max v 1)^(-s/2)| ≤ 2 := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [he, abs_mul, abs_sub_comm]
  exact (mul_le_mul_of_nonneg_left hfac (abs_nonneg _)).trans
    ((mul_le_mul_of_nonneg_right (pinsker_power_sub_le hs) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by change s / 2 * |u-v| * 2 = s * |u-v|; ring))

theorem pinskerVarianceProfile_ac {s : ℝ} (hs : 0 ≤ s) (R : ℝ) :
    AbsolutelyContinuousOnInterval (pinskerVarianceProfile s) 0 R :=
  (pinskerVarianceProfile_lipschitz hs).lipschitzOnWith.absolutelyContinuousOnInterval

theorem pinskerVarianceProfile_deriv_low {s u : ℝ} (hu : u < 1) :
    deriv (pinskerVarianceProfile s) u = 0 := by
  have he : pinskerVarianceProfile s =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_lt_nhds hu] with v hv
    exact pinskerVarianceProfile_of_le hv.le
  rw [he.deriv_eq, deriv_const]

theorem pinskerVarianceProfile_deriv_high {s u : ℝ} (hu : 1 < u) :
    deriv (pinskerVarianceProfile s) u = s * (1-u^(-s/2)) * u^(-s/2-1) := by
  have hpow := Real.hasDerivAt_rpow_const (p := -s/2) (Or.inl (by linarith : u ≠ 0))
  have hd : HasDerivAt (fun v : ℝ => (1-v^(-s/2))^2)
      (s*(1-u^(-s/2))*u^(-s/2-1)) u := by
    convert! (hpow.const_sub 1).pow 2 using 1
    ring
  have he : pinskerVarianceProfile s =ᶠ[𝓝 u] (fun v : ℝ => (1-v^(-s/2))^2) := by
    filter_upwards [eventually_gt_nhds hu] with v hv
    simp only [pinskerVarianceProfile, max_eq_left hv.le]
  exact he.deriv_eq.trans hd.deriv

theorem pinskerVarianceProfile_weighted_deriv_near (s γ η : ℝ) :
    IntegrableOn (fun u => u^(-γ-η) * |deriv (pinskerVarianceProfile s) u|) (Ioc (0 : ℝ) 1) := by
  apply (integrable_const (0 : ℝ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne (1 : ℝ))]
    with u hu hne
  rw [pinskerVarianceProfile_deriv_low (lt_of_le_of_ne hu.2 hne), abs_zero, mul_zero]

theorem pinskerVarianceProfile_weighted_deriv_far {s γ η : ℝ} (hs : 0 < s) (hηγ : η ≤ γ) :
    IntegrableOn (fun u => u^(-γ+η) * |deriv (pinskerVarianceProfile s) u|) (Ioi (1 : ℝ)) := by
  have hp : -γ+η-s/2-1 < -1 := by linarith
  have hi := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul s
  have hmd : Measurable (fun u : ℝ => |deriv (pinskerVarianceProfile s) u|) := by fun_prop
  have hm : AEStronglyMeasurable
      (fun u : ℝ => u^(-γ+η) * |deriv (pinskerVarianceProfile s) u|)
      (volume.restrict (Ioi (1 : ℝ))) :=
    (((measurable_id : Measurable (fun u : ℝ => u)).pow_const _).mul hmd).aestronglyMeasurable
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hp0 := Real.rpow_nonneg hu0.le (-s/2)
  have hp1 := Real.rpow_le_one_of_one_le_of_nonpos hu.le (by linarith : -s/2 ≤ 0)
  rw [pinskerVarianceProfile_deriv_high hu, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu0.le _) (abs_nonneg _)),
    abs_of_nonneg (by positivity : 0 ≤ s*(1-u^(-s/2))*u^(-s/2-1))]
  calc
    _ ≤ s * (u^(-γ+η) * u^(-s/2-1)) := by
      have ht := mul_le_mul_of_nonneg_right (sub_le_self 1 hp0)
        (mul_nonneg (Real.rpow_nonneg hu0.le (-γ+η))
          (mul_nonneg hs.le (Real.rpow_nonneg hu0.le (-s/2-1))))
      nlinarith only [ht]
    _ = s * u^(-γ+η-s/2-1) := by rw [← Real.rpow_add hu0]; congr 2; ring

theorem pinskerVarianceProfile_boundary_zero (s γ : ℝ) :
    Tendsto (fun u => u^(-γ) * pinskerVarianceProfile s u) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1) |>.filter_mono nhdsWithin_le_nhds]
    with u hu
  rw [pinskerVarianceProfile_of_le hu.le, mul_zero]

theorem pinskerVarianceProfile_boundary_infty {s γ : ℝ} (hs : 0 ≤ s) (hγ : 0 < γ) :
    Tendsto (fun u => u^(-γ) * pinskerVarianceProfile s u) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (tendsto_rpow_neg_atTop hγ)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu _) (pinskerVarianceProfile_mem hs).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact (mul_le_mul_of_nonneg_left (pinskerVarianceProfile_mem hs).2
      (Real.rpow_nonneg hu _)).trans_eq (mul_one _)

private theorem pinskerVarianceProfile_weighted_deriv_eq {s γ u : ℝ} (hu : 1 < u) :
    u^(-γ) * deriv (pinskerVarianceProfile s) u =
      s*u^(-γ-s/2-1) - s*u^(-γ-s-1) := by
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [pinskerVarianceProfile_deriv_high hu]
  have he1 : u^(-γ-s/2-1) = u^(-γ)*u^(-s/2-1) := by
    rw [← Real.rpow_add hu0]; congr 1; ring
  have he2 : u^(-γ-s-1) = u^(-γ)*u^(-s/2)*u^(-s/2-1) := by
    rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]; congr 1; ring
  rw [he1, he2]
  ring

/-- The scalar integral giving the exact Pinsker variance constant. -/
theorem pinskerVarianceProfile_integral {s γ : ℝ} (hs : 0 < s) (hγ : 0 < γ) :
    (∫ u in Ioi (0 : ℝ), u^(-γ) * deriv (pinskerVarianceProfile s) u) =
      s/(γ+s/2) - s/(γ+s) := by
  have he : (fun u => u^(-γ) * deriv (pinskerVarianceProfile s) u) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (Ioi (1 : ℝ)).indicator (fun u => s*u^(-γ-s/2-1) - s*u^(-γ-s-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae (volume.ae_ne (1 : ℝ))]
      with u _ hne
    by_cases hu : 1 < u
    · simp only [Set.indicator, mem_Ioi, if_pos hu, pinskerVarianceProfile_weighted_deriv_eq hu]
    · simp only [Set.indicator, mem_Ioi, if_neg hu,
        pinskerVarianceProfile_deriv_low (lt_of_le_of_ne (le_of_not_gt hu) hne), mul_zero]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  have h1 := (integrableOn_Ioi_rpow_of_lt (by linarith : -γ-s/2-1 < -1) zero_lt_one).const_mul s
  have h2 := (integrableOn_Ioi_rpow_of_lt (by linarith : -γ-s-1 < -1) zero_lt_one).const_mul s
  rw [integral_sub h1 h2, integral_const_mul, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -γ-s/2-1 < -1) zero_lt_one,
    integral_Ioi_rpow_of_lt (by linarith : -γ-s-1 < -1) zero_lt_one,
    Real.one_rpow, Real.one_rpow]
  rw [show -γ-s/2-1+1 = -(γ+s/2) by ring, show -γ-s-1+1 = -(γ+s) by ring]
  simp only [neg_div_neg_eq, one_div]
  ring

/-- The manuscript's exact Pinsker variance constant. -/
def pinskerVarianceConstant (s β : ℝ) : ℝ :=
  (s*β)^2 / ((s*β+1)*(s*β+2))

theorem pinskerVarianceConstant_pos {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    0 < pinskerVarianceConstant s β := by
  unfold pinskerVarianceConstant
  positivity

theorem pinskerVarianceProfile_integral_eq_constant {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    (∫ u in Ioi (0 : ℝ), u^(-(1/β)) * deriv (pinskerVarianceProfile s) u) =
      pinskerVarianceConstant s β := by
  rw [pinskerVarianceProfile_integral hs (one_div_pos.mpr hβ)]
  unfold pinskerVarianceConstant
  field_simp
  ring

theorem pinsker_shrinkage_sq_eq_varianceProfile {lam s t : ℝ} (hlam : 0 < lam) :
    ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) t ^ 2 =
      pinskerVarianceProfile s (t/lam) := by
  by_cases ht : t ≤ lam
  · rw [ResidualFilter.pinsker_shrinkage_eq hlam, if_pos ht,
      pinskerVarianceProfile_of_le ((div_le_one hlam).mpr ht)]
    norm_num
  · have htl : lam < t := lt_of_not_ge ht
    have hr : 1 < t/lam := (one_lt_div hlam).mpr htl
    rw [ResidualFilter.pinsker_shrinkage_eq hlam, if_neg ht]
    unfold pinskerVarianceProfile
    rw [max_eq_left hr.le, show -s/2 = -(s/2) by ring,
      Real.rpow_neg_eq_inv_rpow, inv_div]

section ActualSpectrum

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

omit [TopologicalSpace.SeparableSpace H] in
theorem featureFilterDimension_pinsker_eq_profile_sum
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {lam s : ℝ} (hlam : 0 < lam) :
    featureFilterDimension k hk (ResidualFilter.pinsker lam s) =
      ∑' j, pinskerVarianceProfile s ((e j).1.1/lam) := by
  rw [featureFilterDimension_eq_positive_sequence]
  calc
    _ = ∑' j, ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) (e j).1.1 ^ 2 :=
      (e.tsum_eq _).symm
    _ = _ := tsum_congr (fun _ => pinsker_shrinkage_sq_eq_varianceProfile hlam)

/-- The precise Pinsker variance asymptotic from the original exact
population counting law. All profile analysis and the actual series bridge
are proved internally; no dimension or spectral-sum estimate is assumed. -/
theorem featureFilterDimension_pinsker_tendsto
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {β D s : ℝ} (hβ : 1 < β) (hD : 0 < D) (hs : 1 ≤ s)
    (hcount : Tendsto
      (fun t => (featureSpectralCount k hk t : ℝ) / (D * t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun lam => lam^(1/β) * featureFilterDimension k hk (ResidualFilter.pinsker lam s))
      (𝓝[>] 0) (𝓝 (D * pinskerVarianceConstant s β)) := by
  have hβ0 : 0 < β := by linarith
  have hγ : 0 < 1/β := one_div_pos.mpr hβ0
  have hγ1 : 1/β < 1 := (div_lt_one hβ0).mpr hβ
  let η : ℝ := min (1/β) (1-1/β) / 2
  have hmin : 0 < min (1/β) (1-1/β) := lt_min hγ (by linarith)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηγ : η ≤ 1/β := by
    dsimp [η]
    linarith [min_le_left (1/β) (1-1/β)]
  have hcountNorm : Tendsto (fun t => t^(1/β) * (featureSpectralCount k hk t : ℝ))
      (𝓝[>] 0) (𝓝 D) :=
    (exact_counting_limit_iff_ratio (fun t => (featureSpectralCount k hk t : ℝ)) hD.ne').mpr hcount
  have hlim := feature_spectral_sum_tendsto_derivative k hk e hγ hη hcountNorm
    (pinskerVarianceProfile s) (pinskerVarianceProfile_zero s)
    (fun R _ => pinskerVarianceProfile_ac (by linarith : 0 ≤ s) R)
    (pinskerVarianceProfile_weighted_deriv_near s (1/β) η)
    (pinskerVarianceProfile_weighted_deriv_far (by linarith : 0 < s) hηγ)
  rw [pinskerVarianceProfile_integral_eq_constant (by linarith : 0 < s) hβ0] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  rw [featureFilterDimension_pinsker_eq_profile_sum k hk e hlam]

/-- The equivalent asymptotic-ratio convention used in the manuscript. -/
theorem featureFilterDimension_pinsker_ratio_tendsto
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {β D s : ℝ} (hβ : 1 < β) (hD : 0 < D) (hs : 1 ≤ s)
    (hcount : Tendsto
      (fun t => (featureSpectralCount k hk t : ℝ) / (D * t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun lam => featureFilterDimension k hk (ResidualFilter.pinsker lam s) /
      ((D * pinskerVarianceConstant s β) * lam^(-(1/β)))) (𝓝[>] 0) (𝓝 1) := by
  apply (exact_counting_limit_iff_ratio _
    (mul_pos hD (pinskerVarianceConstant_pos (by linarith) (by linarith))).ne').mp
  exact featureFilterDimension_pinsker_tendsto k hk e hβ hD hs hcount

end ActualSpectrum

end
end KernelSeq
