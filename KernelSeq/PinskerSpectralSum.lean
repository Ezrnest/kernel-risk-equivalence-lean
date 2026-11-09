import KernelSeq.SpectralSumIntegral

/-!
# Exact polynomial-counting spectral-sum asymptotics

The counting integral and its domination are derived from the actual sequence
and exact counting hypothesis. The derivative hypotheses are precisely the
two original weighted absolute-integrability conditions, not pointwise
smoothness or a prescribed spectral-sum limit.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

theorem integrable_weighted_deriv_of_two_weights {G : ℝ → ℝ} {γ η : ℝ} (hη : 0 ≤ η)
    (hnear : IntegrableOn (fun u => u ^ (-γ - η) * |deriv G u|) (Ioc (0 : ℝ) 1))
    (hfar : IntegrableOn (fun u => u ^ (-γ + η) * |deriv G u|) (Ioi (1 : ℝ))) :
    IntegrableOn (fun u => u ^ (-γ) * |deriv G u|) (Ioi (0 : ℝ)) := by
  have hma : Measurable (fun u => |deriv G u|) := by
    simpa only [Real.norm_eq_abs] using (measurable_deriv G).norm
  have hm : StronglyMeasurable (fun u : ℝ => u ^ (-γ) * |deriv G u|) :=
    ((measurable_id.pow_const (-γ)).mul hma).stronglyMeasurable
  have hn : IntegrableOn (fun u => u ^ (-γ) * |deriv G u|) (Ioc (0 : ℝ) 1) := by
    apply hnear.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu.1.le _), abs_abs]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2 (by linarith)) (abs_nonneg _)
  have hf : IntegrableOn (fun u => u ^ (-γ) * |deriv G u|) (Ioi (1 : ℝ)) := by
    apply hfar.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hu.le) _), abs_abs]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hu.le (by linarith)) (abs_nonneg _)
  have hset : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext u
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hu, _⟩ | hu) <;> linarith
    · intro hu
      rcases le_total u 1 with h | h
      · exact Or.inl ⟨hu, h⟩
      · by_cases he : u = 1
        · exact Or.inl ⟨hu, he.le⟩
        · exact Or.inr (lt_of_le_of_ne h (Ne.symm he))
  rw [← hset]
  exact hn.union hf

theorem spectralCounting_scaled_le {w : ℕ → ℝ} {γ C lam u : ℝ}
    (hlam : 0 < lam) (hu : 0 < u)
    (hbound : ∀ t, 0 < t → t ^ γ * spectralCounting w t ≤ C) :
    lam ^ γ * spectralCounting w (lam * u) ≤ C * u ^ (-γ) := by
  have hpow : u ^ γ * u ^ (-γ) = 1 := by rw [← Real.rpow_add hu]; simp
  calc
    _ = ((lam * u) ^ γ * spectralCounting w (lam * u)) * u ^ (-γ) := by
      rw [Real.mul_rpow hlam.le hu.le]
      symm
      calc
        _ = (lam ^ γ * spectralCounting w (lam * u)) * (u ^ γ * u ^ (-γ)) := by ring
        _ = _ := by rw [hpow, mul_one]
    _ ≤ C * u ^ (-γ) := mul_le_mul_of_nonneg_right (hbound _ (mul_pos hlam hu))
      (Real.rpow_nonneg hu.le _)

theorem integrable_count_deriv_of_power_bound {w : ℕ → ℝ} {G : ℝ → ℝ} {γ C lam : ℝ}
    (hlam : 0 < lam)
    (hbound : ∀ t, 0 < t → t ^ γ * spectralCounting w t ≤ C)
    (hi : IntegrableOn (fun u => u ^ (-γ) * |deriv G u|) (Ioi (0 : ℝ))) :
    IntegrableOn (fun u => spectralCounting w (lam * u) * |deriv G u|) (Ioi (0 : ℝ)) := by
  have hma : Measurable (fun u => |deriv G u|) := by
    simpa only [Real.norm_eq_abs] using (measurable_deriv G).norm
  have hm : AEStronglyMeasurable (fun u => spectralCounting w (lam * u) * |deriv G u|)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((measurable_spectralCounting w).comp (measurable_const.mul measurable_id)).mul
      hma).aestronglyMeasurable
  have hh := (hi.const_mul C).const_mul (lam ^ γ)⁻¹
  apply hh.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (spectralCounting_nonneg _ _) (abs_nonneg _))]
  have hb := spectralCounting_scaled_le hlam hu hbound
  have hbp := mul_le_mul_of_nonneg_right hb (abs_nonneg (deriv G u))
  have hLp := Real.rpow_pos_of_pos hlam γ
  have h := mul_le_mul_of_nonneg_left hbp (inv_nonneg.mpr hLp.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hLp.ne', one_mul] using h

/-- The spectral-sum identity and limit under exact counting and weighted
a.e. derivative integrability. -/
theorem pinsker_spectral_sum_tendsto_derivative {w : ℕ → ℝ}
    (hs : Summable w) (hw : ∀ j, 0 ≤ w j) {γ D η : ℝ}
    (hγ : 0 < γ) (hη : 0 < η)
    (hcount : Tendsto (fun t => t ^ γ * spectralCounting w t) (𝓝[>] 0) (𝓝 D))
    (G : ℝ → ℝ) (hG0 : G 0 = 0)
    (hac : ∀ R, 0 ≤ R → AbsolutelyContinuousOnInterval G 0 R)
    (hnear : IntegrableOn (fun u => u ^ (-γ - η) * |deriv G u|) (Ioc (0 : ℝ) 1))
    (hfar : IntegrableOn (fun u => u ^ (-γ + η) * |deriv G u|) (Ioi (1 : ℝ))) :
    Tendsto (fun lam => lam ^ γ * ∑' j, G (w j / lam)) (𝓝[>] 0)
      (𝓝 (D * ∫ u in Ioi (0 : ℝ), u ^ (-γ) * deriv G u)) := by
  obtain ⟨C, _, hC⟩ := spectralCounting_global_power_bound hs hw hγ.le hcount
  have hi := integrable_weighted_deriv_of_two_weights hη.le hnear hfar
  have hm (lam : ℝ) : AEStronglyMeasurable
      (fun u => lam ^ γ * spectralCounting w (lam * u) * deriv G u)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_const.mul ((measurable_spectralCounting w).comp
      (measurable_const.mul measurable_id))).mul (measurable_deriv G)).aestronglyMeasurable
  have hlim : Tendsto
      (fun lam => ∫ u in Ioi (0 : ℝ), lam ^ γ * spectralCounting w (lam * u) * deriv G u)
      (𝓝[>] 0) (𝓝 (∫ u in Ioi (0 : ℝ), (D * u ^ (-γ)) * deriv G u)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun u => C * (u ^ (-γ) * |deriv G u|))
      (Eventually.of_forall hm) ?_ (hi.const_mul C) ?_
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hlam.le _) (spectralCounting_nonneg _ _))]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (spectralCounting_scaled_le hlam hu hC) (abs_nonneg (deriv G u))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (spectralCounting_scaled_tendsto hu hcount).mul_const (deriv G u)
  have hInt : (∫ u in Ioi (0 : ℝ), (D * u ^ (-γ)) * deriv G u) =
      D * ∫ u in Ioi (0 : ℝ), u ^ (-γ) * deriv G u := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  rw [hInt] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  rw [spectral_sum_eq_counting_integral hs hw hlam G hG0 hac
    (integrable_count_deriv_of_power_bound hlam hC hi), ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun u => by ring)

section ActualSpectrum

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The spectral-sum limit is applied to the actual covariance eigenvalues,
with the original actual counting function as the sole spectral asymptotic
hypothesis. No limit or domination of a surrogate sequence is supplied. -/
theorem feature_spectral_sum_tendsto_derivative
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk)) {γ D η : ℝ}
    (hγ : 0 < γ) (hη : 0 < η)
    (hcount : Tendsto (fun t => t ^ γ * (featureSpectralCount k hk t : ℝ))
      (𝓝[>] 0) (𝓝 D))
    (G : ℝ → ℝ) (hG0 : G 0 = 0)
    (hac : ∀ R, 0 ≤ R → AbsolutelyContinuousOnInterval G 0 R)
    (hnear : IntegrableOn (fun u => u ^ (-γ - η) * |deriv G u|) (Ioc (0 : ℝ) 1))
    (hfar : IntegrableOn (fun u => u ^ (-γ + η) * |deriv G u|) (Ioi (1 : ℝ))) :
    Tendsto (fun lam => lam ^ γ * ∑' j, G ((e j).1.1 / lam)) (𝓝[>] 0)
      (𝓝 (D * ∫ u in Ioi (0 : ℝ), u ^ (-γ) * deriv G u)) := by
  apply pinsker_spectral_sum_tendsto_derivative
    (summable_enumerated_covariance_eigenvalues k hk e) (fun j => (e j).2.le) hγ hη ?_
    G hG0 hac hnear hfar
  apply hcount.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [spectralCounting_eq_featureSpectralCount k hk e ht]

end ActualSpectrum

/-- Multiplicative exact counting and its normalized-power formulation are
equivalent, so the spectral-sum hypothesis is the original asymptotic one. -/
theorem exact_counting_limit_iff_ratio (N : ℝ → ℝ) {γ D : ℝ} (hD : D ≠ 0) :
    Tendsto (fun t => t ^ γ * N t) (𝓝[>] 0) (𝓝 D) ↔
      Tendsto (fun t => N t / (D * t ^ (-γ))) (𝓝[>] 0) (𝓝 1) := by
  have heq : (fun t => N t / (D * t ^ (-γ))) =ᶠ[𝓝[>] 0]
      (fun t => (t ^ γ * N t) / D) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Real.rpow_neg ht.le]
    field_simp
  constructor
  · intro h
    have hh := h.div_const D
    rw [div_self hD] at hh
    exact hh.congr' heq.symm
  · intro h
    have hh := (h.congr' heq).mul_const D
    simpa only [one_mul, div_mul_cancel₀ _ hD] using hh

end
end KernelSeq
