import KernelSeq.MixedPerturbation
import KernelSeq.VarianceTraceComparison

/-!
# The actual empirical effective dimension on the covariance good event

The empirical spectral sum is first identified with the actual average of
squared whitened sample features. The constructed root transition bounds it
by twice the population-whitened average on the covariance good event.
The latter average has exactly the population effective dimension as its
expectation, giving outer-measure Markov bounds without an assumed stochastic
order or a measurability certificate for the empirical spectral sum.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace KernelSeq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual inverse root of the empirical covariance plus regularization. -/
noncomputable def empiricalRegularizedInvSqrt {n : ℕ} (z : Fin n → H) (lam : ℝ) : H →L[ℝ] H :=
  compactRegularizedInvSqrt (empiricalCovariance z) (empiricalCovariance_isCompact z)
    (empiricalCovariance_isPositive z) lam

/-- Each empirical inverse-root variance column has the actual effective-
dimension weight. The zero eigenspace contributes exactly zero. -/
theorem empiricalInvSqrtVariance_column_energy {n : ℕ} (z : Fin n → H)
    (lam : ℝ) (hlam : 0 < lam) (i : EmpiricalCovarianceIndex z) :
    ‖empiricalVarianceColumns z (empiricalRegularizedInvSqrt z lam)
      (empiricalCovarianceBasis z) i‖ ^ 2 = i.1 / (i.1 + lam) := by
  have ht := compactEigenvalue_nonneg (empiricalCovariance z)
    (empiricalCovariance_isCompact z) (empiricalCovariance_isPositive z) i
  have hsqrt : compactRegularizedSqrt (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) 0 (empiricalCovarianceBasis z i) =
        Real.sqrt i.1 • empiricalCovarianceBasis z i := by
    simpa only [empiricalCovarianceBasis, add_zero] using compactRegularizedSqrt_eigenbasis (empiricalCovariance z)
      (empiricalCovariance_isCompact z) (empiricalCovariance_isPositive z) 0 i
  have hinv : compactRegularizedInvSqrt (empiricalCovariance z) (empiricalCovariance_isCompact z)
      (empiricalCovariance_isPositive z) lam (empiricalCovarianceBasis z i) =
        (Real.sqrt (i.1 + lam))⁻¹ • empiricalCovarianceBasis z i :=
    compactRegularizedInvSqrt_eigenbasis _ _ _ lam hlam i
  rw [empiricalVarianceColumns_apply]
  change ‖empiricalRegularizedInvSqrt z lam (compactRegularizedSqrt (empiricalCovariance z)
    (empiricalCovariance_isCompact z) (empiricalCovariance_isPositive z) 0
      (empiricalCovarianceBasis z i))‖ ^ 2 = _
  rw [hsqrt, map_smul]
  change ‖Real.sqrt i.1 • compactRegularizedInvSqrt (empiricalCovariance z)
    (empiricalCovariance_isCompact z) (empiricalCovariance_isPositive z) lam
      (empiricalCovarianceBasis z i)‖ ^ 2 = _
  rw [hinv]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt ht, Real.sq_sqrt (add_nonneg ht hlam.le),
    (empiricalCovarianceBasis z).orthonormal.norm_eq_one, mul_one]
  rfl

/-- The spectral empirical effective dimension is exactly the finite mean of
actual empirical-whitened feature energies, including the empty-sample convention. -/
theorem empiricalEffectiveDimension_eq_mean_invSqrt_norm_sq {n : ℕ} (z : Fin n → H)
    (lam : ℝ) (hlam : 0 < lam) :
    empiricalEffectiveDimension z lam =
      (n : ℝ)⁻¹ * ∑ i, ‖empiricalRegularizedInvSqrt z lam (z i)‖ ^ 2 := by
  calc
    empiricalEffectiveDimension z lam =
        ‖empiricalVarianceColumns z (empiricalRegularizedInvSqrt z lam) (empiricalCovarianceBasis z)‖ ^ 2 := by
      rw [hsColumns_norm_sq, empiricalEffectiveDimension]
      apply tsum_congr
      intro i
      exact (empiricalInvSqrtVariance_column_energy z lam hlam i).symm
    _ = _ := empiricalVarianceColumns_norm_sq z _ _

/-- Exact transition identity in the orientation needed to bound every
empirical-whitened sample vector by its population-whitened counterpart. -/
theorem invSqrt_eq_rootTransition_adjoint_mul (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    compactRegularizedInvSqrt TX hcX hpX lam =
      (rootTransition T TX hc hcX hp hpX lam).adjoint * compactRegularizedInvSqrt T hc hp lam := by
  symm
  simp only [rootTransition, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    (compactRegularizedInvSqrt_isSelfAdjoint TX hcX hpX lam).adjoint_eq,
    (compactRegularizedSqrt_isSelfAdjoint T hc hp lam).adjoint_eq]
  change compactRegularizedInvSqrt TX hcX hpX lam * compactRegularizedSqrt T hc hp lam *
    compactRegularizedInvSqrt T hc hp lam = _
  rw [mul_assoc, compactRegularizedSqrt_mul_invSqrt T hc hp lam hlam, mul_one]

/-- The actual roots give the pointwise energy comparison on the good event;
no inverse-order functional calculus is assumed. -/
theorem invSqrt_apply_norm_sq_le_two (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 2) (v : H) :
    ‖compactRegularizedInvSqrt TX hcX hpX lam v‖ ^ 2 ≤
      2 * ‖compactRegularizedInvSqrt T hc hp lam v‖ ^ 2 := by
  have htr := rootTransition_norm_le T TX hc hcX hp hpX lam hlam hδ
  have htradj : ‖(rootTransition T TX hc hcX hp hpX lam).adjoint‖ ≤ Real.sqrt 2 := by
    simpa only [LinearIsometryEquiv.norm_map] using htr
  have hnorm : ‖compactRegularizedInvSqrt TX hcX hpX lam v‖ ≤
      Real.sqrt 2 * ‖compactRegularizedInvSqrt T hc hp lam v‖ := by
    rw [invSqrt_eq_rootTransition_adjoint_mul T TX hc hcX hp hpX lam hlam, mul_apply_eq_comp]
    exact (rootTransition T TX hc hcX hp hpX lam).adjoint.le_of_opNorm_le htradj _
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2

section ActualSample

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual population-whitened sample average, whose expectation is `N₁`. -/
noncomputable def sampleMeanNormalizedLeverage (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {n : ℕ} (x : Fin n → X) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, normalizedLeverage k hk lam (x i)

theorem sampleMeanNormalizedLeverage_nonneg (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {n : ℕ} (x : Fin n → X) : 0 ≤ sampleMeanNormalizedLeverage k hk lam x := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The actual covariance deviation defining the manuscript's good event. -/
noncomputable def sampleCovarianceDeviation (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {n : ℕ} (x : Fin n → X) : ℝ :=
  ‖featureRegularizedInvSqrt μ k hk lam *
    (empiricalCovariance (fun i => k (x i)) - populationCovariance (featureEmbedding μ k hk)) *
      featureRegularizedInvSqrt μ k hk lam‖

/-- The manuscript's deterministic good-event effective-dimension comparison. -/
theorem empiricalEffectiveDimension_le_two_sampleMean (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hδ : ‖featureRegularizedInvSqrt μ k hk lam *
      (empiricalCovariance (fun i => k (x i)) - populationCovariance (featureEmbedding μ k hk)) *
        featureRegularizedInvSqrt μ k hk lam‖ ≤ 1 / 4) :
    empiricalEffectiveDimension (fun i => k (x i)) lam ≤
      2 * sampleMeanNormalizedLeverage k hk lam x := by
  have hpoint (i : Fin n) :
      ‖empiricalRegularizedInvSqrt (fun j => k (x j)) lam (k (x i))‖ ^ 2 ≤
        2 * normalizedLeverage k hk lam (x i) := by
    apply invSqrt_apply_norm_sq_le_two (populationCovariance (featureEmbedding μ k hk))
      (empiricalCovariance (fun j => k (x j))) (populationCovariance_feature_isCompact μ k hk)
      (empiricalCovariance_isCompact _) (populationCovariance_isPositive _)
      (empiricalCovariance_isPositive _) lam hlam
    exact hδ.trans (by norm_num)
  rw [empiricalEffectiveDimension_eq_mean_invSqrt_norm_sq _ lam hlam]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i, 2 * normalizedLeverage k hk lam (x i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint i)) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; unfold sampleMeanNormalizedLeverage; ring

/-- The true sample leverage average is integrable solely from the individual
design laws and the population L² feature; independence is unnecessary here. -/
theorem integrable_sampleMeanNormalizedLeverage {n : ℕ} (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ) (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    Integrable (fun ω => sampleMeanNormalizedLeverage k hk lam (fun i => x i ω)) P := by
  have hi (i : Fin n) : Integrable (fun ω => normalizedLeverage k hk lam (x i ω)) P :=
    (hlaw i).integrable_comp_of_integrable (integrable_normalizedLeverage k hk lam)
  exact (integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul (n : ℝ)⁻¹

variable [TopologicalSpace.SeparableSpace H]

/-- The actual sample mean has precisely the population effective dimension as
expectation. Positive sample size is explicit; no inverse of `N₁` is taken. -/
theorem integral_sampleMeanNormalizedLeverage {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) :
    (∫ ω, sampleMeanNormalizedLeverage k hk lam (fun i => x i ω) ∂P) =
      featureEffectiveDimension k hk lam := by
  have hi (i : Fin n) : Integrable (fun ω => normalizedLeverage k hk lam (x i ω)) P :=
    (hlaw i).integrable_comp_of_integrable (integrable_normalizedLeverage k hk lam)
  have hmean (i : Fin n) : (∫ ω, normalizedLeverage k hk lam (x i ω) ∂P) =
      ∫ y, normalizedLeverage k hk lam y ∂μ := by
    have h := integral_map (hlaw i).aemeasurable
      (show AEStronglyMeasurable (normalizedLeverage k hk lam) (Measure.map (x i) P) by
        rw [(hlaw i).map_eq]
        exact (integrable_normalizedLeverage k hk lam).1)
    rw [(hlaw i).map_eq] at h
    exact h.symm
  change (∫ ω, (n : ℝ)⁻¹ * ∑ i, normalizedLeverage k hk lam (x i ω) ∂P) = _
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [hmean]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul,
    integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam]

/-- A good-event tail bound for the actual empirical spectral sum. The event
may be nonmeasurable; the measure is its outer measure. The formula includes
`N₁ = 0` because no division by the effective dimension occurs. -/
theorem measure_empiricalEffectiveDimension_good_ge_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam)
    {t : ℝ} (ht : 0 < t) :
    P {ω | sampleCovarianceDeviation k hk lam (fun i => x i ω) ≤ 1 / 4 ∧
      t ≤ empiricalEffectiveDimension (fun i => k (x i ω)) lam} ≤
        ENNReal.ofReal (2 * featureEffectiveDimension k hk lam / t) := by
  let M : Ω → ℝ := fun ω => sampleMeanNormalizedLeverage k hk lam (fun i => x i ω)
  have hi : Integrable M P := integrable_sampleMeanNormalizedLeverage x hlaw k hk lam
  have hnonneg (ω : Ω) : 0 ≤ M ω := sampleMeanNormalizedLeverage_nonneg k hk lam _
  have hm := (hi.const_mul (2 / t)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (div_nonneg (by norm_num) ht.le) (hnonneg ω)))
    (s := {ω | sampleCovarianceDeviation k hk lam (fun i => x i ω) ≤ 1 / 4 ∧
      t ≤ empiricalEffectiveDimension (fun i => k (x i ω)) lam}) (fun ω hω => by
        have hb := empiricalEffectiveDimension_le_two_sampleMean k hk lam hlam
          (fun i => x i ω) hω.1
        have htm : t ≤ 2 * M ω := hω.2.trans hb
        rw [show (2 / t) * M ω = (2 * M ω) / t by ring, le_div_iff₀ ht]
        simpa only [one_mul] using htm)
  rw [integral_const_mul, integral_sampleMeanNormalizedLeverage hn x hlaw k hk lam hlam] at hm
  convert hm using 1
  congr 1
  ring

/-- The complete outer tail bound is the covariance bad-event probability plus
the proved Markov term, rather than an assumed empirical-dimension rate. -/
theorem measure_empiricalEffectiveDimension_ge_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam)
    {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ empiricalEffectiveDimension (fun i => k (x i ω)) lam} ≤
      P {ω | 1 / 4 < sampleCovarianceDeviation k hk lam (fun i => x i ω)} +
        ENNReal.ofReal (2 * featureEffectiveDimension k hk lam / t) := by
  have hsubset : {ω | t ≤ empiricalEffectiveDimension (fun i => k (x i ω)) lam} ⊆
      {ω | 1 / 4 < sampleCovarianceDeviation k hk lam (fun i => x i ω)} ∪
        {ω | sampleCovarianceDeviation k hk lam (fun i => x i ω) ≤ 1 / 4 ∧
          t ≤ empiricalEffectiveDimension (fun i => k (x i ω)) lam} := by
    intro ω hω
    by_cases hgood : sampleCovarianceDeviation k hk lam (fun i => x i ω) ≤ 1 / 4
    · exact Or.inr ⟨hgood, hω⟩
    · exact Or.inl (lt_of_not_ge hgood)
  exact ((measure_mono hsubset).trans (measure_union_le _ _)).trans (add_le_add le_rfl
    (measure_empiricalEffectiveDimension_good_ge_le hn x hlaw k hk lam hlam ht))

end ActualSample

end KernelSeq
