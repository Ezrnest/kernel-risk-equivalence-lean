import KernelSeq.EmpiricalEffectiveDimension
import KernelSeq.ContinuousCompactCalculus
import KernelSeq.RHSFluctuation

/-!
# Actual good-event empirical effective-dimension second moment

The leverage second-moment bound for an independent, identically distributed sample.
The true sample leverage average has second moment at most `N₁²+LN₁/n`.
The actual empirical spectral dimension is strongly measurable, proved by
its finite resolvent-energy formula, and its good-event second moment is
at most four times that sample-mean bound. No independence between the
covariance deviation and the empirical dimension is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {Ω X H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {μ : Measure X} [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The true finite resolvent-energy representation, including n=0. -/
theorem empiricalEffectiveDimension_eq_mean_resolvent_inner {n : ℕ} (z : Fin n → H)
    (lam : ℝ) (hlam : 0 < lam) :
    empiricalEffectiveDimension z lam = (n : ℝ)⁻¹ * ∑ i,
      inner ℝ (z i) (Ring.inverse (empiricalCovariance z + lam • (1 : H →L[ℝ] H)) (z i)) := by
  rw [empiricalEffectiveDimension_eq_mean_invSqrt_norm_sq z lam hlam]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let R := compactRegularizedInvSqrt (empiricalCovariance z)
    (empiricalCovariance_isCompact z) (empiricalCovariance_isPositive z) lam
  have ha : R.adjoint = R :=
    (compactRegularizedInvSqrt_isSelfAdjoint _ _ _ _).adjoint_eq
  have hsq := compactRegularizedInvSqrt_sq (empiricalCovariance z)
    (empiricalCovariance_isCompact z) (empiricalCovariance_isPositive z) lam hlam
  change ‖R (z i)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, ← R.adjoint_inner_right, ha]
  change inner ℝ (z i) ((R * R) (z i)) = _
  rw [hsq]

/-- Actual measurability of the empirical dimension. Only strong feature
measurability is used; the ambient operator space need not be separable. -/
theorem stronglyMeasurable_empiricalEffectiveDimension {n : ℕ}
    (z : Fin n → Ω → H) (hz : ∀ i, StronglyMeasurable (z i))
    (lam : ℝ) (hlam : 0 < lam) :
    StronglyMeasurable (fun ω => empiricalEffectiveDimension (fun i => z i ω) lam) := by
  have hT := stronglyMeasurable_empiricalCovariance z hz
  have hR := stronglyMeasurable_regularizedInverse (fun ω => empiricalCovariance (fun i => z i ω))
    hT (fun _ => empiricalCovariance_isPositive _) lam hlam
  have hi (i : Fin n) : StronglyMeasurable (fun ω => inner ℝ (z i ω)
      (Ring.inverse (empiricalCovariance (fun j => z j ω) + lam • (1 : H →L[ℝ] H)) (z i ω))) :=
    (hz i).inner (stronglyMeasurable_operator_apply _ hR _ (hz i))
  have heq : (fun ω => empiricalEffectiveDimension (fun i => z i ω) lam) =
      (n : ℝ)⁻¹ • ∑ i, fun ω => inner ℝ (z i ω)
        (Ring.inverse (empiricalCovariance (fun j => z j ω) + lam • (1 : H →L[ℝ] H)) (z i ω)) := by
    funext ω
    simp only [empiricalEffectiveDimension_eq_mean_resolvent_inner _ lam hlam,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [heq]
  exact (Finset.stronglyMeasurable_sum Finset.univ (fun i _ => hi i)).const_smul (n : ℝ)⁻¹

/-- A bounded actual normalized leverage is genuinely L². -/
theorem memLp_normalizedLeverage {L lam : ℝ} (k : X → H) (hk : MemLp k 2 μ)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    MemLp (normalizedLeverage k hk lam) 2 μ := by
  apply MemLp.of_bound (integrable_normalizedLeverage k hk lam).1 L
  filter_upwards [hL] with y hy
  have hp : 0 ≤ normalizedLeverage k hk lam y := sq_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using hy

omit [IsProbabilityMeasure P] in
/-- The actual bounded leverage average is L² even without independence. -/
theorem memLp_sampleMeanNormalizedLeverage {n : ℕ}
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    MemLp (fun ω => sampleMeanNormalizedLeverage k hk lam (fun i => x i ω)) 2 P := by
  have hu := memLp_normalizedLeverage k hk hL
  simpa only [sampleMeanNormalizedLeverage, Finset.sum_apply, Function.comp_apply] using
    (memLp_finsetSum' Finset.univ (fun i _ => hu.comp_measurePreserving (hlaw i))).const_mul (n : ℝ)⁻¹

variable [TopologicalSpace.SeparableSpace H]

/-- The actual iid population-whitened sample average has the correct
second moment scale, derived from centered Hilbert second moments. -/
theorem integral_sampleMeanNormalizedLeverage_sq_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hind : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    (∫ ω, sampleMeanNormalizedLeverage k hk lam (fun i => x i ω) ^ 2 ∂P) ≤
      featureEffectiveDimension k hk lam ^ 2 +
        L / (n : ℝ) * featureEffectiveDimension k hk lam := by
  let u := normalizedLeverage k hk lam
  let D := featureEffectiveDimension k hk lam
  let B : Ω → ℝ := fun ω => sampleMeanNormalizedLeverage k hk lam (fun i => x i ω)
  have hu : MemLp u 2 μ := memLp_normalizedLeverage k hk hL
  have hB : MemLp B 2 P := memLp_sampleMeanNormalizedLeverage x hlaw k hk lam hL
  have humean : (∫ y, u y ∂μ) = D := integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam
  have hmean : (∫ ω, B ω ∂P) = D := integral_sampleMeanNormalizedLeverage hn x hlaw k hk lam hlam
  have hcent := integral_norm_sq_centered_sample_le hn x hlaw hind u hu
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he (ω : Ω) : (n : ℝ)⁻¹ • ∑ i, (u (x i ω) - ∫ y, u y ∂μ) = B ω - D := by
    rw [humean]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
    dsimp only [B, sampleMeanNormalizedLeverage, u]
    field_simp
  simp_rw [he, Real.norm_eq_abs, sq_abs] at hcent
  have hpoly : (∫ ω, (B ω - D) ^ 2 ∂P) = (∫ ω, B ω ^ 2 ∂P) - D ^ 2 := by
    have heq : (fun ω => (B ω - D) ^ 2) =
        (fun ω => B ω ^ 2 - 2 * D * B ω + D ^ 2) := by funext ω; ring
    have he₁ := integral_add (hB.integrable_sq.sub ((hB.integrable (by norm_num)).const_mul (2 * D)))
      (integrable_const (D ^ 2))
    have he₂ := integral_sub hB.integrable_sq ((hB.integrable (by norm_num)).const_mul (2 * D))
    dsimp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂
    rw [heq, he₁, he₂, integral_const_mul, hmean]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [hpoly] at hcent
  have hu2 : (∫ y, u y ^ 2 ∂μ) ≤ L * D := by
    calc
      _ ≤ ∫ y, L * u y ∂μ := integral_mono_ae hu.integrable_sq
        ((hu.integrable (by norm_num)).const_mul L) (by
          filter_upwards [hL] with y hy
          have hu0 : 0 ≤ u y := sq_nonneg _
          change u y ≤ L at hy
          nlinarith)
      _ = _ := by rw [integral_const_mul, humean]
  have ht := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ (n : ℝ)⁻¹)
  change (∫ ω, B ω ^ 2 ∂P) ≤ D ^ 2 + L / (n : ℝ) * D
  rw [div_eq_mul_inv]
  nlinarith

omit [IsProbabilityMeasure P] [TopologicalSpace.SeparableSpace H] in
/-- The true empirical spectral dimension is L² on every measurable subset
of the covariance quarter-event. Its L² existence is derived from the
actual resolvent formula and the sample-mean domination. -/
theorem memLp_empiricalEffectiveDimension_on_good {n : ℕ}
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (lam : ℝ) (hlam : 0 < lam) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (G : Set Ω) (hG : MeasurableSet G)
    (hgood : ∀ ω ∈ G, sampleCovarianceDeviation k hk lam (fun i => x i ω) ≤ 1 / 4) :
    MemLp (fun ω => empiricalEffectiveDimension (fun i => k (x i ω)) lam) 2 (P.restrict G) := by
  have hB := (memLp_sampleMeanNormalizedLeverage x hlaw k hk lam hL).restrict G
  have hN : AEStronglyMeasurable
      (fun ω => empiricalEffectiveDimension (fun i => k (x i ω)) lam) (P.restrict G) :=
    (stronglyMeasurable_empiricalEffectiveDimension (fun i ω => k (x i ω))
    (fun i => hks.comp_measurable (hlaw i).measurable) lam hlam).aestronglyMeasurable
  apply (hB.const_mul 2).mono hN
  filter_upwards [ae_restrict_mem hG] with ω hω
  have hp : 0 ≤ empiricalEffectiveDimension (fun i => k (x i ω)) lam := by
    apply tsum_nonneg
    intro i
    have ht := compactEigenvalue_nonneg _ (empiricalCovariance_isCompact (fun i => k (x i ω)))
      (empiricalCovariance_isPositive _) i
    exact div_nonneg ht (add_nonneg ht hlam.le)
  have hb := empiricalEffectiveDimension_le_two_sampleMean k hk lam hlam (fun i => x i ω) (hgood ω hω)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sampleMeanNormalizedLeverage_nonneg k hk lam _))] using hb

/-- The good-event empirical effective-dimension second-moment bound used
in the expectation proof. All spectral measurability and L² facts above
are proved; independence is used only in the genuine iid average moment. -/
theorem setIntegral_empiricalEffectiveDimension_sq_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hind : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (lam : ℝ) (hlam : 0 < lam) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (G : Set Ω) (hG : MeasurableSet G)
    (hgood : ∀ ω ∈ G, sampleCovarianceDeviation k hk lam (fun i => x i ω) ≤ 1 / 4) :
    (∫ ω in G, empiricalEffectiveDimension (fun i => k (x i ω)) lam ^ 2 ∂P) ≤
      4 * (featureEffectiveDimension k hk lam ^ 2 +
        L / (n : ℝ) * featureEffectiveDimension k hk lam) := by
  let B : Ω → ℝ := fun ω => sampleMeanNormalizedLeverage k hk lam (fun i => x i ω)
  have hB : MemLp B 2 P := memLp_sampleMeanNormalizedLeverage x hlaw k hk lam hL
  have hN := memLp_empiricalEffectiveDimension_on_good x hlaw k hk hks lam hlam hL G hG hgood
  have hsq : ∀ᵐ ω ∂P.restrict G,
      empiricalEffectiveDimension (fun i => k (x i ω)) lam ^ 2 ≤ 4 * B ω ^ 2 := by
    filter_upwards [ae_restrict_mem hG] with ω hω
    have hp : 0 ≤ empiricalEffectiveDimension (fun i => k (x i ω)) lam := by
      apply tsum_nonneg
      intro i
      have ht := compactEigenvalue_nonneg _ (empiricalCovariance_isCompact (fun i => k (x i ω)))
        (empiricalCovariance_isPositive _) i
      exact div_nonneg ht (add_nonneg ht hlam.le)
    have hb := empiricalEffectiveDimension_le_two_sampleMean k hk lam hlam (fun i => x i ω) (hgood ω hω)
    have hB0 : 0 ≤ B ω := sampleMeanNormalizedLeverage_nonneg k hk lam _
    change empiricalEffectiveDimension (fun i => k (x i ω)) lam ≤ 2 * B ω at hb
    nlinarith
  calc
    _ ≤ ∫ ω in G, 4 * B ω ^ 2 ∂P :=
      integral_mono_ae hN.integrable_sq ((hB.restrict G).integrable_sq.const_mul 4) hsq
    _ = 4 * ∫ ω in G, B ω ^ 2 ∂P := integral_const_mul _ _
    _ ≤ 4 * ∫ ω, B ω ^ 2 ∂P := mul_le_mul_of_nonneg_left
      (integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hB.integrable_sq) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_sampleMeanNormalizedLeverage_sq_le hn x hlaw hind k hk lam hlam hL) (by norm_num)

end
end KernelSeq
