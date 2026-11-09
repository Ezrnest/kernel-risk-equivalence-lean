import KernelSeq.PinskerShavedOracle
import KernelSeq.PinskerOracleBenchmark

/-!
# Actual deterministic Pinsker prior variances and source energy

The variance is constructed from the proven positive-part energy profile.
Its equality to the original inverse-shrinkage formula, posterior shrinkage,
and exact sequence risk/source-energy duality are conclusions.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

def pinskerPriorVariance (lam s eps2 t : ℝ) : ℝ :=
  eps2*t^s*lam^(-s)*pinskerPriorEnergyProfile s (t/lam)

theorem pinskerPriorVariance_of_le {lam s eps2 t : ℝ} (hlam : 0 < lam) (ht : t ≤ lam) :
    pinskerPriorVariance lam s eps2 t = 0 := by
  rw [pinskerPriorVariance, pinskerPriorEnergyProfile_of_le ((div_le_one hlam).mpr ht), mul_zero]

theorem pinskerPriorVariance_eq_original {lam s eps2 t : ℝ} (hlam : 0 < lam) (ht : lam < t) :
    pinskerPriorVariance lam s eps2 t = eps2*((t/lam)^(s/2)-1) := by
  have ht0 : 0 < t := hlam.trans ht
  have hu : 0 < t/lam := div_pos ht0 hlam
  have hu1 : 1 < t/lam := (one_lt_div hlam).mpr ht
  have hrat : t^s*lam^(-s) = (t/lam)^s := by
    rw [Real.div_rpow ht0.le hlam.le, Real.rpow_neg hlam.le, div_eq_mul_inv]
  have he1 : (t/lam)^s*(t/lam)^(-s/2) = (t/lam)^(s/2) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  have he2 : (t/lam)^s*(t/lam)^(-s) = 1 := by
    rw [← Real.rpow_add hu, add_neg_cancel, Real.rpow_zero]
  unfold pinskerPriorVariance pinskerPriorEnergyProfile
  rw [max_eq_left hu1.le]
  calc
    _ = eps2*((t^s*lam^(-s))*((t/lam)^(-s/2)-(t/lam)^(-s))) := by ring
    _ = _ := by rw [hrat, mul_sub, he1, he2]

theorem pinskerPriorVariance_nonneg {lam s eps2 t : ℝ}
    (hlam : 0 < lam) (hs : 0 ≤ s) (heps : 0 ≤ eps2) (ht : 0 ≤ t) :
    0 ≤ pinskerPriorVariance lam s eps2 t := by
  exact mul_nonneg (mul_nonneg (mul_nonneg heps (Real.rpow_nonneg ht _))
    (Real.rpow_nonneg hlam.le _)) (pinskerPriorEnergyProfile_mem hs).1

theorem pinskerPriorVariance_pos {lam s eps2 t : ℝ}
    (hlam : 0 < lam) (hs : 0 < s) (heps : 0 < eps2) (ht : lam < t) :
    0 < pinskerPriorVariance lam s eps2 t := by
  rw [pinskerPriorVariance_eq_original hlam ht]
  exact mul_pos heps (sub_pos.mpr (Real.one_lt_rpow ((one_lt_div hlam).mpr ht) (by positivity)))

theorem pinskerPriorVariance_source_weight {lam s eps2 t : ℝ} (ht : 0 < t) :
    t^(-s)*pinskerPriorVariance lam s eps2 t =
      eps2*lam^(-s)*pinskerPriorEnergyProfile s (t/lam) := by
  have he : t^(-s)*t^s = 1 := by rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero]
  unfold pinskerPriorVariance
  calc
    _ = (t^(-s)*t^s)*eps2*lam^(-s)*pinskerPriorEnergyProfile s (t/lam) := by ring
    _ = _ := by rw [he, one_mul]

theorem pinskerPriorVariance_source_weight_le {lam s eps2 t : ℝ}
    (hlam : 0 < lam) (hs : 0 ≤ s) (heps : 0 ≤ eps2) (ht : 0 < t) :
    t^(-s)*pinskerPriorVariance lam s eps2 t ≤ eps2*lam^(-s)/4 := by
  rw [pinskerPriorVariance_source_weight ht]
  have hh := mul_le_mul_of_nonneg_left (pinskerPriorEnergyProfile_mem (u := t/lam) hs).2
    (mul_nonneg heps (Real.rpow_nonneg hlam.le (-s)))
  simpa only [mul_one_div] using hh

theorem pinskerPriorVariance_posterior {lam s eps2 t : ℝ}
    (hlam : 0 < lam) (heps : 0 < eps2) :
    pinskerPriorVariance lam s eps2 t / (pinskerPriorVariance lam s eps2 t+eps2) =
      ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) t := by
  rw [pinsker_shrinkage_eq_priorProfile hlam]
  by_cases ht : t ≤ lam
  · rw [pinskerPriorVariance_of_le hlam ht,
      pinskerPriorShrinkageProfile_of_le ((div_le_one hlam).mpr ht), zero_div]
  · have htl : lam < t := lt_of_not_ge ht
    have hu : 0 < t/lam := div_pos (hlam.trans htl) hlam
    have hp : 0 < (t/lam)^(s/2) := Real.rpow_pos_of_pos hu _
    rw [pinskerPriorVariance_eq_original hlam htl]
    unfold pinskerPriorShrinkageProfile
    rw [max_eq_left ((one_lt_div hlam).mpr htl).le, show -s/2 = -(s/2) by ring,
      Real.rpow_neg hu.le]
    field_simp [heps.ne', hp.ne']
    ring

/-- Exact variance/source-energy duality at each actual positive eigenvalue. -/
theorem pinskerPriorVariance_duality {lam s eps2 t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    eps2*ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) t =
      eps2*(ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) t)^2+
        lam^s*(t^(-s)*pinskerPriorVariance lam s eps2 t) := by
  rw [pinsker_shrinkage_eq_priorProfile hlam, pinskerPriorVariance_source_weight ht,
    pinskerPriorEnergyProfile_eq_sub]
  have hv : pinskerVarianceProfile s (t/lam) = (pinskerPriorShrinkageProfile s (t/lam))^2 := rfl
  rw [hv]
  have hl : lam^s*lam^(-s) = 1 := by rw [← Real.rpow_add hlam, add_neg_cancel, Real.rpow_zero]
  have hc : lam^s*(eps2*lam^(-s)*(pinskerPriorShrinkageProfile s (t/lam)-
      (pinskerPriorShrinkageProfile s (t/lam))^2)) =
      eps2*(pinskerPriorShrinkageProfile s (t/lam)-(pinskerPriorShrinkageProfile s (t/lam))^2) := by
    calc
      _ = (lam^s*lam^(-s))*eps2*(pinskerPriorShrinkageProfile s (t/lam)-
          (pinskerPriorShrinkageProfile s (t/lam))^2) := by ring
      _ = _ := by rw [hl, one_mul]
  rw [hc]
  ring

section ActualSpectrum

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

def featurePinskerPriorSourceEnergy (k : X → H) (hk : MemLp k 2 μ)
    (lam s eps2 : ℝ) : ℝ :=
  ∑' i : PredictionSingularIndex (featureEmbedding μ k hk),
    i.1.1^(-s)*pinskerPriorVariance lam s eps2 i.1.1

def featurePinskerPriorSequenceRisk (k : X → H) (hk : MemLp k 2 μ)
    (lam s eps2 : ℝ) : ℝ :=
  eps2 * ∑' i : PredictionSingularIndex (featureEmbedding μ k hk),
    ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) i.1.1

/-- The actual finite active set, with equality to the threshold omitted
exactly as in the prior construction. -/
def featurePinskerPriorActiveFinset (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    Finset (PredictionSingularIndex (featureEmbedding μ k hk)) := by
  classical
  exact if h : 0 < lam then (finite_featureSpectrum_above k hk h).toFinset.filter
    (fun i => lam < i.1.1) else ∅

theorem mem_featurePinskerPriorActiveFinset
    (k : X → H) (hk : MemLp k 2 μ) {lam : ℝ} (hlam : 0 < lam)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
    i ∈ featurePinskerPriorActiveFinset k hk lam ↔ lam < i.1.1 := by
  classical
  simp only [featurePinskerPriorActiveFinset, dif_pos hlam, Finset.mem_filter,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact and_iff_right_of_imp (fun h => h.le)

theorem featurePinskerPriorSourceEnergy_eq_active_sum
    (k : X → H) (hk : MemLp k 2 μ) {lam s eps2 : ℝ} (hlam : 0 < lam) :
    featurePinskerPriorSourceEnergy k hk lam s eps2 =
      ∑ i ∈ featurePinskerPriorActiveFinset k hk lam,
        i.1.1^(-s)*pinskerPriorVariance lam s eps2 i.1.1 := by
  classical
  apply tsum_eq_sum
  intro i hi
  have ht : i.1.1 ≤ lam := le_of_not_gt (fun h => hi
    ((mem_featurePinskerPriorActiveFinset k hk hlam i).mpr h))
  rw [pinskerPriorVariance_of_le hlam ht, mul_zero]

theorem featurePinskerPriorSequenceRisk_eq_active_sum
    (k : X → H) (hk : MemLp k 2 μ) {lam s eps2 : ℝ} (hlam : 0 < lam) :
    featurePinskerPriorSequenceRisk k hk lam s eps2 =
      eps2*∑ i ∈ featurePinskerPriorActiveFinset k hk lam,
        ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) i.1.1 := by
  classical
  unfold featurePinskerPriorSequenceRisk
  congr 1
  apply tsum_eq_sum
  intro i hi
  have ht : i.1.1 ≤ lam := le_of_not_gt (fun h => hi
    ((mem_featurePinskerPriorActiveFinset k hk hlam i).mpr h))
  rw [ResidualFilter.pinsker_shrinkage_eq hlam, if_pos ht]

omit [TopologicalSpace.SeparableSpace H] [IsProbabilityMeasure μ] in
theorem featurePinskerPriorSourceEnergy_eq_profile_sum
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk)) (lam s eps2 : ℝ) :
    featurePinskerPriorSourceEnergy k hk lam s eps2 =
      eps2*lam^(-s)*∑' j, pinskerPriorEnergyProfile s ((e j).1.1/lam) := by
  unfold featurePinskerPriorSourceEnergy
  rw [← e.tsum_eq]
  simp_rw [pinskerPriorVariance_source_weight (e _).2]
  rw [tsum_mul_left]

omit [TopologicalSpace.SeparableSpace H] [IsProbabilityMeasure μ] in
theorem featurePinskerPriorSequenceRisk_eq_profile_sum
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {lam s eps2 : ℝ} (hlam : 0 < lam) :
    featurePinskerPriorSequenceRisk k hk lam s eps2 =
      eps2*∑' j, pinskerPriorShrinkageProfile s ((e j).1.1/lam) := by
  unfold featurePinskerPriorSequenceRisk
  rw [← e.tsum_eq]
  simp_rw [pinsker_shrinkage_eq_priorProfile hlam]

theorem summable_feature_positive_of_zero_below
    (k : X → H) (hk : MemLp k 2 μ) {lam : ℝ} (hlam : 0 < lam)
    (F : ℝ → ℝ) (hF : ∀ t, t ≤ lam → F t = 0) :
    Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) => F i.1.1) := by
  apply summable_of_hasFiniteSupport
  apply (finite_featureSpectrum_above k hk hlam).subset
  intro i hi
  by_contra hn
  exact hi (hF i.1.1 (le_of_lt (not_le.mp hn)))

theorem featurePinskerPrior_duality
    (k : X → H) (hk : MemLp k 2 μ) {lam s eps2 : ℝ} (hlam : 0 < lam) :
    featurePinskerPriorSequenceRisk k hk lam s eps2 =
      eps2*featureFilterDimension k hk (ResidualFilter.pinsker lam s)+
        lam^s*featurePinskerPriorSourceEnergy k hk lam s eps2 := by
  have hq := summable_feature_positive_of_zero_below k hk hlam
    (ResidualFilter.shrinkage (ResidualFilter.pinsker lam s)) (fun t ht => by
      rw [ResidualFilter.pinsker_shrinkage_eq hlam, if_pos ht])
  have hv := summable_feature_positive_of_zero_below k hk hlam
    (fun t => (ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) t)^2) (fun t ht => by
      rw [ResidualFilter.pinsker_shrinkage_eq hlam, if_pos ht, zero_pow (by norm_num : 2 ≠ 0)])
  have hE := summable_feature_positive_of_zero_below k hk hlam
    (fun t => t^(-s)*pinskerPriorVariance lam s eps2 t) (fun t ht => by
      rw [pinskerPriorVariance_of_le hlam ht, mul_zero])
  unfold featurePinskerPriorSequenceRisk featurePinskerPriorSourceEnergy
  rw [featureFilterDimension_eq_positive_sequence, ← tsum_mul_left,
    ← tsum_mul_left, ← tsum_mul_left, ← (hv.mul_left eps2).tsum_add (hE.mul_left (lam^s))]
  exact tsum_congr (fun i => pinskerPriorVariance_duality hlam i.2)

/-- The maximal coordinate source-energy bound is exactly a constant times
`lambda^(1/beta)`, so the shaving scale is supplied without a new rate
assumption on the prior. -/
theorem pinskerOracleScale_maxSourceWeight_eq {s β R σ D n : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n) :
    (σ^2/n)*pinskerOracleScale s β R σ D n^(-s)/4 =
      (R^2/(4*D*pinskerPriorEnergyConstant s β))*pinskerOracleScale s β R σ D n^(1/β) := by
  let lam := pinskerOracleScale s β R σ D n
  have hl : 0 < lam := pinskerOracleScale_pos hs hβ hR hσ hD hn
  have hK : 0 < D*pinskerPriorEnergyConstant s β :=
    mul_pos hD (pinskerPriorEnergyConstant_pos hs hβ)
  have hb : (σ^2/n)*lam^(-s-1/β) = R^2/(D*pinskerPriorEnergyConstant s β) :=
    (eq_div_iff hK.ne').mpr (pinskerOracleScale_priorEnergy_balance hs hβ hR hσ hD hn)
  have hp : lam^(-s-1/β)*lam^(1/β) = lam^(-s) := by
    rw [← Real.rpow_add hl]
    congr 1
    ring
  change (σ^2/n)*lam^(-s)/4 = _
  calc
    _ = ((σ^2/n)*lam^(-s-1/β))*lam^(1/β)/4 := by rw [mul_assoc, hp]
    _ = _ := by rw [hb]; ring

theorem featurePinskerPriorSourceEnergy_oracle_tendsto
    {I : Type*} {l : Filter I} (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {s β R σ D : ℝ} (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) (n : I → ℝ) (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop) :
    Tendsto (fun i => featurePinskerPriorSourceEnergy k hk
      (pinskerOracleScale s β R σ D (n i)) s (σ^2/n i)) l (𝓝 (R^2)) := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  let lam := fun i => pinskerOracleScale s β R σ D (n i)
  have hl (i : I) : 0 < lam i := pinskerOracleScale_pos hs0 hβ0 hR hσ hD (hn0 i)
  have hlGT : Tendsto lam l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨pinskerOracleScale_tendsto_zero n hn0 hn hs0 hβ0 hR hσ hD, Eventually.of_forall hl⟩
  have hlim := (feature_pinsker_prior_energy_sum k hk e hβ hD hs hcount).2.comp hlGT
  have hK : 0 < D*pinskerPriorEnergyConstant s β :=
    mul_pos hD (pinskerPriorEnergyConstant_pos hs0 hβ0)
  have hid (i : I) : featurePinskerPriorSourceEnergy k hk (lam i) s (σ^2/n i) =
      (R^2/(D*pinskerPriorEnergyConstant s β))*
        (lam i^(1/β)*∑' j, pinskerPriorEnergyProfile s ((e j).1.1/lam i)) := by
    have hb : (σ^2/n i)*lam i^(-s-1/β) = R^2/(D*pinskerPriorEnergyConstant s β) := by
      exact (eq_div_iff hK.ne').mpr (pinskerOracleScale_priorEnergy_balance hs0 hβ0 hR hσ hD (hn0 i))
    rw [featurePinskerPriorSourceEnergy_eq_profile_sum k hk e, ← hb]
    have hp : lam i^(-s-1/β)*lam i^(1/β) = lam i^(-s) := by
      rw [← Real.rpow_add (hl i)]
      congr 1
      ring
    calc
      _ = (σ^2/n i)*(lam i^(-s-1/β)*lam i^(1/β))*
          ∑' j, pinskerPriorEnergyProfile s ((e j).1.1/lam i) := by rw [hp]
      _ = _ := by ring
  have hh := hlim.const_mul (R^2/(D*pinskerPriorEnergyConstant s β))
  have hc : R^2/(D*pinskerPriorEnergyConstant s β)*(D*pinskerPriorEnergyConstant s β) = R^2 :=
    div_mul_cancel₀ _ hK.ne'
  rw [hc] at hh
  exact hh.congr' (Eventually.of_forall fun i => (hid i).symm)

theorem featurePinskerPriorSourceEnergy_shaved_tendsto
    {I : Type*} {l : Filter I} (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {s β R σ D δ : ℝ} (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hδ : δ < 1)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) (n : I → ℝ) (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop) :
    Tendsto (fun i => featurePinskerPriorSourceEnergy k hk
      (pinskerShavedOracleScale s β R σ D (n i) δ) s (σ^2/n i)) l (𝓝 ((1-δ)*R^2)) := by
  have hRad : 0 < Real.sqrt (1-δ)*R := mul_pos (Real.sqrt_pos.2 (by linarith)) hR
  simpa only [pinskerShavedOracleScale_eq_radius hδ, mul_pow,
    Real.sq_sqrt (by linarith : 0 ≤ 1-δ)] using
    featurePinskerPriorSourceEnergy_oracle_tendsto k hk e hs hβ hRad hσ hD hcount n hn0 hn

theorem featurePinskerPriorSequenceRisk_oracle_normalized_limit
    {I : Type*} {l : Filter I} (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {s β R σ D : ℝ} (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) (n : I → ℝ) (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop) :
    Tendsto (fun i => n i^pinskerRiskExponent s β*featurePinskerPriorSequenceRisk k hk
      (pinskerOracleScale s β R σ D (n i)) s (σ^2/n i)) l
      (𝓝 (pinskerUpperConstant s β R σ D)) := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  let lam := fun i => pinskerOracleScale s β R σ D (n i)
  let C := pinskerUpperConstant s β R σ D
  let a := pinskerRiskExponent s β
  have hl (i : I) : 0 < lam i := pinskerOracleScale_pos hs0 hβ0 hR hσ hD (hn0 i)
  have hb (i : I) : n i^a*(R^2*lam i^s) = C/(s*β+1) := by
    rw [pinskerOracleScale_bias hs0 hβ0 hR hσ hD (hn0 i)]
    have hc : n i^a*n i^(-a) = 1 := by
      rw [← Real.rpow_add (hn0 i), add_neg_cancel, Real.rpow_zero]
    calc
      _ = C/(s*β+1)*(n i^a*n i^(-a)) := by ring
      _ = _ := by rw [hc, mul_one]
  have hcoef (i : I) : n i^a*lam i^s = C/((s*β+1)*R^2) := by
    apply (eq_div_iff (by positivity : (s*β+1)*R^2 ≠ 0)).mpr
    have hh := (eq_div_iff (by positivity : s*β+1 ≠ 0)).mp (hb i)
    nlinarith only [hh]
  have hid (i : I) : n i^a*featurePinskerPriorSequenceRisk k hk (lam i) s (σ^2/n i) =
      n i^a*pinskerWorstSequenceBenchmark k hk s β R σ D (n i)+
        C/((s*β+1)*R^2)*(featurePinskerPriorSourceEnergy k hk (lam i) s (σ^2/n i)-R^2) := by
    rw [featurePinskerPrior_duality k hk (hl i), ← hcoef i]
    change n i^a*((σ^2/n i)*featureFilterDimension k hk (ResidualFilter.pinsker (lam i) s)+
      lam i^s*featurePinskerPriorSourceEnergy k hk (lam i) s (σ^2/n i)) =
      n i^a*(R^2*lam i^s+(σ^2/n i)*featureFilterDimension k hk (ResidualFilter.pinsker (lam i) s))+
        _
    ring
  have hE := featurePinskerPriorSourceEnergy_oracle_tendsto k hk e hs hβ hR hσ hD hcount n hn0 hn
  have hB := pinskerWorstSequenceBenchmark_normalized_limit k hk e hs hβ hR hσ hD hcount n hn0 hn
  have hh := hB.add ((hE.sub_const (R^2)).const_mul (C/((s*β+1)*R^2)))
  simp only [sub_self, mul_zero, add_zero] at hh
  exact hh.congr' (Eventually.of_forall fun i => (hid i).symm)

/-- The genuine sequence Bayes expression at the shaved prior has exactly
the original sharp constant multiplied by the shaving factor. -/
theorem featurePinskerPriorSequenceRisk_shaved_normalized_limit
    {I : Type*} {l : Filter I} (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {s β R σ D δ : ℝ} (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hδ : δ < 1)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) (n : I → ℝ) (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop) :
    Tendsto (fun i => n i^pinskerRiskExponent s β*featurePinskerPriorSequenceRisk k hk
      (pinskerShavedOracleScale s β R σ D (n i) δ) s (σ^2/n i)) l
      (𝓝 ((1-δ)^(1/(s*β+1))*pinskerUpperConstant s β R σ D)) := by
  have hRad : 0 < Real.sqrt (1-δ)*R := mul_pos (Real.sqrt_pos.2 (by linarith)) hR
  simpa only [pinskerShavedOracleScale_eq_radius hδ, pinskerUpperConstant_shaved_radius hR.le hδ] using
    featurePinskerPriorSequenceRisk_oracle_normalized_limit k hk e hs hβ hRad hσ hD hcount n hn0 hn

end ActualSpectrum
end
end KernelSeq
