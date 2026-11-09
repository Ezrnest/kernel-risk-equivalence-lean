import KernelSeq.PinskerPriorConcentration
import KernelSeq.FiniteGaussianRegressionBayes
import KernelSeq.SourceNormBounds
import KernelSeq.BayesMinimax
import KernelSeq.FiniteGaussianMinimaxLower
import KernelSeq.PinskerMinimaxAssembly

/-!
# Actual active Pinsker priors and the original source class

The strict active spectral coordinates carry the genuine diagonal Gaussian
prior. The synthesized targets belong to the manuscript's operator source
ball exactly on the weighted ellipsoid, and their containing-ball and
outside-loss bounds follow from the source operator. The Bayes lower bound
concerns every measurable prediction rule in the original regression model.
-/

namespace KernelSeq

open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped ENNReal BigOperators Topology
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

local instance actualPinskerLpMeasurableSpace : MeasurableSpace (Lp ℝ 2 μ) := borel _
local instance actualPinskerLpBorelSpace : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩

def pinskerPriorTarget (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    EuclideanSpace ℝ (PinskerPriorCoordinates k hk lam) →L[ℝ] Lp ℝ 2 μ :=
  FinitePredictionBayes.synthesis (finitePredictionFunction k hk Subtype.val)

def pinskerPriorSourceClass (k : X → H) (hk : MemLp k 2 μ) (lam s R : ℝ) :
    Set (EuclideanSpace ℝ (PinskerPriorCoordinates k hk lam)) :=
  {θ | pinskerGaussianPriorEnergy k hk lam s θ ≤ R^2}

theorem pinskerPriorTarget_sourceEnergy (k : X → H) (hk : MemLp k 2 μ)
    (lam s : ℝ) (θ : EuclideanSpace ℝ (PinskerPriorCoordinates k hk lam)) :
    finiteSourceEnergy k hk Subtype.val s θ = pinskerGaussianPriorEnergy k hk lam s θ := rfl

theorem measurableSet_pinskerPriorSourceClass (k : X → H) (hk : MemLp k 2 μ)
    (lam s R : ℝ) : MeasurableSet (pinskerPriorSourceClass k hk lam s R) := by
  unfold pinskerPriorSourceClass pinskerGaussianPriorEnergy gaussianPriorEnergy
  exact measurableSet_le (by fun_prop) measurable_const

theorem pinskerPriorTarget_mem_sourceBall_iff (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R)
    (θ : EuclideanSpace ℝ (PinskerPriorCoordinates k hk lam)) :
    pinskerPriorTarget k hk lam θ ∈ featureSourceBall k hk s hs R ↔
      θ ∈ pinskerPriorSourceClass k hk lam s R := by
  exact finiteSynthesis_mem_sourceBall_iff_energy k hk Subtype.val Subtype.val_injective hs hR θ

theorem pinskerPriorTarget_norm_sq_le (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {κ s : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ) (hs : 0 ≤ s)
    (θ : EuclideanSpace ℝ (PinskerPriorCoordinates k hk lam)) :
    ‖pinskerPriorTarget k hk lam θ‖^2 ≤ (1+κ^2)^s*pinskerGaussianPriorEnergy k hk lam s θ :=
  finitePrediction_norm_sq_le_sourceEnergy k hk Subtype.val Subtype.val_injective hκ hbound hs θ

theorem pinskerPriorTarget_norm_le_on_class (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {κ s R : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ)
    (hs : 0 ≤ s) (hR : 0 ≤ R)
    {θ : EuclideanSpace ℝ (PinskerPriorCoordinates k hk lam)}
    (hθ : θ ∈ pinskerPriorSourceClass k hk lam s R) :
    ‖pinskerPriorTarget k hk lam θ‖ ≤ (1+κ^2)^(s/2)*R :=
  featureSourceBall_norm_le k hk hκ hbound hs
    ((pinskerPriorTarget_mem_sourceBall_iff k hk lam hs hR θ).mpr hθ)

theorem pinskerPriorCoordinateVariance_pos (k : X → H) (hk : MemLp k 2 μ)
    {lam s eps2 : ℝ} (hlam : 0 < lam) (hs : 0 < s) (heps : 0 < eps2)
    (i : PinskerPriorCoordinates k hk lam) :
    0 < pinskerPriorCoordinateVariance k hk lam s eps2 i :=
  pinskerPriorVariance_pos hlam hs heps
    ((mem_featurePinskerPriorActiveFinset k hk hlam i.val).mp i.property)

/-- The finite prior's genuine weighted source mean being strictly inside
the ball implies positive mass on the actual source class. -/
theorem pinskerPriorSourceClass_measure_pos_of_mean_lt
    (k : X → H) (hk : MemLp k 2 μ) {lam s eps2 R : ℝ}
    (hlam : 0 < lam) (hs : 0 ≤ s) (heps : 0 ≤ eps2)
    (hmean : featurePinskerPriorSourceEnergy k hk lam s eps2 < R^2) :
    0 < pinskerGaussianPrior k hk lam s eps2 (pinskerPriorSourceClass k hk lam s R) := by
  by_contra! hz
  have hzero : pinskerGaussianPrior k hk lam s eps2 (pinskerPriorSourceClass k hk lam s R) = 0 :=
    le_antisymm hz bot_le
  have hae : ∀ᵐ θ ∂pinskerGaussianPrior k hk lam s eps2,
      R^2 ≤ pinskerGaussianPriorEnergy k hk lam s θ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with θ hθ
    exact (not_le.mp hθ).le
  have hh := integral_mono_ae (integrable_const (R^2))
    (pinskerGaussianPriorEnergy_integrable k hk lam s eps2) hae
  rw [integral_const, probReal_univ, one_smul,
    integral_pinskerGaussianPriorEnergy k hk hlam hs heps] at hh
  exact (not_le_of_gt hmean) hh

/-- The actual regression experiment, without restrictions on measurable
prediction rules, has the finite active Gaussian sequence lower bound. -/
theorem pinskerGaussianPrior_bayes_ge_sequence (k : X → H) (hk : MemLp k 2 μ)
    {lam s eps2 σ : ℝ} (hlam : 0 < lam) (hs : 0 < s) (heps : 0 < eps2)
    (hσ : 0 < σ) (n : ℕ) :
    ENNReal.ofReal (∑ j : PinskerPriorCoordinates k hk lam,
      ((pinskerPriorCoordinateVariance k hk lam s eps2 j)⁻¹+(n:ℝ)*(σ^2)⁻¹)⁻¹) ≤
      predictionBayesRisk (pinskerGaussianPrior k hk lam s eps2)
        (gaussianRegressionSampleMeasure μ σ n) (pinskerPriorTarget k hk lam)
        (fun θ => gaussianRegressionData μ (n := n) (pinskerPriorTarget k hk lam θ)) := by
  classical
  exact finiteGaussianRegression_bayes_ge_sequence k hk Subtype.val Subtype.val_injective
    (pinskerPriorCoordinateVariance_pos k hk hlam hs heps) hσ

set_option maxHeartbeats 800000 in
/-- The finite posterior expression is the original full positive-spectrum
sequence Bayes risk; inactive and threshold-equality terms vanish. -/
theorem pinskerPrior_active_sequence_eq (k : X → H) (hk : MemLp k 2 μ)
    {lam s σ : ℝ} (hlam : 0 < lam) (hs : 0 < s) (hσ : 0 < σ)
    {n : ℕ} (hn : 0 < n) :
    (∑ j : PinskerPriorCoordinates k hk lam,
      ((pinskerPriorCoordinateVariance k hk lam s (σ^2/n) j)⁻¹+(n:ℝ)*(σ^2)⁻¹)⁻¹) =
      featurePinskerPriorSequenceRisk k hk lam s (σ^2/n) := by
  classical
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have heps : 0 < σ^2/(n:ℝ) := div_pos (sq_pos_of_pos hσ) hnR
  have hinv : (n:ℝ)*(σ^2)⁻¹ = (σ^2/(n:ℝ))⁻¹ := by
    rw [inv_div]
    rfl
  rw [featurePinskerPriorSequenceRisk_eq_active_sum k hk hlam, Finset.mul_sum]
  calc
    _ = ∑ j : PinskerPriorCoordinates k hk lam,
        (σ^2/(n:ℝ))*ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) j.val.1.1 := by
      apply Finset.sum_congr rfl
      intro j _
      have hv := pinskerPriorCoordinateVariance_pos k hk hlam hs heps j
      rw [hinv]
      have he : ((pinskerPriorCoordinateVariance k hk lam s (σ^2/n) j)⁻¹ +
          (σ^2/(n:ℝ))⁻¹)⁻¹ =
          (σ^2/(n:ℝ))*(pinskerPriorCoordinateVariance k hk lam s (σ^2/n) j /
            (pinskerPriorCoordinateVariance k hk lam s (σ^2/n) j + σ^2/(n:ℝ))) := by
        field_simp [hv.ne', heps.ne', (add_pos hv heps).ne']
        ring
      rw [he]
      exact congrArg ((σ^2/(n:ℝ)) * ·) (pinskerPriorVariance_posterior hlam heps)
    _ = _ := Finset.sum_coe_sort (featurePinskerPriorActiveFinset k hk lam)
      (fun i : PredictionSingularIndex (featureEmbedding μ k hk) =>
        (σ^2/(n:ℝ))*ResidualFilter.shrinkage (ResidualFilter.pinsker lam s) i.1.1)

def pinskerPriorShavingRemainder (k : X → H) (hk : MemLp k 2 μ)
    (lam s eps2 κ R : ℝ) : ℝ :=
  2*((1+κ^2)^(s/2)*R)^2 * (pinskerGaussianPrior k hk lam s eps2).real
      {θ | R^2 < pinskerGaussianPriorEnergy k hk lam s θ} +
    2*(1+κ^2)^s * ∫ θ in {θ | R^2 < pinskerGaussianPriorEnergy k hk lam s θ},
      pinskerGaussianPriorEnergy k hk lam s θ ∂pinskerGaussianPrior k hk lam s eps2

theorem pinskerPriorShavingRemainder_nonneg (k : X → H) (hk : MemLp k 2 μ)
    (lam s eps2 κ R : ℝ) : 0 ≤ pinskerPriorShavingRemainder k hk lam s eps2 κ R := by
  unfold pinskerPriorShavingRemainder
  exact add_nonneg (mul_nonneg (by positivity) measureReal_nonneg)
    (mul_nonneg (by positivity) (integral_nonneg
      (fun θ => pinskerGaussianPriorEnergy_nonneg k hk lam s θ)))

/-- The actual extended-real clipping remainder equals its finite real
probability-and-energy expression. Gaussian energy integrability is proved
upstream, so no undefined Bochner integral is used. -/
theorem pinskerPriorShavingRemainder_lintegral (k : X → H) (hk : MemLp k 2 μ)
    (lam s eps2 κ R : ℝ) :
    (∫⁻ θ in (pinskerPriorSourceClass k hk lam s R)ᶜ,
      ENNReal.ofReal (2*((1+κ^2)^(s/2)*R)^2 +
        2*(1+κ^2)^s*pinskerGaussianPriorEnergy k hk lam s θ)
        ∂pinskerGaussianPrior k hk lam s eps2) =
      ENNReal.ofReal (pinskerPriorShavingRemainder k hk lam s eps2 κ R) := by
  let P := pinskerGaussianPrior k hk lam s eps2
  let E := {θ | R^2 < pinskerGaussianPriorEnergy k hk lam s θ}
  have hE : (pinskerPriorSourceClass k hk lam s R)ᶜ = E := by
    ext θ
    exact not_le (a := pinskerGaussianPriorEnergy k hk lam s θ) (b := R^2)
  rw [hE]
  have hi : Integrable (fun θ => 2*((1+κ^2)^(s/2)*R)^2 +
      2*(1+κ^2)^s*pinskerGaussianPriorEnergy k hk lam s θ) P :=
    (integrable_const _).add ((pinskerGaussianPriorEnergy_integrable k hk lam s eps2).const_mul _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn]
  · congr 1
    rw [integral_add (integrable_const _)
      (((pinskerGaussianPriorEnergy_integrable k hk lam s eps2).const_mul _).integrableOn),
      integral_const, integral_const_mul]
    simp only [smul_eq_mul, measureReal_restrict_apply_univ]
    dsimp [pinskerPriorShavingRemainder, E, P]
    ring
  · exact Eventually.of_forall fun θ => by
      have hq := pinskerGaussianPriorEnergy_nonneg k hk lam s θ
      positivity

/-- A completely actual finite-model lower bound, with only the transparent
strict-inside mean condition needed for the supported-prior normalization. -/
theorem pinsker_minimax_lower_with_remainder (k : X → H) (hk : MemLp k 2 μ)
    {κ lam s R σ : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ)
    (hlam : 0 < lam) (hs : 0 < s) (hR : 0 < R) (hσ : 0 < σ)
    {n : ℕ} (hn : 0 < n)
    (hmean : featurePinskerPriorSourceEnergy k hk lam s (σ^2/n) < R^2) :
    featurePinskerPriorSequenceRisk k hk lam s (σ^2/n) ≤
      (gaussianRangeMinimaxRisk k hk σ n (featureSourceBall k hk s hs.le R)).toReal +
        pinskerPriorShavingRemainder k hk lam s (σ^2/n) κ R := by
  classical
  have heps : 0 < σ^2/(n:ℝ) := div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr hn)
  have hp := pinskerPriorSourceClass_measure_pos_of_mean_lt k hk hlam hs.le heps.le hmean
  have hfin := finiteGaussian_minimax_sourceBall_lower k hk Subtype.val Subtype.val_injective
    hκ hbound hs.le hR hσ n (pinskerPriorCoordinateVariance k hk lam s (σ^2/n))
    (pinskerPriorCoordinateVariance_pos k hk hlam hs heps) hp
  rw [pinskerPrior_active_sequence_eq k hk hlam hs hσ hn] at hfin
  simp_rw [pinskerPriorTarget_sourceEnergy] at hfin
  change ENNReal.ofReal (featurePinskerPriorSequenceRisk k hk lam s (σ^2/n)) ≤
    gaussianRangeMinimaxRisk k hk σ n (featureSourceBall k hk s hs.le R) +
      ∫⁻ θ in (pinskerPriorSourceClass k hk lam s R)ᶜ,
        ENNReal.ofReal (2*((1+κ^2)^(s/2)*R)^2+2*(1+κ^2)^s*pinskerGaussianPriorEnergy k hk lam s θ)
        ∂pinskerGaussianPrior k hk lam s (σ^2/n) at hfin
  rw [pinskerPriorShavingRemainder_lintegral] at hfin
  exact real_le_toReal_add_of_ofReal_le
    (pinskerPriorShavingRemainder_nonneg k hk lam s (σ^2/n) κ R)
    (gaussianRangeMinimaxRisk_sourceBall_lt_top k hk hκ hbound hs.le hR.le σ n).ne hfin

/-- The actual loss remainder from clipping is smaller than every fixed
inverse sample power. Its probability and source-energy terms are both
provided by the actual Gaussian prior concentration theorem. -/
theorem pinskerPriorShavingRemainder_shaved_power_tendsto_zero
    {I : Type*} {l : Filter I} (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {κ s β R σ D δ : ℝ} (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R)
    (hσ : 0 < σ) (hD : 0 < D) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) (n : I → ℝ) (hn0 : ∀ i, 0 < n i)
    (hn : Tendsto n l atTop) (a : ℝ) :
    Tendsto (fun i => n i^a*pinskerPriorShavingRemainder k hk
      (pinskerShavedOracleScale s β R σ D (n i) δ) s (σ^2/n i) κ R) l (𝓝 0) := by
  have ht := pinskerGaussianPrior_shaved_outside_power_tendsto_zero k hk e
    hs hβ hR hσ hD hδ hδ1 hcount n hn0 hn a
  dsimp only at ht
  have hh := (ht.1.const_mul (2*((1+κ^2)^(s/2)*R)^2)).add
    (ht.2.const_mul (2*(1+κ^2)^s))
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [] with i
  unfold pinskerPriorShavingRemainder
  ring

/-- The original full measurable prediction-range decision class has the
sharp shaved Pinsker lower constant. All active-prior, Gaussian regression,
source membership, and outside-loss bounds are supplied internally. -/
theorem pinsker_minimax_normalized_shaved_lower
    {I : Type*} {l : Filter I} (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {κ s β R σ D δ : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ)
    (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) (n : I → ℕ) (hnpos : ∀ i, 0 < n i)
    (hn : Tendsto (fun i => (n i : ℝ)) l atTop) :
    ∀ ε > 0, ∀ᶠ i in l,
      (1-δ)^(1/(s*β+1))*pinskerUpperConstant s β R σ D - ε ≤
        (n i : ℝ)^pinskerRiskExponent s β *
          (gaussianRangeMinimaxRisk k hk σ (n i) (featureSourceBall k hk s
            (zero_lt_one.trans_le hs).le R)).toReal := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hnR (i : I) : 0 < (n i : ℝ) := Nat.cast_pos.mpr (hnpos i)
  let lam := fun i => pinskerShavedOracleScale s β R σ D (n i) δ
  have hl (i : I) : 0 < lam i := pinskerShavedOracleScale_pos hs0 hβ0 hR hσ hD (hnR i) hδ1
  have hmean := featurePinskerPriorSourceEnergy_shaved_tendsto k hk e
    hs hβ hR hσ hD hδ1 hcount (fun i => (n i : ℝ)) hnR hn
  have hmeanlt : ∀ᶠ i in l,
      featurePinskerPriorSourceEnergy k hk (lam i) s (σ^2/(n i:ℝ)) < R^2 :=
    hmean.eventually (gt_mem_nhds (by nlinarith [sq_pos_of_pos hR] : (1-δ)*R^2 < R^2))
  have hseq := featurePinskerPriorSequenceRisk_shaved_normalized_limit k hk e
    hs hβ hR hσ hD hδ1 hcount (fun i => (n i : ℝ)) hnR hn
  have hrem := pinskerPriorShavingRemainder_shaved_power_tendsto_zero k hk e
    (κ := κ) hs hβ hR hσ hD hδ hδ1 hcount (fun i => (n i : ℝ)) hnR hn
    (pinskerRiskExponent s β)
  have hdiff := hseq.sub hrem
  simp only [sub_zero] at hdiff
  intro ε hε
  have hevent := hdiff.eventually (lt_mem_nhds (by linarith :
    (1-δ)^(1/(s*β+1))*pinskerUpperConstant s β R σ D - ε <
      (1-δ)^(1/(s*β+1))*pinskerUpperConstant s β R σ D))
  filter_upwards [hmeanlt, hevent] with i hm hi
  have hfinite := pinsker_minimax_lower_with_remainder k hk hκ hbound
    (hl i) hs0 hR hσ (hnpos i) hm
  have hscaled := mul_le_mul_of_nonneg_left hfinite
    (Real.rpow_nonneg (hnR i).le (pinskerRiskExponent s β))
  change _ < (n i:ℝ)^pinskerRiskExponent s β *
      featurePinskerPriorSequenceRisk k hk (lam i) s (σ^2/(n i:ℝ)) -
    (n i:ℝ)^pinskerRiskExponent s β *
      pinskerPriorShavingRemainder k hk (lam i) s (σ^2/(n i:ℝ)) κ R at hi
  exact hi.le.trans (by linarith only [hscaled])

end
end KernelSeq
