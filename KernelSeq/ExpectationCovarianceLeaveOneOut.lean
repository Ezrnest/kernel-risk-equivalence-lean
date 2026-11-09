import KernelSeq.NormalizedBernstein
import KernelSeq.ProvedBernstein
import KernelSeq.ConditionalNoise

/-!
# Actual covariance leave-one-out events for expected risk

The omitted summand is deleted from the genuine normalized covariance sum.
The normalization remains the original sample size. Measurability and
independence from the deleted full observation pair are proved from the
actual feature and pair sigma-algebras. Essential leverage bounds give
event inclusion almost everywhere, rather than a false literal inclusion
on exceptional design points.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace KernelSeq
noncomputable section

variable {X H Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ]

local instance expectationLOOOperatorMeasurableSpace : MeasurableSpace (H →L[ℝ] H) := borel _
local instance expectationLOOOperatorBorelSpace : BorelSpace (H →L[ℝ] H) := ⟨rfl⟩

/-- The actual centered rank-one increment of the population-whitened feature. -/
def normalizedCovarianceIncrement (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (y : X) : H →L[ℝ] H :=
  centeredRankOne (bernsteinFeature k hk lam) (bernsteinFeature_memLp k hk lam) y

/-- Actual leave-one-out normalized covariance; normalization is `1/n`. -/
def leaveOneOutCovariance (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ)
    {n : ℕ} (i : Fin n) (x : Fin n → X) : H →L[ℝ] H :=
  (n : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, normalizedCovarianceIncrement k hk lam (x j)

/-- The manuscript's strict leave-one-out bad event, at threshold `1/8`. -/
def leaveOneOutCovarianceBad (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ)
    {n : ℕ} (i : Fin n) (x : Fin n → Ω → X) : Set Ω :=
  {ω | (1:ℝ)/8 < ‖leaveOneOutCovariance k hk lam i (fun j => x j ω)‖}

theorem normalizedCovarianceIncrement_stronglyMeasurable (k : X → H) (hk : MemLp k 2 μ)
    (hkm : StronglyMeasurable k) (lam : ℝ) :
    StronglyMeasurable (normalizedCovarianceIncrement k hk lam) := by
  have hu : StronglyMeasurable (bernsteinFeature k hk lam) :=
    (featureRegularizedInvSqrt μ k hk lam).continuous.comp_stronglyMeasurable hkm
  have hr := ((InnerProductSpace.rankOne ℝ).continuous.clm_apply continuous_id).comp_stronglyMeasurable hu
  exact hr.sub stronglyMeasurable_const

theorem leaveOneOutCovariance_stronglyMeasurable (k : X → H) (hk : MemLp k 2 μ)
    (hkm : StronglyMeasurable k) (lam : ℝ) {n : ℕ} (i : Fin n)
    (x : Fin n → Ω → X) (hxm : ∀ j, Measurable (x j)) :
    StronglyMeasurable (fun ω => leaveOneOutCovariance k hk lam i (fun j => x j ω)) := by
  unfold leaveOneOutCovariance
  simpa only [Pi.smul_def, Function.comp_def] using (Finset.stronglyMeasurable_fun_sum _ (fun j _ =>
    (normalizedCovarianceIncrement_stronglyMeasurable k hk hkm lam).comp_measurable (hxm j))).const_smul
      ((n:ℝ)⁻¹)

theorem measurableSet_leaveOneOutCovarianceBad (k : X → H) (hk : MemLp k 2 μ)
    (hkm : StronglyMeasurable k) (lam : ℝ) {n : ℕ} (i : Fin n)
    (x : Fin n → Ω → X) (hxm : ∀ j, Measurable (x j)) :
    MeasurableSet (leaveOneOutCovarianceBad k hk lam i x) :=
  measurableSet_lt measurable_const
    (leaveOneOutCovariance_stronglyMeasurable k hk hkm lam i x hxm).measurable.norm

/-- Exact deletion identity, with no commutation assumption. -/
theorem normalizedCovariance_sum_eq_leaveOneOut_add (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {n : ℕ} (i : Fin n) (x : Fin n → X) :
    (n : ℝ)⁻¹ • ∑ j, normalizedCovarianceIncrement k hk lam (x j) =
      leaveOneOutCovariance k hk lam i x +
        (n : ℝ)⁻¹ • normalizedCovarianceIncrement k hk lam (x i) := by
  rw [leaveOneOutCovariance, ← smul_add,
    Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]

/-- The deterministic reverse-triangle inclusion behind leave-one-out risk
decoupling, retaining the strict thresholds from the manuscript. -/
theorem bad_design_imp_leaveOneOut_of_increment (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → X)
    (hi : ‖normalizedCovarianceIncrement k hk lam (x i)‖ / (n : ℝ) ≤ 1/8)
    (hbad : 1/4 < actualCovarianceDeviation k hk lam x) :
    1/8 < ‖leaveOneOutCovariance k hk lam i x‖ := by
  have hδ : actualCovarianceDeviation k hk lam x ≤
      ‖leaveOneOutCovariance k hk lam i x‖ +
        ‖normalizedCovarianceIncrement k hk lam (x i)‖ / (n : ℝ) := by
    change ‖featureRegularizedInvSqrt μ k hk lam *
      (empiricalCovariance (fun j => k (x j)) - populationCovariance (featureEmbedding μ k hk)) *
        featureRegularizedInvSqrt μ k hk lam‖ ≤ _
    rw [← bernsteinFeature_centered_average hn k hk lam x]
    change ‖(n:ℝ)⁻¹ • ∑ j, normalizedCovarianceIncrement k hk lam (x j)‖ ≤ _
    rw [normalizedCovariance_sum_eq_leaveOneOut_add]
    simpa only [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, div_eq_mul_inv, mul_comm] using
      norm_add_le (leaveOneOutCovariance k hk lam i x)
        ((n : ℝ)⁻¹ • normalizedCovarianceIncrement k hk lam (x i))
  linarith

theorem normalizedCovarianceIncrement_norm_le (k : X → H) (hk : MemLp k 2 μ)
    {lam L : ℝ} (hlam : 0 < lam)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    ∀ᵐ y ∂μ, ‖normalizedCovarianceIncrement k hk lam y‖ ≤ L+1 := by
  filter_upwards [centeredRankOne_norm_le (bernsteinFeature k hk lam)
    (bernsteinFeature_memLp k hk lam) hL] with y hy
  have hc : ‖populationCovariance (featureEmbedding μ (bernsteinFeature k hk lam)
      (bernsteinFeature_memLp k hk lam))‖ ≤ 1 := by
    rw [bernsteinFeature_covariance_norm]
    exact featureCovarianceRetention_le_one k hk lam hlam
  exact hy.trans (add_le_add le_rfl hc)

/-- An essential leverage bound yields the needed event inclusion a.e.
The full-pair independence needed for decoupling is a separate theorem below. -/
theorem actual_bad_design_subset_leaveOneOut_ae (k : X → H) (hk : MemLp k 2 μ)
    {lam L : ℝ} (hlam : 0 < lam) {n : ℕ} (hn : 0 < n) (i : Fin n)
    (x : Fin n → Ω → X) (hlaw : ∀ j, MeasurePreserving (x j) P μ)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hsmall : (L+1)/(n:ℝ) ≤ 1/8) :
    ∀ᵐ ω ∂P, 1/4 < actualCovarianceDeviation k hk lam (fun j => x j ω) →
      ω ∈ leaveOneOutCovarianceBad k hk lam i x := by
  filter_upwards [(hlaw i).quasiMeasurePreserving.ae
    (normalizedCovarianceIncrement_norm_le k hk hlam hL)] with ω hω hbad
  apply bad_design_imp_leaveOneOut_of_increment k hk lam hn i _ _ hbad
  exact (div_le_div_of_nonneg_right hω (Nat.cast_nonneg n)).trans hsmall

omit [MeasurableSpace Ω] in
/-- The actual deleted covariance is measurable in the join of the other
full observation-pair sigma-algebras. -/
theorem leaveOneOutCovariance_otherPairs_measurable (k : X → H) (hk : MemLp k 2 μ)
    (hkm : StronglyMeasurable k) (lam : ℝ) {n : ℕ} (i : Fin n)
    (Z : Fin n → Ω → X × ℝ) :
    Measurable[⨆ j, ⨆ (_ : j ≠ i), observationPairSigma (Z j)]
      (fun ω => leaveOneOutCovariance k hk lam i (fun j => (Z j ω).1)) := by
  unfold leaveOneOutCovariance
  have hs : StronglyMeasurable[⨆ j, ⨆ (_ : j ≠ i), observationPairSigma (Z j)]
      (fun ω => ∑ j ∈ Finset.univ.erase i, normalizedCovarianceIncrement k hk lam (Z j ω).1) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hZj : Measurable[observationPairSigma (Z j)] (Z j) := Measurable.of_comap_le le_rfl
    have hjle : observationPairSigma (Z j) ≤ ⨆ j, ⨆ (_ : j ≠ i), observationPairSigma (Z j) :=
      le_iSup_of_le j (le_iSup_of_le hji le_rfl)
    exact (normalizedCovarianceIncrement_stronglyMeasurable k hk hkm lam).comp_measurable
      ((hZj.mono hjle le_rfl).fst)
  simpa only [Pi.smul_def] using (hs.const_smul ((n:ℝ)⁻¹)).measurable

omit [MeasurableSpace Ω] in
/-- The exact other-pair measurability used for independent integration on
the leave-one-out event. No probability or joint-law assumption is needed. -/
theorem measurableSet_otherPairs_leaveOneOutCovarianceBad (k : X → H) (hk : MemLp k 2 μ)
    (hkm : StronglyMeasurable k) (lam : ℝ) {n : ℕ} (i : Fin n)
    (Z : Fin n → Ω → X × ℝ) :
    MeasurableSet[⨆ j, ⨆ (_ : j ≠ i), observationPairSigma (Z j)]
      (leaveOneOutCovarianceBad k hk lam i (fun j ω => (Z j ω).1)) := by
  letI : MeasurableSpace Ω := ⨆ j, ⨆ (_ : j ≠ i), observationPairSigma (Z j)
  exact measurableSet_lt measurable_const
    (leaveOneOutCovariance_otherPairs_measurable k hk hkm lam i Z).norm

/-- Genuine independence from the omitted full pair; it is not assumed as
a leave-one-out certificate. -/
theorem indepFun_pair_leaveOneOutCovariance (k : X → H) (hk : MemLp k 2 μ)
    (hkm : StronglyMeasurable k) (lam : ℝ) {n : ℕ} (i : Fin n)
    (Z : Fin n → Ω → X × ℝ) (hZ : ∀ j, Measurable (Z j)) (hind : iIndepFun Z P) :
    IndepFun (Z i) (fun ω => leaveOneOutCovariance k hk lam i (fun j => (Z j ω).1)) P := by
  rw [IndepFun_iff]
  have hi := independent_block_rest (fun j => (hZ j).comap_le) hind.iIndep i
  intro s t hs ht
  exact (Indep_iff _ _ _).mp hi s t hs
    ((leaveOneOutCovariance_otherPairs_measurable k hk hkm lam i Z).comap_le t ht)

/-- Deleting a coordinate is exactly the actual smaller independent sample,
while keeping the original normalization. -/
theorem leaveOneOutCovariance_succAbove (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ)
    {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → X) :
    leaveOneOutCovariance k hk lam i x =
      (n+1:ℝ)⁻¹ • ∑ j : Fin n, normalizedCovarianceIncrement k hk lam (x (i.succAbove j)) := by
  have he : (∑ j ∈ Finset.univ.erase i, normalizedCovarianceIncrement k hk lam (x j)) =
      ∑ j : Fin n, normalizedCovarianceIncrement k hk lam (x (i.succAbove j)) := by
    apply add_left_cancel (a := normalizedCovarianceIncrement k hk lam (x i))
    calc
      _ = ∑ j, normalizedCovarianceIncrement k hk lam (x j) := by
        rw [add_comm]
        exact Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)
      _ = _ := Fin.sum_univ_succAbove _ i
  simpa only [leaveOneOutCovariance, Nat.cast_add, Nat.cast_one] using
    congrArg (fun A : H →L[ℝ] H => (n+1:ℝ)⁻¹ • A) he

/-- The genuine global deviation bound from the actual whitened empirical
and population covariances. It holds a.e. for an essential leverage bound. -/
theorem actualCovarianceDeviation_global_ae_le (k : X → H) (hk : MemLp k 2 μ)
    {lam L : ℝ} (hlam : 0 < lam) {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ j, MeasurePreserving (x j) P μ)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    ∀ᵐ ω ∂P, actualCovarianceDeviation k hk lam (fun j => x j ω) ≤ L+1 := by
  let u := bernsteinFeature k hk lam
  let hu := bernsteinFeature_memLp k hk lam
  have hL0 : 0 ≤ L := feature_sq_bound_nonneg u hL
  have hae : ∀ᵐ ω ∂P, ∀ j, ‖u (x j ω)‖^2 ≤ L :=
    (ae_all_iff).mpr (fun j => (hlaw j).quasiMeasurePreserving.ae hL)
  filter_upwards [hae] with ω hω
  have he : ‖empiricalCovariance (fun j => u (x j ω))‖ ≤ L := by
    have hh := norm_empiricalCovariance_le_bound hn (fun j => u (x j ω)) (Real.sqrt L)
      (fun j => (hω j).trans_eq (Real.sq_sqrt hL0).symm)
    simpa only [Real.sq_sqrt hL0] using hh
  have hc : ‖populationCovariance (featureEmbedding μ u hu)‖ ≤ 1 := by
    rw [bernsteinFeature_covariance_norm]
    exact featureCovarianceRetention_le_one k hk lam hlam
  change ‖featureRegularizedInvSqrt μ k hk lam *
    (empiricalCovariance (fun j => k (x j ω)) - populationCovariance (featureEmbedding μ k hk)) *
      featureRegularizedInvSqrt μ k hk lam‖ ≤ _
  rw [← bernsteinFeature_centered_average hn k hk lam _, centeredRankOne_average_eq hn]
  exact (norm_sub_le _ _).trans (add_le_add he hc)

end
end KernelSeq
