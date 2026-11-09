import KernelSeq.HilbertSchmidt
import KernelSeq.RHSFluctuation
import KernelSeq.PopulationCovariance

/-!
# Actual empirical covariance in the Hilbert--Schmidt space

A Hilbert–Schmidt second-moment bound for covariance fluctuations.
Rank-one features are constructed in the complete column Hilbert space;
their population mean and empirical average represent exactly the usual
covariance operators. Independence is applied to these actual random columns.
No fourth-moment assumption is added: the leverage bound and L² feature
integrability imply the required second moment of rank-one columns.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace KernelSeq

variable {ι X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω}

omit [CompleteSpace H] in
/-- The random rank-one feature is strongly measurable in the actual HS space. -/
theorem aestronglyMeasurable_hsRankOne_feature (b : HilbertBasis ι ℝ H)
    (g : X → H) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun y => hsRankOne b (g y) (g y)) μ := by
  exact ((hsRankOneBilin b).continuous.clm_apply continuous_id).comp_aestronglyMeasurable hg

omit [CompleteSpace H] in
/-- L² features have an integrable rank-one HS covariance. -/
theorem integrable_hsRankOne_feature (b : HilbertBasis ι ℝ H)
    (g : X → H) (hg : MemLp g 2 μ) :
    Integrable (fun y => hsRankOne b (g y) (g y)) μ := by
  apply ((memLp_two_iff_integrable_sq_norm hg.1).mp hg).mono'
    (aestronglyMeasurable_hsRankOne_feature b g hg.1)
  exact Filter.Eventually.of_forall fun y => by rw [hsRankOne_norm, pow_two]

omit [CompleteSpace H] in
/-- A leverage bound supplies square integrability of the rank-one HS feature. -/
theorem memLp_hsRankOne_feature (b : HilbertBasis ι ℝ H)
    (g : X → H) (hg : MemLp g 2 μ) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, ‖g y‖ ^ 2 ≤ L) :
    MemLp (fun y => hsRankOne b (g y) (g y)) 2 μ := by
  have hm := aestronglyMeasurable_hsRankOne_feature b g hg.1
  rw [memLp_two_iff_integrable_sq_norm hm]
  apply (((memLp_two_iff_integrable_sq_norm hg.1).mp hg).const_mul L).mono' (hm.norm.pow 2)
  filter_upwards [hL] with y hy
  change ‖‖hsRankOne b (g y) (g y)‖ ^ 2‖ ≤ L * ‖g y‖ ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _), hsRankOne_norm_sq]
  exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)

/-- Population covariance as a genuine Bochner integral in the HS Hilbert space. -/
noncomputable def hsCovariance (b : HilbertBasis ι ℝ H) (μ : Measure X) (g : X → H) :
    HilbertSchmidtColumns ι H :=
  ∫ y, hsRankOne b (g y) (g y) ∂μ

/-- Empirical covariance in the same Hilbert space. -/
noncomputable def hsEmpiricalCovariance (b : HilbertBasis ι ℝ H) {n : ℕ}
    (z : Fin n → H) : HilbertSchmidtColumns ι H :=
  (n : ℝ)⁻¹ • ∑ i, hsRankOne b (z i) (z i)

noncomputable def hsCovarianceFluctuation (b : HilbertBasis ι ℝ H)
    (μ : Measure X) (g : X → H) {n : ℕ} (x : Fin n → X) : HilbertSchmidtColumns ι H :=
  hsEmpiricalCovariance b (fun i => g (x i)) - hsCovariance b μ g

/-- The HS mean represents exactly the population operator `S* S`. -/
theorem hilbertSchmidtOperator_hsCovariance (b : HilbertBasis ι ℝ H)
    (g : X → H) (hg : MemLp g 2 μ) :
    hilbertSchmidtOperator b (hsCovariance b μ g) =
      populationCovariance (featureEmbedding μ g hg) := by
  rw [hsCovariance, ← (hilbertSchmidtOperator b).integral_comp_comm
    (integrable_hsRankOne_feature b g hg)]
  simp only [hilbertSchmidtOperator_rankOne]
  exact (populationCovariance_eq_integral g hg).symm

theorem hilbertSchmidtOperator_hsEmpiricalCovariance (b : HilbertBasis ι ℝ H)
    {n : ℕ} (z : Fin n → H) :
    hilbertSchmidtOperator b (hsEmpiricalCovariance b z) = empiricalCovariance z := by
  simp only [hsEmpiricalCovariance, map_smul, map_sum, hilbertSchmidtOperator_rankOne,
    empiricalCovariance]

/-- Actual empirical-minus-population covariance, not an abstract fluctuation. -/
theorem hilbertSchmidtOperator_hsCovarianceFluctuation (b : HilbertBasis ι ℝ H)
    (g : X → H) (hg : MemLp g 2 μ) {n : ℕ} (x : Fin n → X) :
    hilbertSchmidtOperator b (hsCovarianceFluctuation b μ g x) =
      empiricalCovariance (fun i => g (x i)) -
        populationCovariance (featureEmbedding μ g hg) := by
  rw [hsCovarianceFluctuation, map_sub, hilbertSchmidtOperator_hsEmpiricalCovariance,
    hilbertSchmidtOperator_hsCovariance b g hg]

omit [CompleteSpace H] in
theorem hsCovarianceFluctuation_centered (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (g : X → H) (x : Fin n → X) :
    hsCovarianceFluctuation b μ g x = (n : ℝ)⁻¹ •
      ∑ i, (hsRankOne b (g (x i)) (g (x i)) - ∫ y, hsRankOne b (g y) (g y) ∂μ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [hsCovarianceFluctuation, hsEmpiricalCovariance, hsCovariance,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub]
  simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn0]

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

omit [CompleteSpace H] [IsProbabilityMeasure P] in
/-- Actual HS sample fluctuations are square integrable, including the random
feature construction; this is not assumed for the covariance estimator. -/
theorem memLp_hsCovarianceFluctuation (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (g : X → H) (hg : MemLp g 2 μ) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, ‖g y‖ ^ 2 ≤ L) :
    MemLp (fun ω => hsCovarianceFluctuation b μ g (fun i => x i ω)) 2 P := by
  have hu := memLp_hsRankOne_feature b g hg hL
  have hv := hu.sub (memLp_const (∫ y, hsRankOne b (g y) (g y) ∂μ))
  have hs := (memLp_finsetSum' Finset.univ
    (fun i _ => hv.comp_measurePreserving (hlaw i))).const_smul (n : ℝ)⁻¹
  simp_rw [hsCovarianceFluctuation_centered b hn]
  convert hs using 1
  funext ω
  simp only [Pi.smul_apply, Finset.sum_apply, Function.comp_apply, Pi.sub_apply]

/-- The manuscript's HS second-moment estimate from true independent sample
variables. Only pairwise independence is needed for this part. -/
theorem integral_hsCovarianceFluctuation_sq_le (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (g : X → H) (hg : MemLp g 2 μ) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, ‖g y‖ ^ 2 ≤ L) :
    (∫ ω, ‖hsCovarianceFluctuation b μ g (fun i => x i ω)‖ ^ 2 ∂P) ≤
      L / (n : ℝ) * ∫ y, ‖g y‖ ^ 2 ∂μ := by
  letI : MeasurableSpace (HilbertSchmidtColumns ι H) := borel _
  letI : BorelSpace (HilbertSchmidtColumns ι H) := ⟨rfl⟩
  simp_rw [hsCovarianceFluctuation_centered b hn]
  have hu := memLp_hsRankOne_feature b g hg hL
  refine (integral_norm_sq_centered_sample_le hn x hlaw hindep _ hu).trans ?_
  have hm : (∫ y, ‖hsRankOne b (g y) (g y)‖ ^ 2 ∂μ) ≤ L * ∫ y, ‖g y‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hu.1).mp hu)
      (((memLp_two_iff_integrable_sq_norm hg.1).mp hg).const_mul L)
    filter_upwards [hL] with y hy
    rw [hsRankOne_norm_sq]
    exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)
  calc
    _ ≤ (n : ℝ)⁻¹ * (L * ∫ y, ‖g y‖ ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The actual covariance operator perturbation is pointwise bounded by its
Hilbert--Schmidt fluctuation. This does not replace the sharper Bernstein
operator-norm rate needed by the main theorem. -/
theorem covarianceFluctuation_opNorm_le (b : HilbertBasis ι ℝ H)
    (g : X → H) (hg : MemLp g 2 μ) {n : ℕ} (x : Fin n → X) :
    ‖empiricalCovariance (fun i => g (x i)) -
      populationCovariance (featureEmbedding μ g hg)‖ ≤
        ‖hsCovarianceFluctuation b μ g x‖ := by
  rw [← hilbertSchmidtOperator_hsCovarianceFluctuation b g hg x]
  exact hilbertSchmidtOperator_le b _

end KernelSeq
