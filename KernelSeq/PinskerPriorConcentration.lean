import KernelSeq.PinskerPriorEnergy
import KernelSeq.GaussianPriorOutsideMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual Gaussian Pinsker priors outside the source ball

The prior is the genuine finite diagonal multivariate Gaussian on the actual
strict spectral active set. All means, coordinate bounds and exponential
moments are supplied internally from the original counting law and oracle.
-/

namespace KernelSeq

open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped Topology ENNReal BigOperators
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

abbrev PinskerPriorCoordinates (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :=
  ↥(featurePinskerPriorActiveFinset k hk lam)

def pinskerPriorCoordinateVariance (k : X → H) (hk : MemLp k 2 μ)
    (lam s eps2 : ℝ) (i : PinskerPriorCoordinates k hk lam) : ℝ :=
  pinskerPriorVariance lam s eps2 i.1.1.1

def pinskerPriorCoordinateWeight (k : X → H) (hk : MemLp k 2 μ)
    (lam s : ℝ) (i : PinskerPriorCoordinates k hk lam) : ℝ := i.1.1.1^(-s)

def pinskerGaussianPrior (k : X → H) (hk : MemLp k 2 μ) (lam s eps2 : ℝ) :
    Measure (EuclideanSpace ℝ (PinskerPriorCoordinates k hk lam)) := by
  classical
  exact multivariateGaussian 0 (Matrix.diagonal (pinskerPriorCoordinateVariance k hk lam s eps2))

def pinskerGaussianPriorEnergy (k : X → H) (hk : MemLp k 2 μ) (lam s : ℝ) :
    EuclideanSpace ℝ (PinskerPriorCoordinates k hk lam) → ℝ :=
  gaussianPriorEnergy (pinskerPriorCoordinateWeight k hk lam s)

instance pinskerGaussianPrior_probability (k : X → H) (hk : MemLp k 2 μ) (lam s eps2 : ℝ) :
    IsProbabilityMeasure (pinskerGaussianPrior k hk lam s eps2) := by
  unfold pinskerGaussianPrior
  infer_instance

theorem pinskerPriorCoordinateVariance_nonneg
    (k : X → H) (hk : MemLp k 2 μ) {lam s eps2 : ℝ}
    (hlam : 0 < lam) (hs : 0 ≤ s) (heps : 0 ≤ eps2) (i : PinskerPriorCoordinates k hk lam) :
    0 ≤ pinskerPriorCoordinateVariance k hk lam s eps2 i :=
  pinskerPriorVariance_nonneg hlam hs heps i.1.2.le

theorem pinskerPriorCoordinateWeight_nonneg
    (k : X → H) (hk : MemLp k 2 μ) (lam s : ℝ) (i : PinskerPriorCoordinates k hk lam) :
    0 ≤ pinskerPriorCoordinateWeight k hk lam s i := Real.rpow_nonneg i.1.2.le _

theorem pinskerPriorCoordinate_source_weight_le
    (k : X → H) (hk : MemLp k 2 μ) {lam s eps2 : ℝ}
    (hlam : 0 < lam) (hs : 0 ≤ s) (heps : 0 ≤ eps2) (i : PinskerPriorCoordinates k hk lam) :
    pinskerPriorCoordinateWeight k hk lam s i*pinskerPriorCoordinateVariance k hk lam s eps2 i ≤
      eps2*lam^(-s)/4 := pinskerPriorVariance_source_weight_le hlam hs heps i.1.2

theorem pinskerPriorCoordinate_source_sum
    (k : X → H) (hk : MemLp k 2 μ) {lam s eps2 : ℝ} (hlam : 0 < lam) :
    (∑ i : PinskerPriorCoordinates k hk lam,
      pinskerPriorCoordinateWeight k hk lam s i*pinskerPriorCoordinateVariance k hk lam s eps2 i) =
      featurePinskerPriorSourceEnergy k hk lam s eps2 := by
  classical
  rw [featurePinskerPriorSourceEnergy_eq_active_sum k hk hlam]
  exact Finset.sum_coe_sort (featurePinskerPriorActiveFinset k hk lam)
    (fun i : PredictionSingularIndex (featureEmbedding μ k hk) =>
      i.1.1^(-s)*pinskerPriorVariance lam s eps2 i.1.1)

theorem integral_pinskerGaussianPriorEnergy
    (k : X → H) (hk : MemLp k 2 μ) {lam s eps2 : ℝ}
    (hlam : 0 < lam) (hs : 0 ≤ s) (heps : 0 ≤ eps2) :
    (∫ θ, pinskerGaussianPriorEnergy k hk lam s θ ∂pinskerGaussianPrior k hk lam s eps2) =
      featurePinskerPriorSourceEnergy k hk lam s eps2 := by
  classical
  rw [pinskerGaussianPrior, pinskerGaussianPriorEnergy,
    integral_gaussianPriorEnergy _ _ (pinskerPriorCoordinateVariance_nonneg k hk hlam hs heps),
    pinskerPriorCoordinate_source_sum k hk hlam]

theorem pinskerGaussianPriorEnergy_integrable
    (k : X → H) (hk : MemLp k 2 μ) (lam s eps2 : ℝ) :
    Integrable (pinskerGaussianPriorEnergy k hk lam s) (pinskerGaussianPrior k hk lam s eps2) := by
  classical
  exact gaussianPriorEnergy_integrable _ _

theorem pinskerGaussianPriorEnergy_nonneg
    (k : X → H) (hk : MemLp k 2 μ) (lam s : ℝ)
    (θ : EuclideanSpace ℝ (PinskerPriorCoordinates k hk lam)) :
    0 ≤ pinskerGaussianPriorEnergy k hk lam s θ :=
  gaussianPriorEnergy_nonneg _ (pinskerPriorCoordinateWeight_nonneg k hk lam s) θ

/-- Any sample power is dominated by the genuine exponential shaving rate.
The sample-power relation is derived from the original threshold formula. -/
theorem pinskerShavedOracleScale_power_exp_tendsto_zero
    {I : Type*} {l : Filter I} (n : I → ℝ) (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop)
    {s β R σ D δ c : ℝ} (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R)
    (hσ : 0 < σ) (hD : 0 < D) (hδ : δ < 1) (hc : 0 < c) (a : ℝ) :
    Tendsto (fun i => n i^a*Real.exp (-c/(pinskerShavedOracleScale s β R σ D (n i) δ)^(1/β)))
      l (𝓝 0) := by
  let K := σ^2*D*(s*β)/((1-δ)*R^2*(s*β+1)*(s*β+2))
  let θ := β/(s*β+1)
  let b := θ*(1/β)
  have hK : 0 < K := by dsimp [K]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hb : 0 < b := mul_pos hθ (one_div_pos.mpr hβ)
  have he (i : I) : pinskerShavedOracleScale s β R σ D (n i) δ = K^θ*n i^(-θ) := by
    have hr : σ^2*D*(s*β)/(n i*(1-δ)*R^2*(s*β+1)*(s*β+2)) = K/n i := by
      dsimp [K]
      field_simp
    rw [pinskerShavedOracleScale, hr, Real.div_rpow hK.le (hn0 i).le, Real.rpow_neg (hn0 i).le]
    rfl
  have hinv (i : I) : ((pinskerShavedOracleScale s β R σ D (n i) δ)^(1/β))⁻¹ =
      K^(-b)*n i^b := by
    have hl := pinskerShavedOracleScale_pos hs hβ hR hσ hD (hn0 i) hδ
    rw [← Real.rpow_neg hl.le, he i, Real.mul_rpow (Real.rpow_nonneg hK.le _) (Real.rpow_nonneg (hn0 i).le _),
      ← Real.rpow_mul hK.le, ← Real.rpow_mul (hn0 i).le]
    congr 2 <;> dsimp only [b] <;> ring
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b)
    (c*K^(-b)) (by positivity)).comp ((tendsto_rpow_atTop hb).comp hn)
  apply hlim.congr'
  filter_upwards [] with i
  have hp : (n i^b)^(a/b) = n i^a := by
    rw [← Real.rpow_mul (hn0 i).le]
    congr 1
    field_simp
  dsimp only [Function.comp_def]
  rw [hp, div_eq_mul_inv, hinv i]
  congr 2
  ring

def pinskerPriorMaxWeightConstant (s β R D δ : ℝ) : ℝ :=
  (1-δ)*R^2/(4*D*pinskerPriorEnergyConstant s β)

def pinskerPriorOutsideRate (s β R D δ : ℝ) : ℝ :=
  priorShavingExponent δ R/pinskerPriorMaxWeightConstant s β R D δ

theorem pinskerPriorMaxWeightConstant_pos {s β R D δ : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hD : 0 < D) (hδ : δ < 1) :
    0 < pinskerPriorMaxWeightConstant s β R D δ := by
  unfold pinskerPriorMaxWeightConstant
  exact div_pos (mul_pos (by linarith) (sq_pos_of_pos hR))
    (mul_pos (mul_pos (by norm_num) hD) (pinskerPriorEnergyConstant_pos hs hβ))

theorem pinskerPriorOutsideRate_pos {s β R D δ : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hD : 0 < D)
    (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < pinskerPriorOutsideRate s β R D δ := by
  exact div_pos (priorShavingExponent_pos hδ hδ1 hR)
    (pinskerPriorMaxWeightConstant_pos hs hβ hR hD hδ1)

theorem pinskerShavedOracleScale_maxSourceWeight_eq {s β R σ D n δ : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hn : 0 < n) (hδ : δ < 1) :
    (σ^2/n)*pinskerShavedOracleScale s β R σ D n δ^(-s)/4 =
      pinskerPriorMaxWeightConstant s β R D δ*pinskerShavedOracleScale s β R σ D n δ^(1/β) := by
  have hRad : 0 < Real.sqrt (1-δ)*R := mul_pos (Real.sqrt_pos.2 (by linarith)) hR
  rw [pinskerShavedOracleScale_eq_radius hδ]
  have hh := pinskerOracleScale_maxSourceWeight_eq hs hβ hRad hσ hD hn
  simpa only [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1-δ), pinskerPriorMaxWeightConstant] using hh

/-- The actual finite Gaussian prior has an exponentially small outside
probability and first source-energy moment. Every bound is derived from
the original counting law, rather than imposed on the prior. -/
theorem pinskerGaussianPrior_shaved_exponential_bounds
    {I : Type*} {l : Filter I} (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {s β R σ D δ : ℝ} (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) (n : I → ℝ) (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop) :
    ∀ᶠ i in l,
      let lam := pinskerShavedOracleScale s β R σ D (n i) δ
      let P := pinskerGaussianPrior k hk lam s (σ^2/n i)
      let Q := pinskerGaussianPriorEnergy k hk lam s
      P {θ | R^2 < Q θ} ≤ ENNReal.ofReal (Real.exp (-pinskerPriorOutsideRate s β R D δ/lam^(1/β))) ∧
      (∫ θ in {θ | R^2 < Q θ}, Q θ ∂P) ≤
        Real.sqrt (2*Real.exp (2*R^2))*Real.exp (-pinskerPriorOutsideRate s β R D δ/(2*lam^(1/β))) := by
  classical
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hγ : 0 < 1/β := one_div_pos.mpr hβ0
  let lam := fun i => pinskerShavedOracleScale s β R σ D (n i) δ
  let B := fun i => (σ^2/n i)*lam i^(-s)/4
  let S := fun i => featurePinskerPriorSourceEnergy k hk (lam i) s (σ^2/n i)
  let K := pinskerPriorMaxWeightConstant s β R D δ
  have hK : 0 < K := pinskerPriorMaxWeightConstant_pos hs0 hβ0 hR hD hδ1
  have hl (i : I) : 0 < lam i := pinskerShavedOracleScale_pos hs0 hβ0 hR hσ hD (hn0 i) hδ1
  have hB (i : I) : 0 < B i := by
    have hli := hl i
    have hni := hn0 i
    dsimp [B]
    positivity
  have hBeq (i : I) : B i = K*lam i^(1/β) :=
    pinskerShavedOracleScale_maxSourceWeight_eq hs0 hβ0 hR hσ hD (hn0 i) hδ1
  have hS := featurePinskerPriorSourceEnergy_shaved_tendsto k hk e hs hβ hR hσ hD hδ1 hcount n hn0 hn
  have hSlo : ∀ᶠ i in l, (1-δ)*R^2/2 ≤ S i :=
    (hS.eventually (lt_mem_nhds (by nlinarith [sq_pos_of_pos hR] :
      (1-δ)*R^2/2 < (1-δ)*R^2))).mono (fun _ hi => hi.le)
  have hShi : ∀ᶠ i in l, S i ≤ (1-δ/2)*R^2 :=
    (hS.eventually (gt_mem_nhds (by nlinarith [sq_pos_of_pos hR] :
      (1-δ)*R^2 < (1-δ/2)*R^2))).mono (fun _ hi => hi.le)
  have hBl : Tendsto B l (𝓝 0) := by
    have hh := (pinskerShavedOracleScale_tendsto_zero n hn0 hn hs0 hβ0 hR hσ hD hδ1).rpow_const_nhds_zero hγ
    have hh' := hh.const_mul K
    simp only [mul_zero] at hh'
    exact hh'.congr' (Eventually.of_forall fun i => (hBeq i).symm)
  have hBsmall : ∀ᶠ i in l, B i ≤ 1/4 :=
    (hBl.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))).mono (fun _ hi => hi.le)
  filter_upwards [hSlo, hShi, hBsmall] with i hlo hhi hsmall
  let v := pinskerPriorCoordinateVariance k hk (lam i) s (σ^2/n i)
  let w := pinskerPriorCoordinateWeight k hk (lam i) s
  have heps : 0 ≤ σ^2/n i := div_nonneg (sq_nonneg σ) (hn0 i).le
  have hv := pinskerPriorCoordinateVariance_nonneg k hk (hl i) hs0.le heps
  have hw := pinskerPriorCoordinateWeight_nonneg k hk (lam i) s
  have hbound := pinskerPriorCoordinate_source_weight_le k hk (hl i) hs0.le heps
  have hslo : (1-δ)*R^2/2 ≤ ∑ j, w j*v j := by
    rw [pinskerPriorCoordinate_source_sum k hk (hl i)]
    exact hlo
  have hshi : (∑ j, w j*v j) ≤ (1-δ/2)*R^2 := by
    rw [pinskerPriorCoordinate_source_sum k hk (hl i)]
    exact hhi
  have ht := gaussianPriorEnergy_outside_tail v w hv hw hδ hδ1 hR (hB i) hbound hslo hshi
  have hm := gaussianPriorEnergy_outside_moment_le v w hv hw hδ hδ1 hR (hB i) hsmall hbound hslo hshi
  have hexp : -priorShavingExponent δ R/B i = -pinskerPriorOutsideRate s β R D δ/lam i^(1/β) := by
    rw [hBeq i]
    dsimp [pinskerPriorOutsideRate, K]
    ring
  have hexp2 : -priorShavingExponent δ R/(2*B i) = -pinskerPriorOutsideRate s β R D δ/(2*lam i^(1/β)) := by
    rw [hBeq i]
    dsimp [pinskerPriorOutsideRate, K]
    ring
  rw [hexp] at ht
  rw [hexp2] at hm
  exact ⟨ht, hm⟩

/-- Both the actual outside probability and the actual outside source
energy are negligible after multiplication by every fixed real sample
power. The noise and coordinate probability spaces need not be identified
across sample sizes. -/
theorem pinskerGaussianPrior_shaved_outside_power_tendsto_zero
    {I : Type*} {l : Filter I} (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {s β R σ D δ : ℝ} (hs : 1 ≤ s) (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcount : Tendsto (fun t => (featureSpectralCount k hk t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1)) (n : I → ℝ) (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop) (a : ℝ) :
    let lam := fun i => pinskerShavedOracleScale s β R σ D (n i) δ
    let P := fun i => pinskerGaussianPrior k hk (lam i) s (σ^2/n i)
    let Q := fun i => pinskerGaussianPriorEnergy k hk (lam i) s
    Tendsto (fun i => n i^a*(P i).real {θ | R^2 < Q i θ}) l (𝓝 0) ∧
      Tendsto (fun i => n i^a*∫ θ in {θ | R^2 < Q i θ}, Q i θ ∂P i) l (𝓝 0) := by
  dsimp only
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  let c := pinskerPriorOutsideRate s β R D δ
  let C := Real.sqrt (2*Real.exp (2*R^2))
  have hc : 0 < c := pinskerPriorOutsideRate_pos hs0 hβ0 hR hD hδ hδ1
  have hb := pinskerGaussianPrior_shaved_exponential_bounds k hk e hs hβ hR hσ hD hδ hδ1 hcount n hn0 hn
  have hprob := pinskerShavedOracleScale_power_exp_tendsto_zero n hn0 hn hs0 hβ0 hR hσ hD hδ1 hc a
  have hmoment := (pinskerShavedOracleScale_power_exp_tendsto_zero n hn0 hn
    hs0 hβ0 hR hσ hD hδ1 (by positivity : 0 < c/2) a).const_mul C
  simp only [mul_zero] at hmoment
  constructor
  · apply squeeze_zero' (Eventually.of_forall fun i =>
      mul_nonneg (Real.rpow_nonneg (hn0 i).le _) (measureReal_nonneg)) _ hprob
    filter_upwards [hb] with i hi
    dsimp only at hi
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi.1
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hr
    exact mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg (hn0 i).le _)
  · apply squeeze_zero' (Eventually.of_forall fun i =>
      mul_nonneg (Real.rpow_nonneg (hn0 i).le _)
        (integral_nonneg (fun θ => pinskerGaussianPriorEnergy_nonneg k hk _ s θ))) _ hmoment
    filter_upwards [hb] with i hi
    dsimp only at hi
    have hh := mul_le_mul_of_nonneg_left hi.2 (Real.rpow_nonneg (hn0 i).le a)
    have he : -c/(2*pinskerShavedOracleScale s β R σ D (n i) δ^(1/β)) =
        -(c/2)/pinskerShavedOracleScale s β R σ D (n i) δ^(1/β) := by ring
    change _ ≤ C*(n i^a*Real.exp (-(c/2)/pinskerShavedOracleScale s β R σ D (n i) δ^(1/β)))
    refine hh.trans_eq ?_
    change n i^a*(C*Real.exp (-c/(2*pinskerShavedOracleScale s β R σ D (n i) δ^(1/β)))) = _
    rw [he]
    ring

end
end KernelSeq
