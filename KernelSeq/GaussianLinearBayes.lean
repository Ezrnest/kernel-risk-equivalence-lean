import KernelSeq.GaussianLinearBayesMatrices
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# A genuine finite Gaussian prior and independent Gaussian noise

The probability law is the actual product of multivariate Gaussian measures.
Finite matrix statistics are actual continuous linear maps of this model.
The posterior covariance algebra is supplied by the preceding module.
-/

namespace KernelSeq.GaussianLinearBayes

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def modelMeasure (v : ι → ℝ) (σ : ℝ) :
    Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :=
  (multivariateGaussian 0 (priorCovariance v)).prod
    (multivariateGaussian 0 (σ^2 • (1 : Matrix κ κ ℝ)))

instance modelMeasure_probability (v : ι → ℝ) (σ : ℝ) :
    IsProbabilityMeasure (modelMeasure (κ := κ) v σ) := by
  unfold modelMeasure
  infer_instance

theorem prior_hasGaussianLaw (v : ι → ℝ) (σ : ℝ) :
    HasGaussianLaw (Prod.fst : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → EuclideanSpace ℝ ι)
      (modelMeasure v σ) := by
  constructor
  simp only [modelMeasure, Measure.map_fst_prod, measure_univ, one_smul]
  infer_instance

theorem noise_hasGaussianLaw (v : ι → ℝ) (σ : ℝ) :
    HasGaussianLaw (Prod.snd : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → EuclideanSpace ℝ κ)
      (modelMeasure v σ) := by
  constructor
  simp only [modelMeasure, Measure.map_snd_prod, measure_univ, one_smul]
  infer_instance

theorem prior_independent_noise (v : ι → ℝ) (σ : ℝ) :
    IndepFun (Prod.fst : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → EuclideanSpace ℝ ι)
      Prod.snd (modelMeasure v σ) := indepFun_prod measurable_id measurable_id

theorem joint_hasGaussianLaw (v : ι → ℝ) (σ : ℝ) :
    HasGaussianLaw (id : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → _)
      (modelMeasure v σ) :=
  IndepFun.hasGaussianLaw (prior_hasGaussianLaw v σ) (noise_hasGaussianLaw v σ)
    (prior_independent_noise v σ)

def matrixCLM {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (M : Matrix a b ℝ) : EuclideanSpace ℝ b →L[ℝ] EuclideanSpace ℝ a :=
  (Matrix.toLpLin 2 2 M).toContinuousLinearMap

theorem matrixCLM_apply {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (M : Matrix a b ℝ) (x : EuclideanSpace ℝ b) (i : a) :
    matrixCLM M x i = ∑ j, M i j * x j := rfl

def statisticCLM {a : Type*} [Fintype a]
    (A : Matrix a ι ℝ) (B : Matrix a κ ℝ) :
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) →L[ℝ] EuclideanSpace ℝ a :=
  (matrixCLM A).comp (.fst ℝ _ _) + (matrixCLM B).comp (.snd ℝ _ _)

theorem statisticCLM_apply {a : Type*} [Fintype a]
    (A : Matrix a ι ℝ) (B : Matrix a κ ℝ)
    (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) (i : a) :
    statisticCLM A B ω i = (∑ j, A i j * ω.1 j) + (∑ j, B i j * ω.2 j) := rfl

theorem statistic_hasGaussianLaw {a : Type*} [Fintype a]
    (v : ι → ℝ) (σ : ℝ) (A : Matrix a ι ℝ) (B : Matrix a κ ℝ) :
    HasGaussianLaw (fun ω => statisticCLM A B ω) (modelMeasure v σ) :=
  (joint_hasGaussianLaw v σ).map_fun (statisticCLM A B)

def coordinateCLM {a : Type*} [Fintype a] (i : a) : EuclideanSpace ℝ a →L[ℝ] ℝ :=
  (EuclideanSpace.projₗ i).toContinuousLinearMap

theorem prior_coordinate_memLp (v : ι → ℝ) (σ : ℝ) (i : ι) :
    MemLp (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => ω.1 i) 2 (modelMeasure v σ) :=
  ((prior_hasGaussianLaw v σ).map_fun (coordinateCLM i)).memLp_two

theorem noise_coordinate_memLp (v : ι → ℝ) (σ : ℝ) (i : κ) :
    MemLp (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => ω.2 i) 2 (modelMeasure v σ) :=
  ((noise_hasGaussianLaw v σ).map_fun (coordinateCLM i)).memLp_two

theorem statistic_coordinate_memLp {a : Type*} [Fintype a]
    (v : ι → ℝ) (σ : ℝ) (A : Matrix a ι ℝ) (B : Matrix a κ ℝ) (i : a) :
    MemLp (fun ω => statisticCLM A B ω i) 2 (modelMeasure v σ) :=
  ((statistic_hasGaussianLaw v σ A B).map_fun (coordinateCLM i)).memLp_two

theorem integral_prior (v : ι → ℝ) (σ : ℝ) :
    (∫ ω, ω.1 ∂modelMeasure (κ := κ) v σ) = (0 : EuclideanSpace ℝ ι) := by
  rw [modelMeasure, integral_fun_fst (fun x => x), integral_id_multivariateGaussian, smul_zero]

theorem integral_noise (v : ι → ℝ) (σ : ℝ) :
    (∫ ω, ω.2 ∂modelMeasure (κ := κ) v σ) = (0 : EuclideanSpace ℝ κ) := by
  rw [modelMeasure, integral_fun_snd (fun x => x), integral_id_multivariateGaussian, smul_zero]

theorem integral_statistic {a : Type*} [Fintype a]
    (v : ι → ℝ) (σ : ℝ) (A : Matrix a ι ℝ) (B : Matrix a κ ℝ) :
    (∫ ω, statisticCLM A B ω ∂modelMeasure v σ) = 0 := by
  rw [show (fun ω => statisticCLM A B ω) =
    (fun ω => matrixCLM A ω.1 + matrixCLM B ω.2) from rfl,
    integral_add ((prior_hasGaussianLaw v σ).map_fun (matrixCLM A)).integrable
      ((noise_hasGaussianLaw v σ).map_fun (matrixCLM B)).integrable,
    (matrixCLM A).integral_comp_comm (prior_hasGaussianLaw v σ).integrable,
    (matrixCLM B).integral_comp_comm (noise_hasGaussianLaw v σ).integrable,
    integral_prior, integral_noise, map_zero, map_zero, add_zero]

theorem covariance_prior {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ) (i j : ι) :
    cov[fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => ω.1 i,
      fun ω => ω.1 j; modelMeasure v σ] = priorCovariance v i j := by
  have he := covariance_map_fun (μ := modelMeasure (κ := κ) v σ)
    (X := fun x : EuclideanSpace ℝ ι => x i) (Y := fun x : EuclideanSpace ℝ ι => x j)
    (Z := Prod.fst) (by fun_prop) (by fun_prop) (by fun_prop)
  simp only [modelMeasure, Measure.map_fst_prod, measure_univ, one_smul] at he
  exact he.symm.trans (covariance_eval_multivariateGaussian (priorCovariance_posDef hv).posSemidef i j)

omit [Fintype κ] in
theorem noiseCovariance_posSemidef (σ : ℝ) : (σ^2 • (1 : Matrix κ κ ℝ)).PosSemidef :=
  PosSemidef.one.smul (sq_nonneg σ)

theorem covariance_noise (v : ι → ℝ) (σ : ℝ) (i j : κ) :
    cov[fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => ω.2 i,
      fun ω => ω.2 j; modelMeasure v σ] = (σ^2 • (1 : Matrix κ κ ℝ)) i j := by
  have he := covariance_map_fun (μ := modelMeasure v σ)
    (X := fun x : EuclideanSpace ℝ κ => x i) (Y := fun x : EuclideanSpace ℝ κ => x j)
    (Z := Prod.snd) (by fun_prop) (by fun_prop) (by fun_prop)
  simp only [modelMeasure, Measure.map_snd_prod, measure_univ, one_smul] at he
  exact he.symm.trans (covariance_eval_multivariateGaussian (noiseCovariance_posSemidef σ) i j)

theorem covariance_prior_noise (v : ι → ℝ) (σ : ℝ) (i : ι) (j : κ) :
    cov[fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => ω.1 i,
      fun ω => ω.2 j; modelMeasure v σ] = 0 := by
  have hi : IndepFun (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => ω.1 i)
      (fun ω => ω.2 j) (modelMeasure v σ) :=
    (prior_independent_noise v σ).comp
      (show Measurable (fun x : EuclideanSpace ℝ ι => x i) from by fun_prop)
      (show Measurable (fun x : EuclideanSpace ℝ κ => x j) from by fun_prop)
  exact hi.covariance_eq_zero (prior_coordinate_memLp v σ i) (noise_coordinate_memLp v σ j)

omit [DecidableEq ι] [DecidableEq κ] in
private theorem covariance_matrix_sum {Ω a b : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ j, MemLp (Y j) 2 P)
    (A : Matrix a ι ℝ) (B : Matrix b κ ℝ) (i : a) (j : b) :
    cov[fun ω => ∑ r, A i r * X r ω, fun ω => ∑ t, B j t * Y t ω; P] =
      (A * (Matrix.of fun r t => cov[X r, Y t; P]) * Bᵀ) i j := by
  rw [covariance_fun_sum_fun_sum (fun r => (hX r).const_mul _) (fun t => (hY t).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, Matrix.mul_apply,
    transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  simp only [Matrix.of_apply]
  ring

/-- Every actual pair of finite linear statistics has the covariance
computed from the prior/noise matrices. No Gaussian moment is a field. -/
theorem covariance_statistic {a b : Type*} [Fintype a] [Fintype b]
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ)
    (A : Matrix a ι ℝ) (B : Matrix a κ ℝ)
    (D : Matrix b ι ℝ) (E : Matrix b κ ℝ) (i : a) (j : b) :
    cov[fun ω => statisticCLM A B ω i, fun ω => statisticCLM D E ω j; modelMeasure v σ] =
      (A * priorCovariance v * Dᵀ + B * (σ^2 • (1 : Matrix κ κ ℝ)) * Eᵀ) i j := by
  let X (r : ι) (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) := ω.1 r
  let Y (r : κ) (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) := ω.2 r
  have hX (r : ι) : MemLp (X r) 2 (modelMeasure v σ) := prior_coordinate_memLp v σ r
  have hY (r : κ) : MemLp (Y r) 2 (modelMeasure v σ) := noise_coordinate_memLp v σ r
  have hXA : MemLp (fun ω => ∑ r, A i r * X r ω) 2 (modelMeasure v σ) :=
    memLp_finsetSum _ (fun r _ => (hX r).const_mul _)
  have hYB : MemLp (fun ω => ∑ r, B i r * Y r ω) 2 (modelMeasure v σ) :=
    memLp_finsetSum _ (fun r _ => (hY r).const_mul _)
  have hXD : MemLp (fun ω => ∑ r, D j r * X r ω) 2 (modelMeasure v σ) :=
    memLp_finsetSum _ (fun r _ => (hX r).const_mul _)
  have hYE : MemLp (fun ω => ∑ r, E j r * Y r ω) 2 (modelMeasure v σ) :=
    memLp_finsetSum _ (fun r _ => (hY r).const_mul _)
  change cov[(fun ω => ∑ r, A i r * X r ω) + (fun ω => ∑ r, B i r * Y r ω),
    (fun ω => ∑ r, D j r * X r ω) + (fun ω => ∑ r, E j r * Y r ω); modelMeasure v σ] = _
  rw [covariance_add_left hXA hYB (hXD.add hYE),
    covariance_add_right hXA hXD hYE, covariance_add_right hYB hXD hYE,
    covariance_matrix_sum X X hX hX A D, covariance_matrix_sum X Y hX hY A E,
    covariance_matrix_sum Y X hY hX B D, covariance_matrix_sum Y Y hY hY B E]
  have hXX : (fun r t => cov[X r, X t; modelMeasure v σ]) = priorCovariance v :=
    funext (fun r => funext (fun t => covariance_prior hv σ r t))
  have hYY : (fun r t => cov[Y r, Y t; modelMeasure v σ]) = σ^2 • (1 : Matrix κ κ ℝ) :=
    funext (fun r => funext (fun t => covariance_noise v σ r t))
  have hXY : (fun r t => cov[X r, Y t; modelMeasure v σ]) = (0 : Matrix ι κ ℝ) :=
    funext (fun r => funext (fun t => covariance_prior_noise v σ r t))
  have hYX : (fun r t => cov[Y r, X t; modelMeasure v σ]) = (0 : Matrix κ ι ℝ) := by
    ext r t
    rw [covariance_comm]
    exact covariance_prior_noise v σ t r
  simp only [hXX, hYY, hXY, hYX]
  change (A * priorCovariance v * Dᵀ) i j + (A * (0 : Matrix ι κ ℝ) * Eᵀ) i j +
    ((B * (0 : Matrix κ ι ℝ) * Dᵀ) i j + (B * (σ^2 • (1 : Matrix κ κ ℝ)) * Eᵀ) i j) = _
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, add_zero, zero_add,
    Matrix.add_apply]

def observation (Φ : Matrix κ ι ℝ) := statisticCLM Φ (1 : Matrix κ κ ℝ)

def posteriorResidual (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) :=
  statisticCLM (residualFactor v σ Φ) (-gain v σ Φ)

private theorem matrixCLM_one_apply {a : Type*} [Fintype a] [DecidableEq a]
    (x : EuclideanSpace ℝ a) : matrixCLM (1 : Matrix a a ℝ) x = x := by
  ext i
  change ((1 : Matrix a a ℝ) *ᵥ x) i = x i
  rw [one_mulVec]

private theorem matrixCLM_sub_apply {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (A B : Matrix a b ℝ) (x : EuclideanSpace ℝ b) :
    matrixCLM (A-B) x = matrixCLM A x - matrixCLM B x := by
  ext i
  simp only [matrixCLM_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, PiLp.sub_apply]

private theorem matrixCLM_neg_apply {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (A : Matrix a b ℝ) (x : EuclideanSpace ℝ b) :
    matrixCLM (-A) x = -matrixCLM A x := by
  ext i
  simp only [matrixCLM_apply, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, PiLp.neg_apply]

private theorem matrixCLM_mul_apply {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c] (A : Matrix a b ℝ) (B : Matrix b c ℝ)
    (x : EuclideanSpace ℝ c) : matrixCLM (A*B) x = matrixCLM A (matrixCLM B x) := by
  ext i
  change ((A*B) *ᵥ x) i = (A *ᵥ (B *ᵥ x)) i
  rw [mulVec_mulVec]

/-- The actual observed vector is `Φθ+ε`. -/
theorem observation_apply (Φ : Matrix κ ι ℝ)
    (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :
    observation Φ ω = matrixCLM Φ ω.1 + ω.2 := by
  change matrixCLM Φ ω.1 + matrixCLM 1 ω.2 = _
  rw [matrixCLM_one_apply]

/-- The actual residual equals prior minus the candidate posterior mean,
not just a second linear statistic with an assumed interpretation. -/
theorem posteriorResidual_eq (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ)
    (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :
    posteriorResidual v σ Φ ω = ω.1 - matrixCLM (gain v σ Φ) (observation Φ ω) := by
  change matrixCLM (residualFactor v σ Φ) ω.1 + matrixCLM (-gain v σ Φ) ω.2 = _
  rw [residualFactor, matrixCLM_sub_apply, matrixCLM_one_apply, matrixCLM_mul_apply,
    matrixCLM_neg_apply, observation_apply, map_add]
  abel

theorem posteriorResidual_integral (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    (∫ ω, posteriorResidual v σ Φ ω ∂modelMeasure v σ) = 0 :=
  integral_statistic v σ _ _

theorem posteriorResidual_hasGaussianLaw (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    HasGaussianLaw (fun ω => posteriorResidual v σ Φ ω) (modelMeasure v σ) :=
  statistic_hasGaussianLaw v σ _ _

theorem covariance_posteriorResidual_observation {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) (i : ι) (j : κ) :
    cov[fun ω => posteriorResidual v σ Φ ω i,
      fun ω => observation Φ ω j; modelMeasure v σ] = 0 := by
  unfold posteriorResidual observation
  rw [covariance_statistic hv]
  simpa only [transpose_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    smul_neg, ← sub_eq_add_neg, Matrix.zero_apply] using
    congrArg (fun M : Matrix ι κ ℝ => M i j) (residual_observation_covariance_zero hv hσ Φ)

theorem covariance_posteriorResidual {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) (i j : ι) :
    cov[fun ω => posteriorResidual v σ Φ ω i,
      fun ω => posteriorResidual v σ Φ ω j; modelMeasure v σ] =
      posteriorCovariance v σ Φ i j := by
  unfold posteriorResidual
  rw [covariance_statistic hv]
  simpa only [transpose_neg, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.neg_mul,
    Matrix.mul_neg, smul_neg, neg_neg] using
    congrArg (fun M : Matrix ι ι ℝ => M i j) (residual_covariance_eq hv hσ Φ)

theorem posteriorResidual_independent_observation {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) :
    IndepFun (fun ω => posteriorResidual v σ Φ ω) (fun ω => observation Φ ω)
      (modelMeasure v σ) := by
  let eι := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let eκ := PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)
  have hg : HasGaussianLaw (fun ω =>
      (fun i => posteriorResidual v σ Φ ω i, fun j => observation Φ ω j))
      (modelMeasure v σ) := by
    exact (joint_hasGaussianLaw v σ).map_fun
      ((eι.toContinuousLinearMap.comp (posteriorResidual v σ Φ)).prod
        (eκ.toContinuousLinearMap.comp (observation Φ)))
  have hi := hg.indepFun_of_covariance_eval (covariance_posteriorResidual_observation hv hσ Φ)
  exact hi.comp eι.symm.continuous.measurable eκ.symm.continuous.measurable

end
end KernelSeq.GaussianLinearBayes
