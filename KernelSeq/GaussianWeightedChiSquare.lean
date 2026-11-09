import KernelSeq.GaussianQuadraticMoments
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Basic

/-!
# Genuine finite weighted Gaussian-square exponential tails

All exponential integrability and moment bounds are derived from the actual
standard Gaussian product law. The exponential tail is a sufficient,
nonoptimal specialization for prior shaving, not a postulated MGF inequality.
-/

namespace KernelSeq

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

def standardGaussianCoordinates (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance standardGaussianCoordinates_probability : IsProbabilityMeasure (standardGaussianCoordinates ι) := by
  unfold standardGaussianCoordinates
  infer_instance

def gaussianQuadraticForm (b : ι → ℝ) (z : ι → ℝ) : ℝ := ∑ i, b i * z i ^ 2
def gaussianQuadraticMean (b : ι → ℝ) : ℝ := ∑ i, b i

private theorem gaussianQuadratic_exp_eq_prod (b : ι → ℝ) (t : ℝ) (z : ι → ℝ) :
    Real.exp (t*(gaussianQuadraticForm b z-gaussianQuadraticMean b)) =
      ∏ i, Real.exp ((t*b i)*(z i^2-1)) := by
  rw [← Real.exp_sum]
  congr 1
  unfold gaussianQuadraticForm gaussianQuadraticMean
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gaussianQuadratic_exp_integrable (b : ι → ℝ) {t : ℝ}
    (hsmall : ∀ i, t*b i < 1/2) :
    Integrable (fun z => Real.exp (t*(gaussianQuadraticForm b z-gaussianQuadraticMean b)))
      (standardGaussianCoordinates ι) := by
  simp_rw [gaussianQuadratic_exp_eq_prod]
  exact Integrable.fintype_prod_dep (fun i => integrable_exp_centered_sq_standardGaussian (hsmall i))

/-- Independence is used through genuine finite-product integration. -/
theorem gaussianQuadratic_exp_integral (b : ι → ℝ) {t : ℝ}
    (hsmall : ∀ i, t*b i < 1/2) :
    (∫ z, Real.exp (t*(gaussianQuadraticForm b z-gaussianQuadraticMean b))
      ∂standardGaussianCoordinates ι) =
      ∏ i, Real.exp (-(t*b i)) / Real.sqrt (1-2*(t*b i)) := by
  simp_rw [gaussianQuadratic_exp_eq_prod]
  rw [standardGaussianCoordinates, integral_fintype_prod_eq_prod
    (fun i (x : ℝ) => Real.exp ((t*b i)*(x^2-1)))]
  exact Finset.prod_congr rfl (fun i _ => integral_exp_centered_sq_standardGaussian (hsmall i))

theorem gaussianQuadratic_exp_integral_le (b : ι → ℝ) {t : ℝ}
    (hsmall0 : ∀ i, 0 ≤ t*b i) (hsmall1 : ∀ i, t*b i ≤ 1/4) :
    (∫ z, Real.exp (t*(gaussianQuadraticForm b z-gaussianQuadraticMean b))
      ∂standardGaussianCoordinates ι) ≤ Real.exp (4*t^2 * ∑ i, b i^2) := by
  simp_rw [gaussianQuadratic_exp_eq_prod]
  rw [standardGaussianCoordinates, integral_fintype_prod_eq_prod
    (fun i (x : ℝ) => Real.exp ((t*b i)*(x^2-1)))]
  calc
    _ ≤ ∏ i, Real.exp (4*(t*b i)^2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg (fun _ => (Real.exp_pos _).le)
      · intro i _
        exact integral_exp_centered_sq_standardGaussian_le (hsmall0 i) (hsmall1 i)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The actual Chernoff bound before optimizing the exponential parameter. -/
theorem gaussianQuadratic_centered_tail (b : ι → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hsmall0 : ∀ i, 0 ≤ t*b i) (hsmall1 : ∀ i, t*b i ≤ 1/4) (r : ℝ) :
    (standardGaussianCoordinates ι).real
      {z | r ≤ gaussianQuadraticForm b z-gaussianQuadraticMean b} ≤
      Real.exp (-t*r+4*t^2 * ∑ i, b i^2) := by
  have hm := measure_ge_le_exp_mul_mgf (μ := standardGaussianCoordinates ι)
    (X := fun z => gaussianQuadraticForm b z-gaussianQuadraticMean b) r ht
    (gaussianQuadratic_exp_integrable b (fun i => (hsmall1 i).trans_lt (by norm_num)))
  have hb := gaussianQuadratic_exp_integral_le b hsmall0 hsmall1
  exact hm.trans ((mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm)

/-- A dimension-free exponential upper tail adequate for Gaussian prior
shaving. It includes zero weights and the empty active set. -/
theorem gaussianQuadratic_relative_tail (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    {B δ : ℝ} (hB : 0 < B) (hbound : ∀ i, b i ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (standardGaussianCoordinates ι).real
      {z | (1+δ)*gaussianQuadraticMean b ≤ gaussianQuadraticForm b z} ≤
      Real.exp (-(δ^2*gaussianQuadraticMean b)/(32*B)) := by
  let t := δ/(16*B)
  have ht : 0 < t := by dsimp [t]; positivity
  have hS : 0 ≤ gaussianQuadraticMean b := Finset.sum_nonneg (fun i _ => hb i)
  have hsmall0 (i : ι) : 0 ≤ t*b i := mul_nonneg ht.le (hb i)
  have hsmall1 (i : ι) : t*b i ≤ 1/4 := by
    have he : t*B = δ/16 := by dsimp [t]; field_simp
    calc
      _ ≤ t*B := mul_le_mul_of_nonneg_left (hbound i) ht.le
      _ = δ/16 := he
      _ ≤ _ := by linarith
  have hsq : (∑ i, b i^2) ≤ B*gaussianQuadraticMean b := by
    rw [gaussianQuadraticMean, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by nlinarith [mul_nonneg (hb i) (sub_nonneg.mpr (hbound i))])
  have hevent : {z | (1+δ)*gaussianQuadraticMean b ≤ gaussianQuadraticForm b z} =
      {z | δ*gaussianQuadraticMean b ≤ gaussianQuadraticForm b z-gaussianQuadraticMean b} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hz <;> nlinarith only [hz]
  rw [hevent]
  refine (gaussianQuadratic_centered_tail b ht.le hsmall0 hsmall1 (δ*gaussianQuadraticMean b)).trans
    (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ -t*(δ*gaussianQuadraticMean b) + 4*t^2*(B*gaussianQuadraticMean b) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*t^2 by positivity))
    _ = -(3*δ^2*gaussianQuadraticMean b)/(64*B) := by dsimp [t]; field_simp; ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : 0 < 64*B) (by positivity : 0 < 32*B)).mpr
      nlinarith [mul_nonneg hB.le (mul_nonneg (sq_nonneg δ) hS)]

theorem gaussianQuadratic_relative_tail_ennreal (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    {B δ : ℝ} (hB : 0 < B) (hbound : ∀ i, b i ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (standardGaussianCoordinates ι)
      {z | (1+δ)*gaussianQuadraticMean b ≤ gaussianQuadraticForm b z} ≤
      ENNReal.ofReal (Real.exp (-(δ^2*gaussianQuadraticMean b)/(32*B))) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_pos _).le] using
    gaussianQuadratic_relative_tail b hb hB hbound hδ hδ1

end
end KernelSeq
