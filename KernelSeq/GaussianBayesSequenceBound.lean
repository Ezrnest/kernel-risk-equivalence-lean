import KernelSeq.GaussianLinearBayesTrace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Group.Pi.Units

/-!
# Diagonal inverse bounds for the actual Gaussian precision

The scalar variational bound and its integral form derive the sequence Bayes
lower bound from the true random design precision. No inverse-Jensen or
posterior-risk inequality is supplied as an assumption.
-/

namespace KernelSeq.GaussianLinearBayes
open Matrix MeasureTheory
open scoped BigOperators
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype κ] in
theorem posDef_inverse_diagonal_ge_variational {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (j : ι) (t : ℝ) : 2*t - t^2 * A j j ≤ A⁻¹ j j := by
  let e : ι → ℝ := Pi.single j 1
  let c : ι → ℝ := A⁻¹ *ᵥ e
  have hAC : A * A⁻¹ = 1 :=
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hA.isUnit)
  have hAc : A *ᵥ c = e := by dsimp [c]; rw [mulVec_mulVec, hAC, one_mulVec]
  have hce : c ⬝ᵥ e = A⁻¹ j j := by simp [c, e, mulVec_single]
  have hee : e ⬝ᵥ e = 1 := by simp [e]
  have hea : e ⬝ᵥ (A *ᵥ e) = A j j := by simp [e, mulVec_single]
  have hca : c ⬝ᵥ (A *ᵥ e) = 1 := by
    rw [dotProduct_mulVec]
    have hv : c ᵥ* A = e := by
      ext i
      change (∑ k, c k * A k i) = e i
      have heq (k : ι) : A k i = A i k := by simpa only [star_trivial] using hA.isHermitian.apply i k
      simp_rw [heq, mul_comm (c _)]
      exact congrFun hAc i
    rw [hv, hee]
  have hq := hA.posSemidef.dotProduct_mulVec_nonneg (c - t • e)
  simp only [star_trivial, mulVec_sub, mulVec_smul, hAc, sub_dotProduct,
    dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul, hce, hca, hee, hea] at hq
  nlinarith only [hq]

omit [Fintype κ] in
theorem posDef_inverse_diagonal_ge_inv {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (j : ι) : (A j j)⁻¹ ≤ A⁻¹ j j := by
  have h := posDef_inverse_diagonal_ge_variational hA j (A j j)⁻¹
  have hp : 0 < A j j := hA.diag_pos
  have he : 2*(A j j)⁻¹ - ((A j j)⁻¹)^2 * A j j = (A j j)⁻¹ := by
    field_simp
    ring
  rwa [he] at h

theorem posteriorCovariance_diagonal_ge_inv_precision {v : ι → ℝ}
    (hv : ∀ j, 0 < v j) (σ : ℝ) (Φ : Matrix κ ι ℝ) (j : ι) :
    (precision v σ Φ j j)⁻¹ ≤ posteriorCovariance v σ Φ j j :=
  posDef_inverse_diagonal_ge_inv (precision_posDef hv σ Φ) j

theorem precision_diagonal {v : ι → ℝ} (hv : ∀ j, 0 < v j) (σ : ℝ) (Φ : Matrix κ ι ℝ) (j : ι) :
    precision v σ Φ j j = (v j)⁻¹ + (σ^2)⁻¹ * ∑ i : κ, Φ i j ^ 2 := by
  have hu : IsUnit v := Pi.isUnit_iff.mpr (fun j => (isUnit_iff_ne_zero.mpr (hv j).ne'))
  have hi : Ring.inverse v j = (v j)⁻¹ := by
    apply mul_left_cancel₀ (hv j).ne'
    calc
      v j * Ring.inverse v j = 1 := congrFun (Ring.mul_inverse_cancel v hu) j
      _ = v j * (v j)⁻¹ := (mul_inv_cancel₀ (hv j).ne').symm
  simp [precision, priorCovariance, Matrix.inv_diagonal, Matrix.mul_apply, ← pow_two, hi]

local instance sequenceBoundMatrixMeasurableSpace {a b : Type*} : MeasurableSpace (Matrix a b ℝ) :=
  borel _
local instance sequenceBoundMatrixBorelSpace {a b : Type*} : BorelSpace (Matrix a b ℝ) := ⟨rfl⟩

section RandomDesign
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
  [DecidableEq κ]

/-- The diagonal scalar variational inequality integrates without invoking
operator Jensen. The design input is its actual coordinate L2 moment, used
later with normalized population prediction eigenfunctions. -/
theorem expected_posterior_trace_ge_sequence {v : ι → ℝ} (hv : ∀ j, 0 < v j)
    {σ : ℝ} (hσ : 0 < σ) (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ)
    (hLp : ∀ i j, MemLp (fun x => Φ x i j) 2 ν)
    (hmoment : ∀ j, (∫ x, ∑ i : κ, Φ x i j ^ 2 ∂ν) = (Fintype.card κ : ℝ)) :
    (∑ j : ι, ((v j)⁻¹ + (Fintype.card κ : ℝ) * (σ^2)⁻¹)⁻¹) ≤
      ∫ x, (posteriorCovariance v σ (Φ x)).trace ∂ν := by
  let a : ι → ℝ := fun j => (v j)⁻¹ + (Fintype.card κ : ℝ) * (σ^2)⁻¹
  have ha (j : ι) : 0 < a j := by have hp := hv j; dsimp [a]; positivity
  have hint (j : ι) : Integrable (fun x => precision v σ (Φ x) j j) ν := by
    simp_rw [precision_diagonal hv]
    exact (integrable_const _).add ((integrable_finsetSum _
      (fun i _ => (hLp i j).integrable_sq)).const_mul _)
  have havg (j : ι) : (∫ x, precision v σ (Φ x) j j ∂ν) = a j := by
    simp_rw [precision_diagonal hv]
    rw [integral_add (integrable_const _) ((integrable_finsetSum _
      (fun i _ => (hLp i j).integrable_sq)).const_mul _), integral_const_mul, hmoment]
    simp [a, mul_comm]
  have hvar (x : X) : (∑ j : ι, (2 * (a j)⁻¹ - ((a j)⁻¹)^2 * precision v σ (Φ x) j j)) ≤
      (posteriorCovariance v σ (Φ x)).trace := by
    exact Finset.sum_le_sum fun j _ =>
      posDef_inverse_diagonal_ge_variational (precision_posDef hv σ (Φ x)) j (a j)⁻¹
  have hleft : Integrable (fun x => ∑ j : ι,
      (2 * (a j)⁻¹ - ((a j)⁻¹)^2 * precision v σ (Φ x) j j)) ν :=
    integrable_finsetSum _ fun j _ => (integrable_const _).sub ((hint j).const_mul _)
  have hle := integral_mono hleft (integrable_posterior_trace hv hσ Φ hΦ) hvar
  have hterm (j : ι) : Integrable (fun x =>
      2 * (a j)⁻¹ - ((a j)⁻¹)^2 * precision v σ (Φ x) j j) ν :=
    (integrable_const _).sub ((hint j).const_mul _)
  rw [integral_finsetSum _ (fun j _ => hterm j)] at hle
  have heq (j : ι) : (∫ x, 2 * (a j)⁻¹ - ((a j)⁻¹)^2 * precision v σ (Φ x) j j ∂ν) = (a j)⁻¹ := by
    rw [integral_sub (integrable_const _) ((hint j).const_mul _)]
    simp only [integral_const_mul, integral_const, probReal_univ,
      smul_eq_mul, one_mul, havg]
    field_simp [(ha j).ne']
    ring
  simpa only [heq, a] using hle

/-- The actual random-design Bayes risk, over every jointly measurable
decision rule, dominates the Gaussian sequence posterior risk. -/
theorem sequence_bound_le_designCoefficientBayesRisk {v : ι → ℝ} (hv : ∀ j, 0 < v j)
    {σ : ℝ} (hσ : 0 < σ) (Φ : X → Matrix κ ι ℝ) (hΦ : Measurable Φ)
    (hLp : ∀ i j, MemLp (fun x => Φ x i j) 2 ν)
    (hmoment : ∀ j, (∫ x, ∑ i : κ, Φ x i j ^ 2 ∂ν) = (Fintype.card κ : ℝ)) :
    ENNReal.ofReal (∑ j : ι, ((v j)⁻¹ + (Fintype.card κ : ℝ) * (σ^2)⁻¹)⁻¹) ≤
      designCoefficientBayesRisk ν v σ Φ := by
  rw [designCoefficientBayesRisk_eq_expected_trace hv hσ Φ hΦ]
  exact ENNReal.ofReal_le_ofReal (expected_posterior_trace_ge_sequence hv hσ Φ hΦ hLp hmoment)

end RandomDesign

end
end KernelSeq.GaussianLinearBayes
