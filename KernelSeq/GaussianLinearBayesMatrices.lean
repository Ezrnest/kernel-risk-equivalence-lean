import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity

/-!
# Actual precision and residual matrices for finite Gaussian linear models

The prior covariance is a diagonal matrix with strictly positive variances.
All inverse, normal-equation and residual covariance identities are derived
from that positivity and positive noise variance, rather than supplied as
conjugacy or risk certificates.
-/

namespace KernelSeq.GaussianLinearBayes

open Matrix
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

def priorCovariance (v : ι → ℝ) : Matrix ι ι ℝ := diagonal v

def precision (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) : Matrix ι ι ℝ :=
  (priorCovariance v)⁻¹ + (σ^2)⁻¹ • (Φᵀ * Φ)

def posteriorCovariance (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) : Matrix ι ι ℝ :=
  (precision v σ Φ)⁻¹

def gain (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) : Matrix ι κ ℝ :=
  (σ^2)⁻¹ • (posteriorCovariance v σ Φ * Φᵀ)

def residualFactor (v : ι → ℝ) (σ : ℝ) (Φ : Matrix κ ι ℝ) : Matrix ι ι ℝ :=
  1 - gain v σ Φ * Φ

omit [Fintype ι] in
theorem priorCovariance_posDef {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    (priorCovariance v).PosDef := PosDef.diagonal hv

theorem precision_posDef {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    (precision v σ Φ).PosDef := by
  apply (priorCovariance_posDef hv).inv.add_posSemidef
  have hgram : (Φᵀ * Φ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self Φ
  exact hgram.smul (inv_nonneg.mpr (sq_nonneg σ))

theorem posteriorCovariance_posDef {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (σ : ℝ) (Φ : Matrix κ ι ℝ) : (posteriorCovariance v σ Φ).PosDef :=
  (precision_posDef hv σ Φ).inv

theorem posteriorCovariance_mul_precision {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (σ : ℝ) (Φ : Matrix κ ι ℝ) : posteriorCovariance v σ Φ * precision v σ Φ = 1 :=
  nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (precision_posDef hv σ Φ).isUnit)

theorem precision_mul_posteriorCovariance {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (σ : ℝ) (Φ : Matrix κ ι ℝ) : precision v σ Φ * posteriorCovariance v σ Φ = 1 :=
  mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (precision_posDef hv σ Φ).isUnit)

theorem normal_equation {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    posteriorCovariance v σ Φ * (priorCovariance v)⁻¹ + gain v σ Φ * Φ = 1 := by
  simpa only [precision, gain, mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] using
    posteriorCovariance_mul_precision hv σ Φ

theorem residualFactor_eq {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    residualFactor v σ Φ = posteriorCovariance v σ Φ * (priorCovariance v)⁻¹ := by
  unfold residualFactor
  exact (sub_eq_iff_eq_add).mpr (normal_equation hv σ Φ).symm

theorem residualFactor_mul_priorCovariance {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (σ : ℝ) (Φ : Matrix κ ι ℝ) :
    residualFactor v σ Φ * priorCovariance v = posteriorCovariance v σ Φ := by
  rw [residualFactor_eq hv, Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (priorCovariance_posDef hv).isUnit), mul_one]

theorem noiseVariance_smul_gain {v : ι → ℝ} {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) :
    σ^2 • gain v σ Φ = posteriorCovariance v σ Φ * Φᵀ := by
  rw [gain, smul_smul, mul_inv_cancel₀ (sq_pos_of_pos hσ).ne', one_smul]

/-- The true prior/noise covariance calculation for residual versus data
reduces to zero. This identity will supply Gaussian independence. -/
theorem residual_observation_covariance_zero {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) :
    residualFactor v σ Φ * priorCovariance v * Φᵀ - σ^2 • gain v σ Φ = 0 := by
  rw [residualFactor_mul_priorCovariance hv, noiseVariance_smul_gain hσ, sub_self]

/-- The residual covariance is the actual inverse precision, obtained from
the prior and noise covariance formula, rather than postulated as a posterior. -/
theorem residual_covariance_eq {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {σ : ℝ} (hσ : 0 < σ) (Φ : Matrix κ ι ℝ) :
    residualFactor v σ Φ * priorCovariance v * (residualFactor v σ Φ)ᵀ +
      σ^2 • (gain v σ Φ * (gain v σ Φ)ᵀ) = posteriorCovariance v σ Φ := by
  rw [residualFactor_mul_priorCovariance hv, ← Matrix.smul_mul, noiseVariance_smul_gain hσ]
  calc
    _ = posteriorCovariance v σ Φ *
        ((residualFactor v σ Φ)ᵀ + Φᵀ * (gain v σ Φ)ᵀ) := by rw [mul_add, Matrix.mul_assoc]
    _ = posteriorCovariance v σ Φ * (residualFactor v σ Φ + gain v σ Φ * Φ)ᵀ := by
      rw [transpose_add, transpose_mul]
    _ = _ := by rw [residualFactor, sub_add_cancel, transpose_one, mul_one]

end
end KernelSeq.GaussianLinearBayes
