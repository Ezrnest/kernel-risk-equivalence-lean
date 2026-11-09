import KernelSeq.LipschitzFourierTransference
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Actual finite heat polynomials and their second-order Riesz time integral

The heat normalization is `∂t H = (1/2) Δ H`, as in the Brownian heat
extension in Geiss--Montgomery-Smith--Saksman, Lemma 6.1. The standard torus
phase is `2π k·θ`. All zero-frequency cases are retained explicitly.

This module proves scalar heat calculus and actual finite polynomial time
integration. It asserts no martingale-transform, Fourier, or Schatten norm
estimate. In particular it does not discharge `FixedEvenFourierL2Bound`.
-/

open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

/-- Squared Euclidean frequency, without a square-root convention at zero. -/
def planarFrequencySq (ξ : ℝ × ℝ) : ℝ := ξ.1 ^ 2 + ξ.2 ^ 2

theorem planarFrequencySq_nonneg (ξ : ℝ × ℝ) : 0 ≤ planarFrequencySq ξ := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem planarFrequencySq_pos {ξ : ℝ × ℝ} (hξ : ξ ≠ 0) : 0 < planarFrequencySq ξ := by
  by_contra h
  have hh : ξ.1 ^ 2 + ξ.2 ^ 2 ≤ 0 := le_of_not_gt h
  have hx : ξ.1 = 0 := by nlinarith [sq_nonneg ξ.1, sq_nonneg ξ.2]
  have hy : ξ.2 = 0 := by nlinarith [sq_nonneg ξ.1, sq_nonneg ξ.2]
  exact hξ (Prod.ext hx hy)

/-- Brownian heat rate for the torus frequency `2π ξ`. -/
def planarHeatRate (ξ : ℝ × ℝ) : ℝ := (2 * Real.pi) ^ 2 / 2 * planarFrequencySq ξ

theorem planarHeatRate_nonneg (ξ : ℝ × ℝ) : 0 ≤ planarHeatRate ξ := by
  exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (planarFrequencySq_nonneg ξ)

theorem planarHeatRate_pos {ξ : ℝ × ℝ} (hξ : ξ ≠ 0) : 0 < planarHeatRate ξ := by
  exact mul_pos (div_pos (sq_pos_of_pos (by positivity)) (by norm_num)) (planarFrequencySq_pos hξ)

def planarHeatDecay (ξ : ℝ × ℝ) (t : ℝ) : ℝ := Real.exp (-planarHeatRate ξ * t)

@[simp] theorem planarHeatDecay_zero_time (ξ : ℝ × ℝ) : planarHeatDecay ξ 0 = 1 := by
  simp [planarHeatDecay]

@[simp] theorem planarHeatDecay_zero_frequency (t : ℝ) : planarHeatDecay 0 t = 1 := by
  simp [planarHeatDecay, planarHeatRate, planarFrequencySq]

theorem planarHeatDecay_hasDerivAt (ξ : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (planarHeatDecay ξ) (-planarHeatRate ξ * planarHeatDecay ξ t) t := by
  convert ((hasDerivAt_id t).const_mul (-planarHeatRate ξ)).exp using 1 <;>
    first | rfl | dsimp only [planarHeatDecay, id_eq]; ring

theorem planarHeatDecay_double_time (ξ : ℝ × ℝ) (t : ℝ) :
    planarHeatDecay ξ (2 * t) = planarHeatDecay ξ t ^ 2 := by
  simp only [planarHeatDecay, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem planarHeatDecay_add_time (ξ : ℝ × ℝ) (s t : ℝ) :
    planarHeatDecay ξ (s + t) = planarHeatDecay ξ s * planarHeatDecay ξ t := by
  simp only [planarHeatDecay, ← Real.exp_add]
  congr 1
  ring

theorem planarHeatDecay_tendsto_zero {ξ : ℝ × ℝ} (hξ : ξ ≠ 0) :
    Tendsto (planarHeatDecay ξ) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos (planarHeatRate_pos hξ))).2 tendsto_id)

/-- The actual quadratic form of an arbitrary real two-by-two matrix. -/
def planarQuadraticForm (A : Fin 2 → Fin 2 → ℝ) (ξ : ℝ × ℝ) : ℝ :=
  A 0 0 * ξ.1 ^ 2 + (A 0 1 + A 1 0) * ξ.1 * ξ.2 + A 1 1 * ξ.2 ^ 2

@[simp] theorem planarQuadraticForm_zero (A : Fin 2 → Fin 2 → ℝ) :
    planarQuadraticForm A 0 = 0 := by simp [planarQuadraticForm]

/-- The genuine second-order Riesz symbol, totalized to zero at zero. -/
def planarRieszSymbol (A : Fin 2 → Fin 2 → ℝ) (ξ : ℝ × ℝ) : ℝ :=
  planarQuadraticForm A ξ / planarFrequencySq ξ

@[simp] theorem planarRieszSymbol_zero (A : Fin 2 → Fin 2 → ℝ) :
    planarRieszSymbol A 0 = 0 := by simp [planarRieszSymbol]

/-- The diagonal reflection matrix used for the base even multiplier in GMSS. -/
def planarReflectionMatrix (i j : Fin 2) : ℝ :=
  if i = j then if i = 0 then 1 else -1 else 0

/-- The actual base even symbol `m₀(ξ) = 2ξ₁²/|ξ|² - 1`, away from zero.
Its zero value is separately retained by `planarRieszSymbol_zero`. -/
theorem planarRieszSymbol_reflection {ξ : ℝ × ℝ} (hξ : ξ ≠ 0) :
    planarRieszSymbol planarReflectionMatrix ξ = 2 * ξ.1 ^ 2 / planarFrequencySq ξ - 1 := by
  have hn : planarFrequencySq ξ ≠ 0 := (planarFrequencySq_pos hξ).ne'
  simp only [planarRieszSymbol, planarQuadraticForm, planarReflectionMatrix]
  norm_num
  field_simp
  unfold planarFrequencySq
  ring

/-- The gradient-product time coefficient in the Brownian heat identity. -/
def planarHeatRieszKernel (A : Fin 2 → Fin 2 → ℝ) (ξ : ℝ × ℝ) (t : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 * planarQuadraticForm A ξ * planarHeatDecay ξ t ^ 2

@[simp] theorem planarHeatRieszKernel_zero (A : Fin 2 → Fin 2 → ℝ) (t : ℝ) :
    planarHeatRieszKernel A 0 t = 0 := by simp [planarHeatRieszKernel]

theorem planarHeatRieszKernel_exp (A : Fin 2 → Fin 2 → ℝ) (ξ : ℝ × ℝ) (t : ℝ) :
    planarHeatRieszKernel A ξ t =
      ((2 * Real.pi) ^ 2 * planarQuadraticForm A ξ) * Real.exp (-(2 * planarHeatRate ξ) * t) := by
  simp only [planarHeatRieszKernel, planarHeatDecay, pow_two, ← Real.exp_add]
  congr 2
  ring

/-- Genuine time integrability includes zero frequency, where the integrand
is exactly zero rather than a nonintegrable constant exponential. -/
theorem planarHeatRieszKernel_integrableOn (A : Fin 2 → Fin 2 → ℝ) (ξ : ℝ × ℝ) :
    IntegrableOn (planarHeatRieszKernel A ξ) (Ioi (0 : ℝ)) := by
  by_cases hξ : ξ = 0
  · subst ξ
    have hz : planarHeatRieszKernel A 0 = fun _ : ℝ => 0 :=
      funext (planarHeatRieszKernel_zero A)
    rw [hz]
    exact integrableOn_zero
  · have hi := integrableOn_exp_mul_Ioi
      (show -(2 * planarHeatRate ξ) < 0 by linarith [planarHeatRate_pos hξ]) (0 : ℝ)
    change Integrable (fun t => planarHeatRieszKernel A ξ t) (volume.restrict (Ioi (0 : ℝ)))
    simpa only [planarHeatRieszKernel_exp] using hi.const_mul
      ((2 * Real.pi) ^ 2 * planarQuadraticForm A ξ)

/-- The actual heat time integral is precisely the second-order Riesz symbol.
The proof never divides by a zero frequency. -/
theorem integral_planarHeatRieszKernel (A : Fin 2 → Fin 2 → ℝ) (ξ : ℝ × ℝ) :
    (∫ t in Ioi (0 : ℝ), planarHeatRieszKernel A ξ t) = planarRieszSymbol A ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [planarHeatRieszKernel_zero, integral_zero, planarRieszSymbol_zero]
  · simp only [planarHeatRieszKernel_exp, integral_const_mul]
    rw [integral_exp_mul_Ioi (show -(2 * planarHeatRate ξ) < 0 by
      linarith [planarHeatRate_pos hξ])]
    simp only [mul_zero, Real.exp_zero]
    unfold planarRieszSymbol planarHeatRate
    have hfreq : planarFrequencySq ξ ≠ 0 := (planarFrequencySq_pos hξ).ne'
    have hpi : (2 * Real.pi) ^ 2 ≠ 0 := pow_ne_zero 2 (by positivity)
    field_simp

/-- The integer frequencies used by the actual Fourier transference. -/
def integerPlanarFrequency (k : ℤ × ℤ) : ℝ × ℝ := ((k.1 : ℝ), (k.2 : ℝ))

def heatCosMode (k : ℤ × ℤ) (t : ℝ) (θ : ℝ × ℝ) : ℝ :=
  planarHeatDecay (integerPlanarFrequency k) t * Real.cos (integerPlanePhase k θ)

def heatSinMode (k : ℤ × ℤ) (t : ℝ) (θ : ℝ × ℝ) : ℝ :=
  planarHeatDecay (integerPlanarFrequency k) t * Real.sin (integerPlanePhase k θ)

theorem heatCosMode_time_hasDerivAt (k : ℤ × ℤ) (t : ℝ) (θ : ℝ × ℝ) :
    HasDerivAt (fun s => heatCosMode k s θ)
      (-planarHeatRate (integerPlanarFrequency k) * heatCosMode k t θ) t := by
  convert (planarHeatDecay_hasDerivAt (integerPlanarFrequency k) t).mul_const
    (Real.cos (integerPlanePhase k θ)) using 1 <;> first | rfl | dsimp only [heatCosMode]; ring

theorem heatSinMode_time_hasDerivAt (k : ℤ × ℤ) (t : ℝ) (θ : ℝ × ℝ) :
    HasDerivAt (fun s => heatSinMode k s θ)
      (-planarHeatRate (integerPlanarFrequency k) * heatSinMode k t θ) t := by
  convert (planarHeatDecay_hasDerivAt (integerPlanarFrequency k) t).mul_const
    (Real.sin (integerPlanePhase k θ)) using 1 <;> first | rfl | dsimp only [heatSinMode]; ring

theorem heatCosMode_x_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => heatCosMode k t (z, y))
      (-(2 * Real.pi * (k.1 : ℝ)) * heatSinMode k t (x, y)) x := by
  have hp : HasDerivAt (fun z : ℝ => integerPlanePhase k (z, y))
      (2 * Real.pi * (k.1 : ℝ)) x := by
    convert (((hasDerivAt_id x).const_mul (k.1 : ℝ)).add_const ((k.2 : ℝ) * y)).const_mul
      (2 * Real.pi) using 1 <;> first | rfl | ring
  convert hp.cos.const_mul (planarHeatDecay (integerPlanarFrequency k) t) using 1 <;>
    first | rfl | dsimp only [heatSinMode]; ring

theorem heatSinMode_x_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => heatSinMode k t (z, y))
      ((2 * Real.pi * (k.1 : ℝ)) * heatCosMode k t (x, y)) x := by
  have hp : HasDerivAt (fun z : ℝ => integerPlanePhase k (z, y))
      (2 * Real.pi * (k.1 : ℝ)) x := by
    convert (((hasDerivAt_id x).const_mul (k.1 : ℝ)).add_const ((k.2 : ℝ) * y)).const_mul
      (2 * Real.pi) using 1 <;> first | rfl | ring
  convert hp.sin.const_mul (planarHeatDecay (integerPlanarFrequency k) t) using 1 <;>
    first | rfl | dsimp only [heatCosMode]; ring

theorem heatCosMode_y_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => heatCosMode k t (x, z))
      (-(2 * Real.pi * (k.2 : ℝ)) * heatSinMode k t (x, y)) y := by
  have hp : HasDerivAt (fun z : ℝ => integerPlanePhase k (x, z))
      (2 * Real.pi * (k.2 : ℝ)) y := by
    convert (((hasDerivAt_id y).const_mul (k.2 : ℝ)).const_add ((k.1 : ℝ) * x)).const_mul
      (2 * Real.pi) using 1 <;> first | rfl | ring
  convert hp.cos.const_mul (planarHeatDecay (integerPlanarFrequency k) t) using 1 <;>
    first | rfl | dsimp only [heatSinMode]; ring

theorem heatSinMode_y_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => heatSinMode k t (x, z))
      ((2 * Real.pi * (k.2 : ℝ)) * heatCosMode k t (x, y)) y := by
  have hp : HasDerivAt (fun z : ℝ => integerPlanePhase k (x, z))
      (2 * Real.pi * (k.2 : ℝ)) y := by
    convert (((hasDerivAt_id y).const_mul (k.2 : ℝ)).const_add ((k.1 : ℝ) * x)).const_mul
      (2 * Real.pi) using 1 <;> first | rfl | ring
  convert hp.sin.const_mul (planarHeatDecay (integerPlanarFrequency k) t) using 1 <;>
    first | rfl | dsimp only [heatCosMode]; ring

/-- The second x derivative of the genuine cosine heat mode. -/
theorem heatCosMode_xx_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => -(2 * Real.pi * (k.1 : ℝ)) * heatSinMode k t (z, y))
      (-(2 * Real.pi * (k.1 : ℝ)) ^ 2 * heatCosMode k t (x, y)) x := by
  convert (heatSinMode_x_hasDerivAt k t x y).const_mul (-(2 * Real.pi * (k.1 : ℝ))) using 1 <;> first | rfl | ring

theorem heatSinMode_xx_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => (2 * Real.pi * (k.1 : ℝ)) * heatCosMode k t (z, y))
      (-(2 * Real.pi * (k.1 : ℝ)) ^ 2 * heatSinMode k t (x, y)) x := by
  convert (heatCosMode_x_hasDerivAt k t x y).const_mul (2 * Real.pi * (k.1 : ℝ)) using 1 <;> first | rfl | ring

theorem heatCosMode_xy_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => -(2 * Real.pi * (k.1 : ℝ)) * heatSinMode k t (x, z))
      (-(2 * Real.pi * (k.1 : ℝ)) * (2 * Real.pi * (k.2 : ℝ)) * heatCosMode k t (x, y)) y := by
  convert (heatSinMode_y_hasDerivAt k t x y).const_mul (-(2 * Real.pi * (k.1 : ℝ))) using 1 <;> first | rfl | ring

theorem heatSinMode_xy_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => (2 * Real.pi * (k.1 : ℝ)) * heatCosMode k t (x, z))
      (-(2 * Real.pi * (k.1 : ℝ)) * (2 * Real.pi * (k.2 : ℝ)) * heatSinMode k t (x, y)) y := by
  convert (heatCosMode_y_hasDerivAt k t x y).const_mul (2 * Real.pi * (k.1 : ℝ)) using 1 <;> first | rfl | ring

theorem heatCosMode_yx_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => -(2 * Real.pi * (k.2 : ℝ)) * heatSinMode k t (z, y))
      (-(2 * Real.pi * (k.1 : ℝ)) * (2 * Real.pi * (k.2 : ℝ)) * heatCosMode k t (x, y)) x := by
  convert (heatSinMode_x_hasDerivAt k t x y).const_mul (-(2 * Real.pi * (k.2 : ℝ))) using 1 <;> first | rfl | ring

theorem heatSinMode_yx_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => (2 * Real.pi * (k.2 : ℝ)) * heatCosMode k t (z, y))
      (-(2 * Real.pi * (k.1 : ℝ)) * (2 * Real.pi * (k.2 : ℝ)) * heatSinMode k t (x, y)) x := by
  convert (heatCosMode_x_hasDerivAt k t x y).const_mul (2 * Real.pi * (k.2 : ℝ)) using 1 <;> first | rfl | ring

theorem heatCosMode_yy_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => -(2 * Real.pi * (k.2 : ℝ)) * heatSinMode k t (x, z))
      (-(2 * Real.pi * (k.2 : ℝ)) ^ 2 * heatCosMode k t (x, y)) y := by
  convert (heatSinMode_y_hasDerivAt k t x y).const_mul (-(2 * Real.pi * (k.2 : ℝ))) using 1 <;> first | rfl | ring

theorem heatSinMode_yy_hasDerivAt (k : ℤ × ℤ) (t x y : ℝ) :
    HasDerivAt (fun z => (2 * Real.pi * (k.2 : ℝ)) * heatCosMode k t (x, z))
      (-(2 * Real.pi * (k.2 : ℝ)) ^ 2 * heatSinMode k t (x, y)) y := by
  convert (heatCosMode_y_hasDerivAt k t x y).const_mul (2 * Real.pi * (k.2 : ℝ)) using 1 <;> first | rfl | ring

section Polynomial

variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual finite heat polynomial with arbitrary real Banach-space coefficients. -/
def realHeatPolynomial (k : J → ℤ × ℤ) (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) : E :=
  ∑ j, (heatCosMode (k j) t θ • X j + heatSinMode (k j) t θ • Y j)

theorem realHeatPolynomial_zero_time (k : J → ℤ × ℤ) (X Y : J → E) (θ : ℝ × ℝ) :
    realHeatPolynomial k X Y 0 θ =
      ∑ j, (Real.cos (integerPlanePhase (k j) θ) • X j + Real.sin (integerPlanePhase (k j) θ) • Y j) := by
  simp only [realHeatPolynomial, heatCosMode, heatSinMode, planarHeatDecay_zero_time, one_mul]

def realHeatFirstX (k : J → ℤ × ℤ) (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) : E :=
  ∑ j, ((-(2 * Real.pi * ((k j).1 : ℝ)) * heatSinMode (k j) t θ) • X j +
    ((2 * Real.pi * ((k j).1 : ℝ)) * heatCosMode (k j) t θ) • Y j)

def realHeatFirstY (k : J → ℤ × ℤ) (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) : E :=
  ∑ j, ((-(2 * Real.pi * ((k j).2 : ℝ)) * heatSinMode (k j) t θ) • X j +
    ((2 * Real.pi * ((k j).2 : ℝ)) * heatCosMode (k j) t θ) • Y j)

def realHeatSecondXX (k : J → ℤ × ℤ) (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) : E :=
  ∑ j, ((-(2 * Real.pi * ((k j).1 : ℝ)) ^ 2 * heatCosMode (k j) t θ) • X j +
    (-(2 * Real.pi * ((k j).1 : ℝ)) ^ 2 * heatSinMode (k j) t θ) • Y j)

def realHeatSecondXY (k : J → ℤ × ℤ) (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) : E :=
  ∑ j, ((-(2 * Real.pi * ((k j).1 : ℝ)) * (2 * Real.pi * ((k j).2 : ℝ)) *
      heatCosMode (k j) t θ) • X j +
    (-(2 * Real.pi * ((k j).1 : ℝ)) * (2 * Real.pi * ((k j).2 : ℝ)) *
      heatSinMode (k j) t θ) • Y j)

def realHeatSecondYY (k : J → ℤ × ℤ) (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) : E :=
  ∑ j, ((-(2 * Real.pi * ((k j).2 : ℝ)) ^ 2 * heatCosMode (k j) t θ) • X j +
    (-(2 * Real.pi * ((k j).2 : ℝ)) ^ 2 * heatSinMode (k j) t θ) • Y j)

theorem realHeatPolynomial_time_hasDerivAt (k : J → ℤ × ℤ) (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) :
    HasDerivAt (fun s => realHeatPolynomial k X Y s θ)
      (∑ j, ((-planarHeatRate (integerPlanarFrequency (k j)) * heatCosMode (k j) t θ) • X j +
        (-planarHeatRate (integerPlanarFrequency (k j)) * heatSinMode (k j) t θ) • Y j)) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    ((heatCosMode_time_hasDerivAt (k j) t θ).smul_const (X j)).add
      ((heatSinMode_time_hasDerivAt (k j) t θ).smul_const (Y j))

theorem realHeatPolynomial_x_hasDerivAt (k : J → ℤ × ℤ) (X Y : J → E) (t x y : ℝ) :
    HasDerivAt (fun z => realHeatPolynomial k X Y t (z, y)) (realHeatFirstX k X Y t (x, y)) x := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    ((heatCosMode_x_hasDerivAt (k j) t x y).smul_const (X j)).add
      ((heatSinMode_x_hasDerivAt (k j) t x y).smul_const (Y j))

theorem realHeatPolynomial_y_hasDerivAt (k : J → ℤ × ℤ) (X Y : J → E) (t x y : ℝ) :
    HasDerivAt (fun z => realHeatPolynomial k X Y t (x, z)) (realHeatFirstY k X Y t (x, y)) y := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    ((heatCosMode_y_hasDerivAt (k j) t x y).smul_const (X j)).add
      ((heatSinMode_y_hasDerivAt (k j) t x y).smul_const (Y j))

theorem realHeatPolynomial_xx_hasDerivAt (k : J → ℤ × ℤ) (X Y : J → E) (t x y : ℝ) :
    HasDerivAt (fun z => realHeatFirstX k X Y t (z, y)) (realHeatSecondXX k X Y t (x, y)) x := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    ((heatCosMode_xx_hasDerivAt (k j) t x y).smul_const (X j)).add
      ((heatSinMode_xx_hasDerivAt (k j) t x y).smul_const (Y j))

theorem realHeatPolynomial_xy_hasDerivAt (k : J → ℤ × ℤ) (X Y : J → E) (t x y : ℝ) :
    HasDerivAt (fun z => realHeatFirstX k X Y t (x, z)) (realHeatSecondXY k X Y t (x, y)) y := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    ((heatCosMode_xy_hasDerivAt (k j) t x y).smul_const (X j)).add
      ((heatSinMode_xy_hasDerivAt (k j) t x y).smul_const (Y j))

/-- The reverse mixed partial is the same actual operator-valued function. -/
theorem realHeatPolynomial_yx_hasDerivAt (k : J → ℤ × ℤ) (X Y : J → E) (t x y : ℝ) :
    HasDerivAt (fun z => realHeatFirstY k X Y t (z, y)) (realHeatSecondXY k X Y t (x, y)) x := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    ((heatCosMode_yx_hasDerivAt (k j) t x y).smul_const (X j)).add
      ((heatSinMode_yx_hasDerivAt (k j) t x y).smul_const (Y j))

theorem realHeatPolynomial_yy_hasDerivAt (k : J → ℤ × ℤ) (X Y : J → E) (t x y : ℝ) :
    HasDerivAt (fun z => realHeatFirstY k X Y t (x, z)) (realHeatSecondYY k X Y t (x, y)) y := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    ((heatCosMode_yy_hasDerivAt (k j) t x y).smul_const (X j)).add
      ((heatSinMode_yy_hasDerivAt (k j) t x y).smul_const (Y j))

/-- The actual finite polynomial satisfies the Brownian heat equation. -/
theorem realHeatPolynomial_heat_equation (k : J → ℤ × ℤ) (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) :
    deriv (fun s => realHeatPolynomial k X Y s θ) t =
      (1 / 2 : ℝ) • (realHeatSecondXX k X Y t θ + realHeatSecondYY k X Y t θ) := by
  rw [(realHeatPolynomial_time_hasDerivAt k X Y t θ).deriv]
  simp only [realHeatSecondXX, realHeatSecondYY, ← Finset.sum_add_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_add, smul_smul, planarHeatRate, planarFrequencySq, integerPlanarFrequency]
  module

/-- The actual matrix-weighted spatial Hessian of the finite heat polynomial. -/
def realHeatWeightedHessian (A : Fin 2 → Fin 2 → ℝ) (k : J → ℤ × ℤ)
    (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) : E :=
  A 0 0 • realHeatSecondXX k X Y t θ +
    (A 0 1 + A 1 0) • realHeatSecondXY k X Y t θ +
    A 1 1 • realHeatSecondYY k X Y t θ

/-- All four entries in the matrix-weighted Hessian are genuine spatial
derivatives, including both orders of the mixed derivative. -/
theorem realHeatWeightedHessian_eq_derivs (A : Fin 2 → Fin 2 → ℝ) (k : J → ℤ × ℤ)
    (X Y : J → E) (t x y : ℝ) :
    realHeatWeightedHessian A k X Y t (x, y) =
      A 0 0 • deriv (fun z => realHeatFirstX k X Y t (z, y)) x +
        A 0 1 • deriv (fun z => realHeatFirstX k X Y t (x, z)) y +
        A 1 0 • deriv (fun z => realHeatFirstY k X Y t (z, y)) x +
        A 1 1 • deriv (fun z => realHeatFirstY k X Y t (x, z)) y := by
  rw [(realHeatPolynomial_xx_hasDerivAt k X Y t x y).deriv,
    (realHeatPolynomial_xy_hasDerivAt k X Y t x y).deriv,
    (realHeatPolynomial_yx_hasDerivAt k X Y t x y).deriv,
    (realHeatPolynomial_yy_hasDerivAt k X Y t x y).deriv]
  simp only [realHeatWeightedHessian, add_smul]
  abel

/-- The actual heat/Riesz time integrand with the original coefficient vectors. -/
def realHeatRieszPolynomial (A : Fin 2 → Fin 2 → ℝ) (k : J → ℤ × ℤ)
    (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) : E :=
  ∑ j, ((planarHeatRieszKernel A (integerPlanarFrequency (k j)) t *
      Real.cos (integerPlanePhase (k j) θ)) • X j +
    (planarHeatRieszKernel A (integerPlanarFrequency (k j)) t *
      Real.sin (integerPlanePhase (k j) θ)) • Y j)

/-- The actual finite second-order Riesz multiplier polynomial. -/
def realRieszPolynomial (A : Fin 2 → Fin 2 → ℝ) (k : J → ℤ × ℤ)
    (X Y : J → E) (θ : ℝ × ℝ) : E :=
  ∑ j, ((planarRieszSymbol A (integerPlanarFrequency (k j)) *
      Real.cos (integerPlanePhase (k j) θ)) • X j +
    (planarRieszSymbol A (integerPlanarFrequency (k j)) *
      Real.sin (integerPlanePhase (k j) θ)) • Y j)

/-- The integrand is the negative actual weighted Hessian at doubled time. -/
theorem realHeatRieszPolynomial_eq_neg_hessian (A : Fin 2 → Fin 2 → ℝ) (k : J → ℤ × ℤ)
    (X Y : J → E) (t : ℝ) (θ : ℝ × ℝ) :
    realHeatRieszPolynomial A k X Y t θ = -realHeatWeightedHessian A k X Y (2 * t) θ := by
  simp only [realHeatRieszPolynomial, realHeatWeightedHessian, realHeatSecondXX,
    realHeatSecondXY, realHeatSecondYY, Finset.smul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [planarHeatRieszKernel, heatCosMode, heatSinMode, planarHeatDecay_double_time,
    planarQuadraticForm, integerPlanarFrequency, smul_add, smul_smul]
  module

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem realHeatRieszPolynomial_integrableOn (A : Fin 2 → Fin 2 → ℝ) (k : J → ℤ × ℤ)
    (X Y : J → E) (θ : ℝ × ℝ) :
    IntegrableOn (fun t => realHeatRieszPolynomial A k X Y t θ) (Ioi (0 : ℝ)) := by
  apply integrable_finsetSum
  intro j _
  have hi := planarHeatRieszKernel_integrableOn A (integerPlanarFrequency (k j))
  exact ((hi.mul_const (Real.cos (integerPlanePhase (k j) θ))).smul_const (X j)).add
    ((hi.mul_const (Real.sin (integerPlanePhase (k j) θ))).smul_const (Y j))

/-- Actual Banach-valued Bochner time integration gives the finite Riesz
polynomial. No integration or reconstruction certificate is assumed. -/
theorem integral_realHeatRieszPolynomial (A : Fin 2 → Fin 2 → ℝ) (k : J → ℤ × ℤ)
    (X Y : J → E) (θ : ℝ × ℝ) :
    (∫ t in Ioi (0 : ℝ), realHeatRieszPolynomial A k X Y t θ) = realRieszPolynomial A k X Y θ := by
  unfold realHeatRieszPolynomial realRieszPolynomial
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    have hi := planarHeatRieszKernel_integrableOn A (integerPlanarFrequency (k j))
    rw [integral_add ((hi.mul_const _).smul_const _) ((hi.mul_const _).smul_const _),
      integral_smul_const, integral_smul_const, integral_mul_const, integral_mul_const,
      integral_planarHeatRieszKernel]
  · intro j _
    have hi := planarHeatRieszKernel_integrableOn A (integerPlanarFrequency (k j))
    exact ((hi.mul_const _).smul_const _).add ((hi.mul_const _).smul_const _)

/-- A concrete finite heat-semigroup representation of the actual Riesz
polynomial, through genuine spatial second derivatives. -/
theorem realRieszPolynomial_eq_integral_neg_hessian (A : Fin 2 → Fin 2 → ℝ)
    (k : J → ℤ × ℤ) (X Y : J → E) (θ : ℝ × ℝ) :
    realRieszPolynomial A k X Y θ =
      ∫ t in Ioi (0 : ℝ), -realHeatWeightedHessian A k X Y (2 * t) θ := by
  rw [← integral_realHeatRieszPolynomial A k X Y θ]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => realHeatRieszPolynomial_eq_neg_hessian A k X Y t θ

end Polynomial

section MatrixConnection

variable {J H : Type*} [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Actual identification with the matrix polynomial already used by the
proved Fourier transference, with its genuinely heat-damped coefficients. -/
theorem realHeatPolynomial_matrix_eq (k : J → ℤ × ℤ) (X Y : J → H →L[ℝ] H)
    (t : ℝ) (θ : ℝ × ℝ) :
    realHeatPolynomial k X Y t θ = realMatrixTrigPolynomial k
      (fun j => planarHeatDecay (integerPlanarFrequency (k j)) t • X j)
      (fun j => planarHeatDecay (integerPlanarFrequency (k j)) t • Y j) θ := by
  simp only [realHeatPolynomial, realMatrixTrigPolynomial, heatCosMode, heatSinMode,
    smul_smul, mul_comm]

/-- The integrated Riesz polynomial is the actual coefficientwise matrix
Fourier action of the explicit second-order Riesz symbol. -/
theorem realRieszPolynomial_matrix_eq (A : Fin 2 → Fin 2 → ℝ) (k : J → ℤ × ℤ)
    (X Y : J → H →L[ℝ] H) (θ : ℝ × ℝ) :
    realRieszPolynomial A k X Y θ = realMatrixTrigPolynomial k
      (fun j => planarRieszSymbol A (integerPlanarFrequency (k j)) • X j)
      (fun j => planarRieszSymbol A (integerPlanarFrequency (k j)) • Y j) θ := by
  simp only [realRieszPolynomial, realMatrixTrigPolynomial, smul_smul, mul_comm]

end MatrixConnection

end
end KernelSeq
