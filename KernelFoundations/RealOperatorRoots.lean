import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Real regularized operator prerequisites

This file establishes coercivity and invertibility of `T + lam I` on a real
Hilbert space. It deliberately does not define an operator square root: this
Mathlib snapshot has no real-operator continuous functional calculus instance
and no bundled analytic Hilbert-space complexification bridge.
-/

namespace KernelFoundations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive regularization has a quantitative quadratic-form lower bound. -/
theorem regularized_quadratic_coercivity_real (T : E →L[ℝ] E) (hT : 0 ≤ T)
    (lam : ℝ) (x : E) :
    lam * ‖x‖ ^ 2 ≤ inner ℝ x ((T + lam • (1 : E →L[ℝ] E)) x) := by
  have hpos := ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT).inner_nonneg_right x
  change lam * ‖x‖ ^ 2 ≤ inner ℝ x (T x + lam • x)
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_left hpos

/-- The corresponding pointwise norm lower bound, allowing zero vectors. -/
theorem regularized_norm_coercivity_real (T : E →L[ℝ] E) (hT : 0 ≤ T)
    (lam : ℝ) (x : E) :
    lam * ‖x‖ ≤ ‖(T + lam • (1 : E →L[ℝ] E)) x‖ := by
  have hq := regularized_quadratic_coercivity_real T hT lam x
  have hc := real_inner_le_norm x ((T + lam • (1 : E →L[ℝ] E)) x)
  by_cases hx : x = 0
  · simp [hx]
  · have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith

variable [CompleteSpace E]

/-- Strictly positive regularization is an actual unit in the operator ring. -/
theorem regularized_isUnit_real (T : E →L[ℝ] E) (hT : 0 ≤ T)
    (lam : ℝ) (hlam : 0 < lam) : IsUnit (T + lam • (1 : E →L[ℝ] E)) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (c := ⟨lam, hlam.le⟩) _ hlam
  intro x
  have hq := regularized_quadratic_coercivity_real T hT lam x
  have hs : inner ℝ x ((T + lam • (1 : E →L[ℝ] E)) x) ≤
      |inner ℝ ((T + lam • (1 : E →L[ℝ] E)) x) x| := by
    rw [real_inner_comm]
    exact le_abs_self _
  change ‖x‖ ^ 2 * lam ≤ |inner ℝ ((T + lam • (1 : E →L[ℝ] E)) x) x|
  nlinarith [hq.trans hs]

/-- The actual operator-ring inverse has the standard regularization norm bound. -/
theorem regularized_inverse_norm_le_real (T : E →L[ℝ] E) (hT : 0 ≤ T)
    (lam : ℝ) (hlam : 0 < lam) :
    ‖Ring.inverse (T + lam • (1 : E →L[ℝ] E))‖ ≤ 1 / lam := by
  let a := T + lam • (1 : E →L[ℝ] E)
  have hu : IsUnit a := regularized_isUnit_real T hT lam hlam
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hx : a ((Ring.inverse a) x) = x := by
    have hi := Ring.mul_inverse_cancel a hu
    exact congrArg (fun f : E →L[ℝ] E => f x) hi
  have hbound := regularized_norm_coercivity_real T hT lam ((Ring.inverse a) x)
  change lam * ‖(Ring.inverse a) x‖ ≤ ‖a ((Ring.inverse a) x)‖ at hbound
  rw [hx] at hbound
  change ‖(Ring.inverse a) x‖ ≤ 1 / lam * ‖x‖
  rw [one_div_mul_eq_div]
  exact (le_div_iff₀ hlam).mpr (by simpa only [mul_comm] using hbound)

end KernelFoundations
