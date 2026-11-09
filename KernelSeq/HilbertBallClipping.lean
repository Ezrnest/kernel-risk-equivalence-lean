import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Actual clipping of arbitrary Hilbert-valued decisions

The continuous radial projection onto a closed norm ball preserves every
target in that ball and decreases squared loss. This supplies bounded
decisions for the Gaussian-prior truncation argument without assuming that
an arbitrary measurable prediction rule has moments.
-/

namespace KernelSeq
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def clipHilbertBall (B : ℝ) (x : E) : E := (B / max B ‖x‖) • x

theorem clipHilbertBall_eq_self {B : ℝ} (hB : 0 < B) {x : E} (hx : ‖x‖ ≤ B) :
    clipHilbertBall B x = x := by simp [clipHilbertBall, max_eq_left hx, hB.ne']

theorem clipHilbertBall_norm_le {B : ℝ} (hB : 0 < B) (x : E) :
    ‖clipHilbertBall B x‖ ≤ B := by
  unfold clipHilbertBall
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (hB.trans_le (le_max_left _ _))).mpr
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hB.le

theorem clipHilbertBall_continuous {B : ℝ} (hB : 0 < B) : Continuous (clipHilbertBall (E := E) B) := by
  unfold clipHilbertBall
  have hd (x : E) : max B ‖x‖ ≠ 0 := ne_of_gt (hB.trans_le (le_max_left _ _))
  exact (continuous_const.div (continuous_const.max continuous_norm) hd).smul continuous_id

theorem clipHilbertBall_dist_le {B : ℝ} (hB : 0 < B) (x f : E) (hf : ‖f‖ ≤ B) :
    ‖clipHilbertBall B x - f‖ ≤ ‖x - f‖ := by
  by_cases hx : ‖x‖ ≤ B
  · rw [clipHilbertBall_eq_self hB hx]
  have hxB : B < ‖x‖ := lt_of_not_ge hx
  have hx0 : 0 < ‖x‖ := hB.trans hxB
  let t := B / ‖x‖
  have ht0 : 0 < t := div_pos hB hx0
  have ht1 : t ≤ 1 := (div_le_one hx0).2 hxB.le
  have htx : t * ‖x‖ = B := div_mul_cancel₀ B hx0.ne'
  have hi : inner ℝ x f ≤ ‖x‖ * B :=
    (real_inner_le_norm x f).trans (mul_le_mul_of_nonneg_left hf hx0.le)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [clipHilbertBall, max_eq_right hxB.le, norm_sub_sq_real, norm_sub_sq_real]
  change ‖t • x‖ ^ 2 - 2 * inner ℝ (t • x) f + ‖f‖ ^ 2 ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, inner_smul_left, conj_trivial]
  have hh : 0 ≤ (1-t) * (‖x‖-B) * ‖x‖ := by positivity
  have hh' : 0 ≤ (1-t) * (‖x‖ * B - inner ℝ x f) :=
    mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hi)
  nlinarith [htx]

theorem clipHilbertBall_sq_loss_le {B : ℝ} (hB : 0 < B) (x f : E) (hf : ‖f‖ ≤ B) :
    ‖clipHilbertBall B x - f‖ ^ 2 ≤ ‖x - f‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (clipHilbertBall_dist_le hB x f hf) 2

theorem clipHilbertBall_sq_loss_bound {B : ℝ} (hB : 0 < B) (x f : E) :
    ‖clipHilbertBall B x - f‖ ^ 2 ≤ 2*B^2 + 2*‖f‖^2 := by
  have hn := (norm_sub_le (clipHilbertBall B x) f).trans
    (add_le_add (clipHilbertBall_norm_le hB x) (le_refl ‖f‖))
  nlinarith [sq_nonneg (B-‖f‖), norm_nonneg (clipHilbertBall B x-f), norm_nonneg f]

end
end KernelSeq
