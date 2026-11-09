import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Internal exponent choices for the original scale regions

Fractional moment exponents are chosen here from the stated manuscript
parameters. They are not extra regularity hypotheses in an application.
-/

namespace KernelSeq

theorem exists_favourable_polynomial_moment_exponent {β θ a : ℝ}
    (hβ : 1 < β) (hθ : 0 < θ) (hθβ : θ < β) (ha : 0 < a) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ 1 < β * p ∧
      θ * (3 * p - 2 / β) < 1 ∧ 0 < a + 1 / β - p ∧ θ * p < 1 := by
  have hβ0 : 0 < β := by linarith
  let q := 1 / β
  have hq0 : 0 < q := one_div_pos.mpr hβ0
  have hq1 : q < 1 := (div_lt_one hβ0).mpr hβ
  have hqθ : q < 1 / θ := one_div_lt_one_div_of_lt hθ hθβ
  have hqβ : β * q = 1 := by dsimp only [q]; field_simp
  have hbound : q < min 1 (min (q + a) ((1 / θ + 2 * q) / 3)) := by
    exact lt_min hq1 (lt_min (by linarith) (by linarith))
  obtain ⟨p, hqp, hpb⟩ := exists_between hbound
  have hp1 : p < 1 := hpb.trans_le (min_le_left _ _)
  have hpa : p < q + a := hpb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hpr : p < (1 / θ + 2 * q) / 3 :=
    hpb.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpβ := mul_lt_mul_of_pos_left hqp hβ0
  have hcompat : θ * (3 * p - 2 * q) < 1 := by
    have hr : 3 * p - 2 * q < 1 / θ := by linarith
    have hh := mul_lt_mul_of_pos_left hr hθ
    have hθcancel : θ * (1 / θ) = 1 := by field_simp
    rw [hθcancel] at hh
    exact hh
  have hpθ : θ * p < 1 := by
    have hh := mul_lt_mul_of_pos_left hqp hθ
    nlinarith
  refine ⟨p, hq0.trans hqp, hp1.le, ?_, ?_, ?_, hpθ⟩
  · simpa only [hqβ] using hpβ
  · simpa only [q, div_eq_mul_inv, one_mul] using hcompat
  · change 0 < a + q - p
    linarith

theorem exists_universal_polynomial_moment_exponent {β θ a : ℝ}
    (hβ : 1 < β) (hθ : 0 < θ) (hθ1 : θ < 1) (ha : 1 - 1 / β < a) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ 1 < β * p ∧
      θ * (2 * p + 1 - 2 / β) < 1 ∧ 0 < a + 1 / β - 1 := by
  have hβ0 : 0 < β := by linarith
  let q := 1 / β
  have hq0 : 0 < q := one_div_pos.mpr hβ0
  have hq1 : q < 1 := (div_lt_one hβ0).mpr hβ
  have hθinv : 1 < 1 / θ := (one_lt_div hθ).mpr hθ1
  have hqβ : β * q = 1 := by dsimp only [q]; field_simp
  have hbound : q < min 1 (q + (1 / θ - 1) / 2) :=
    lt_min hq1 (by linarith)
  obtain ⟨p, hqp, hpb⟩ := exists_between hbound
  have hp1 : p < 1 := hpb.trans_le (min_le_left _ _)
  have hpr := hpb.trans_le (min_le_right _ _)
  have hpβ := mul_lt_mul_of_pos_left hqp hβ0
  have hcompat : θ * (2 * p + 1 - 2 * q) < 1 := by
    have hr : 2 * p + 1 - 2 * q < 1 / θ := by linarith
    have hh := mul_lt_mul_of_pos_left hr hθ
    have hθcancel : θ * (1 / θ) = 1 := by field_simp
    rw [hθcancel] at hh
    exact hh
  refine ⟨p, hq0.trans hqp, hp1.le, ?_, ?_, ?_⟩
  · simpa only [hqβ] using hpβ
  · simpa only [q, div_eq_mul_inv, one_mul] using hcompat
  · linarith

theorem exists_exponential_moment_exponent {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ θ * (3 * p) < 1 ∧ 0 < a - p ∧ θ * p < 1 := by
  have hbound : (0 : ℝ) < min 1 (min a (1 / (3 * θ))) := by positivity
  obtain ⟨p, hp, hpb⟩ := exists_between hbound
  have hp1 := hpb.trans_le (min_le_left _ _)
  have hpa := hpb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hpr := hpb.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hh := (lt_div_iff₀ (by positivity : 0 < 3 * θ)).mp hpr
  exact ⟨p, hp, hp1.le, by nlinarith, by linarith, by nlinarith⟩

end KernelSeq
