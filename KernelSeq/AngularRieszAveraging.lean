import KernelSeq.AngularRieszExpansion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual rotation averages of the anisotropic Riesz profile

Integer harmonic orthogonality is proved by genuine interval integrals.
The actual geometric harmonic expansion is integrated using a summable
uniform majorant. No orthogonality or integration-exchange certificate is
assumed, and this module makes no Schatten multiplier norm claim.
-/

open MeasureTheory
open scoped BigOperators
namespace KernelSeq
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem angular_integral_cos_int (m : ℤ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos ((m : ℝ) * φ)) =
      if m = 0 then 2 * Real.pi else 0 := by
  by_cases hm : m = 0
  · subst m; simp
  · rw [intervalIntegral.integral_comp_mul_left Real.cos (by exact_mod_cast hm)]
    simp only [integral_cos, mul_zero, Real.sin_zero, sub_zero, smul_eq_mul, if_neg hm]
    have hs : Real.sin ((m : ℝ) * (2 * Real.pi)) = 0 := by
      have he : (m : ℝ) * (2 * Real.pi) = ((2 * m : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [he, Real.sin_int_mul_pi]
    rw [hs, mul_zero]

private theorem angular_integral_sin_int (m : ℤ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin ((m : ℝ) * φ)) = 0 := by
  by_cases hm : m = 0
  · subst m; simp
  · rw [intervalIntegral.integral_comp_mul_left Real.sin (by exact_mod_cast hm)]
    simp only [integral_sin, mul_zero, Real.cos_zero, Real.cos_int_mul_two_pi, sub_self,
      smul_eq_mul, mul_zero]

private theorem angular_integral_cos_phase (m : ℤ) (θ : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos (θ - (m : ℝ) * φ)) =
      if m = 0 then 2 * Real.pi * Real.cos θ else 0 := by
  have he : (fun φ : ℝ => Real.cos (θ - (m : ℝ) * φ)) =
      (fun φ => Real.cos θ * Real.cos ((m : ℝ) * φ) + Real.sin θ * Real.sin ((m : ℝ) * φ)) := by
    funext φ
    exact Real.cos_sub _ _
  rw [he, intervalIntegral.integral_add ((by fun_prop : Continuous (fun φ : ℝ => Real.cos θ * Real.cos ((m : ℝ) * φ))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun φ : ℝ => Real.sin θ * Real.sin ((m : ℝ) * φ))).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    angular_integral_cos_int, angular_integral_sin_int]
  by_cases hm : m = 0 <;> simp [hm, mul_comm]

private theorem angular_integral_sin_phase (m : ℤ) (θ : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin (θ - (m : ℝ) * φ)) =
      if m = 0 then 2 * Real.pi * Real.sin θ else 0 := by
  have he : (fun φ : ℝ => Real.sin (θ - (m : ℝ) * φ)) =
      (fun φ => Real.sin θ * Real.cos ((m : ℝ) * φ) - Real.cos θ * Real.sin ((m : ℝ) * φ)) := by
    funext φ
    exact Real.sin_sub _ _
  rw [he, intervalIntegral.integral_sub ((by fun_prop : Continuous (fun φ : ℝ => Real.sin θ * Real.cos ((m : ℝ) * φ))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun φ : ℝ => Real.cos θ * Real.sin ((m : ℝ) * φ))).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    angular_integral_cos_int, angular_integral_sin_int]
  by_cases hm : m = 0 <;> simp [hm, mul_comm]

/-- Actual shifted cosine/cosine orthogonality on one rotation period. -/
theorem angular_integral_shifted_cos_cos (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (ψ : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos ((m : ℝ) * (ψ - φ)) * Real.cos ((N : ℝ) * φ)) =
      if m = N then Real.pi * Real.cos ((N : ℝ) * ψ) else 0 := by
  have he : (fun φ : ℝ => 2 * (Real.cos ((m : ℝ) * (ψ - φ)) * Real.cos ((N : ℝ) * φ))) =
      (fun φ => Real.cos ((m : ℝ) * ψ - (((m : ℤ) + (N : ℤ) : ℤ) : ℝ) * φ) +
        Real.cos ((m : ℝ) * ψ - (((m : ℤ) - (N : ℤ) : ℤ) : ℝ) * φ)) := by
    funext φ
    have h := Real.two_mul_cos_mul_cos ((m : ℝ) * (ψ - φ)) ((N : ℝ) * φ)
    calc
      _ = 2 * Real.cos ((m : ℝ) * (ψ - φ)) * Real.cos ((N : ℝ) * φ) := by ring
      _ = _ := h
      _ = _ := congrArg₂ (fun a b : ℝ => Real.cos a + Real.cos b) (by push_cast; ring) (by push_cast; ring)
  have hi := congrArg (fun f : ℝ → ℝ => ∫ φ in (0 : ℝ)..(2 * Real.pi), f φ) he
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((by fun_prop : Continuous (fun φ : ℝ => Real.cos ((m : ℝ) * ψ - (((m : ℤ) + (N : ℤ) : ℤ) : ℝ) * φ))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun φ : ℝ => Real.cos ((m : ℝ) * ψ - (((m : ℤ) - (N : ℤ) : ℤ) : ℝ) * φ))).intervalIntegrable _ _),
    angular_integral_cos_phase, angular_integral_cos_phase] at hi
  have hs : (m : ℤ) + (N : ℤ) ≠ 0 := by omega
  by_cases h : m = N
  · subst m
    simp [hs] at hi ⊢
    linarith only [hi]
  · have hd : (m : ℤ) - (N : ℤ) ≠ 0 := by omega
    simp only [if_neg hs, if_neg hd, zero_add] at hi
    simp only [if_neg h]
    linarith only [hi]

/-- Actual shifted cosine/sine orthogonality, including its positive sign. -/
theorem angular_integral_shifted_cos_sin (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (ψ : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos ((m : ℝ) * (ψ - φ)) * Real.sin ((N : ℝ) * φ)) =
      if m = N then Real.pi * Real.sin ((N : ℝ) * ψ) else 0 := by
  have he : (fun φ : ℝ => 2 * (Real.cos ((m : ℝ) * (ψ - φ)) * Real.sin ((N : ℝ) * φ))) =
      (fun φ => Real.sin ((m : ℝ) * ψ - (((m : ℤ) - (N : ℤ) : ℤ) : ℝ) * φ) -
        Real.sin ((m : ℝ) * ψ - (((m : ℤ) + (N : ℤ) : ℤ) : ℝ) * φ)) := by
    funext φ
    have h := Real.two_mul_sin_mul_cos ((N : ℝ) * φ) ((m : ℝ) * (ψ - φ))
    have h1 : (N : ℝ) * φ - (m : ℝ) * (ψ - φ) =
        -((m : ℝ) * ψ - (((m : ℤ) + (N : ℤ) : ℤ) : ℝ) * φ) := by push_cast; ring
    have h2 : (N : ℝ) * φ + (m : ℝ) * (ψ - φ) =
        (m : ℝ) * ψ - (((m : ℤ) - (N : ℤ) : ℤ) : ℝ) * φ := by push_cast; ring
    rw [h1, h2, Real.sin_neg] at h
    linear_combination h
  have hi := congrArg (fun f : ℝ → ℝ => ∫ φ in (0 : ℝ)..(2 * Real.pi), f φ) he
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((by fun_prop : Continuous (fun φ : ℝ => Real.sin ((m : ℝ) * ψ - (((m : ℤ) - (N : ℤ) : ℤ) : ℝ) * φ))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun φ : ℝ => Real.sin ((m : ℝ) * ψ - (((m : ℤ) + (N : ℤ) : ℤ) : ℝ) * φ))).intervalIntegrable _ _),
    angular_integral_sin_phase, angular_integral_sin_phase] at hi
  have hs : (m : ℤ) + (N : ℤ) ≠ 0 := by omega
  by_cases h : m = N
  · subst m
    simp [hs] at hi ⊢
    linarith only [hi]
  · have hd : (m : ℤ) - (N : ℤ) ≠ 0 := by omega
    simp only [if_neg hs, if_neg hd, sub_self] at hi
    simp only [if_neg h]
    linarith only [hi]

theorem angularRieszProfile_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (angularRieszProfile r) := by
  unfold angularRieszProfile
  apply Continuous.div (by fun_prop) (by unfold angularRieszDenominator; fun_prop)
  intro ψ
  exact ne_of_gt (angularRieszDenominator_pos hr0 hr1 ψ)

/-- Genuine integration of the geometric profile expansion against any
bounded continuous scalar test function, from a summable uniform majorant. -/
theorem hasSum_integral_angularRieszProfile_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ψ : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ φ, |g φ| ≤ 1) :
    HasSum (fun k : ℕ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      ((1 - r ^ 2) * r ^ k * Real.cos (((k : ℝ) + 1) * (ψ - φ))) * g φ)
      (∫ φ in (0 : ℝ)..(2 * Real.pi), (angularRieszProfile r (ψ - φ) + r) * g φ) := by
  let μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  let F : ℕ → ℝ → ℝ := fun k φ => ((1 - r ^ 2) * r ^ k * Real.cos (((k : ℝ) + 1) * (ψ - φ))) * g φ
  let B : ℕ → ℝ := fun k => (1 - r ^ 2) * r ^ k
  have hcoef (k : ℕ) : 0 ≤ B k := by dsimp only [B]; exact mul_nonneg (by nlinarith) (pow_nonneg hr0 k)
  have hF (k : ℕ) : AEStronglyMeasurable (F k) μ :=
    ((by fun_prop : Continuous (F k))).aestronglyMeasurable
  have hb (k : ℕ) : ∀ᵐ φ ∂μ, ‖F k φ‖ ≤ B k := Filter.Eventually.of_forall fun φ => by
    have hp : |Real.cos (((k : ℝ) + 1) * (ψ - φ))| * |g φ| ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (Real.abs_cos_le_one _) (hgb φ) (abs_nonneg _) zero_le_one
    calc
      _ = B k * (|Real.cos (((k : ℝ) + 1) * (ψ - φ))| * |g φ|) := by
        dsimp only [F, B]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hcoef k)]
        ring
      _ ≤ B k * 1 := mul_le_mul_of_nonneg_left hp (hcoef k)
      _ = _ := mul_one _
  have hsum : Summable B := (summable_geometric_of_lt_one hr0 hr1).mul_left (1 - r ^ 2)
  have hi := hasSum_integral_of_dominated_convergence (μ := μ) (fun k _ => B k) hF hb
    (Filter.Eventually.of_forall fun _ => hsum) (integrable_const _)
    (Filter.Eventually.of_forall fun φ => (hasSum_angularRieszProfile hr0 hr1 (ψ - φ)).mul_right (g φ))
  simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), μ, F] using hi

/-- The actual rotation average extracts exactly the selected positive
cosine harmonic of the anisotropic reflection profile. -/
theorem angularRieszProfile_cos_average {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) (hN : 0 < N) (ψ : ℝ) :
    (1 / (2 * Real.pi)) * (∫ φ in (0 : ℝ)..(2 * Real.pi),
      angularRieszProfile r (ψ - φ) * Real.cos ((N : ℝ) * φ)) =
      ((1 - r ^ 2) * r ^ (N - 1) / 2) * Real.cos ((N : ℝ) * ψ) := by
  let C := (1 - r ^ 2) * r ^ (N - 1) * Real.pi * Real.cos ((N : ℝ) * ψ)
  have hints (k : ℕ) : (∫ φ in (0 : ℝ)..(2 * Real.pi),
      ((1 - r ^ 2) * r ^ k * Real.cos (((k : ℝ) + 1) * (ψ - φ))) * Real.cos ((N : ℝ) * φ)) =
      if k = N - 1 then C else 0 := by
    have he : (fun φ : ℝ => ((1 - r ^ 2) * r ^ k * Real.cos (((k : ℝ) + 1) * (ψ - φ))) * Real.cos ((N : ℝ) * φ)) =
        (fun φ => ((1 - r ^ 2) * r ^ k) *
          (Real.cos (((k + 1 : ℕ) : ℝ) * (ψ - φ)) * Real.cos ((N : ℝ) * φ))) := by
      funext φ
      push_cast
      ring
    rw [he, intervalIntegral.integral_const_mul,
      angular_integral_shifted_cos_cos (k + 1) N (by omega) hN ψ]
    by_cases hk : k = N - 1
    · subst k
      have hn : N - 1 + 1 = N := by omega
      rw [if_pos hn, if_pos rfl]
      dsimp only [C]
      ring
    · have hn : k + 1 ≠ N := by omega
      rw [if_neg hn, if_neg hk, mul_zero]
  have h := hasSum_integral_angularRieszProfile_mul hr0 hr1 ψ
    (fun φ => Real.cos ((N : ℝ) * φ)) (by fun_prop) (fun _ => Real.abs_cos_le_one _)
  have hs : HasSum (fun k : ℕ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      ((1 - r ^ 2) * r ^ k * Real.cos (((k : ℝ) + 1) * (ψ - φ))) * Real.cos ((N : ℝ) * φ)) C := by
    simpa only [hints] using hasSum_ite_eq (N - 1) C
  have hi := h.unique hs
  have hR : Continuous (fun φ : ℝ => angularRieszProfile r (ψ - φ) * Real.cos ((N : ℝ) * φ)) :=
    ((angularRieszProfile_continuous hr0 hr1).comp (by fun_prop)).mul (by fun_prop)
  have hconst : Continuous (fun φ : ℝ => r * Real.cos ((N : ℝ) * φ)) := by fun_prop
  have he : (fun φ : ℝ => (angularRieszProfile r (ψ - φ) + r) * Real.cos ((N : ℝ) * φ)) =
      (fun φ => angularRieszProfile r (ψ - φ) * Real.cos ((N : ℝ) * φ) + r * Real.cos ((N : ℝ) * φ)) := by
    funext φ
    ring
  rw [he, intervalIntegral.integral_add (hR.intervalIntegrable _ _) (hconst.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at hi
  have hn : (N : ℤ) ≠ 0 := by omega
  have hzero : (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos ((N : ℝ) * φ)) = 0 := by
    simpa only [Int.cast_natCast, if_neg hn] using angular_integral_cos_int (N : ℤ)
  rw [hzero, mul_zero, add_zero] at hi
  rw [hi]
  dsimp only [C]
  field_simp [Real.pi_ne_zero]

/-- The sine rotation average has the same coefficient, with its actual
positive sine phase established by interval integration. -/
theorem angularRieszProfile_sin_average {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (N : ℕ) (hN : 0 < N) (ψ : ℝ) :
    (1 / (2 * Real.pi)) * (∫ φ in (0 : ℝ)..(2 * Real.pi),
      angularRieszProfile r (ψ - φ) * Real.sin ((N : ℝ) * φ)) =
      ((1 - r ^ 2) * r ^ (N - 1) / 2) * Real.sin ((N : ℝ) * ψ) := by
  let C := (1 - r ^ 2) * r ^ (N - 1) * Real.pi * Real.sin ((N : ℝ) * ψ)
  have hints (k : ℕ) : (∫ φ in (0 : ℝ)..(2 * Real.pi),
      ((1 - r ^ 2) * r ^ k * Real.cos (((k : ℝ) + 1) * (ψ - φ))) * Real.sin ((N : ℝ) * φ)) =
      if k = N - 1 then C else 0 := by
    have he : (fun φ : ℝ => ((1 - r ^ 2) * r ^ k * Real.cos (((k : ℝ) + 1) * (ψ - φ))) * Real.sin ((N : ℝ) * φ)) =
        (fun φ => ((1 - r ^ 2) * r ^ k) *
          (Real.cos (((k + 1 : ℕ) : ℝ) * (ψ - φ)) * Real.sin ((N : ℝ) * φ))) := by
      funext φ
      push_cast
      ring
    rw [he, intervalIntegral.integral_const_mul,
      angular_integral_shifted_cos_sin (k + 1) N (by omega) hN ψ]
    by_cases hk : k = N - 1
    · subst k
      have hn : N - 1 + 1 = N := by omega
      rw [if_pos hn, if_pos rfl]
      dsimp only [C]
      ring
    · have hn : k + 1 ≠ N := by omega
      rw [if_neg hn, if_neg hk, mul_zero]
  have h := hasSum_integral_angularRieszProfile_mul hr0 hr1 ψ
    (fun φ => Real.sin ((N : ℝ) * φ)) (by fun_prop) (fun _ => Real.abs_sin_le_one _)
  have hs : HasSum (fun k : ℕ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      ((1 - r ^ 2) * r ^ k * Real.cos (((k : ℝ) + 1) * (ψ - φ))) * Real.sin ((N : ℝ) * φ)) C := by
    simpa only [hints] using hasSum_ite_eq (N - 1) C
  have hi := h.unique hs
  have hR : Continuous (fun φ : ℝ => angularRieszProfile r (ψ - φ) * Real.sin ((N : ℝ) * φ)) :=
    ((angularRieszProfile_continuous hr0 hr1).comp (by fun_prop)).mul (by fun_prop)
  have hconst : Continuous (fun φ : ℝ => r * Real.sin ((N : ℝ) * φ)) := by fun_prop
  have he : (fun φ : ℝ => (angularRieszProfile r (ψ - φ) + r) * Real.sin ((N : ℝ) * φ)) =
      (fun φ => angularRieszProfile r (ψ - φ) * Real.sin ((N : ℝ) * φ) + r * Real.sin ((N : ℝ) * φ)) := by
    funext φ
    ring
  rw [he, intervalIntegral.integral_add (hR.intervalIntegrable _ _) (hconst.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at hi
  have hzero : (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin ((N : ℝ) * φ)) = 0 := by
    simpa only [Int.cast_natCast] using angular_integral_sin_int (N : ℤ)
  rw [hzero, mul_zero, add_zero] at hi
  rw [hi]
  dsimp only [C]
  field_simp [Real.pi_ne_zero]

theorem angularRieszAnisotropy_mem (n : ℕ) :
    0 ≤ angularRieszAnisotropy n ∧ angularRieszAnisotropy n < 1 := by
  have hd : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hp : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have hl : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 :=
    (div_le_iff₀ hd).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  unfold angularRieszAnisotropy
  constructor <;> linarith

/-- The concrete anisotropy extracts its selected harmonic with half the
already proved scalar coefficient. -/
theorem angularRieszProfile_selected_cos_average (n : ℕ) (ψ : ℝ) :
    (1 / (2 * Real.pi)) * (∫ φ in (0 : ℝ)..(2 * Real.pi),
      angularRieszProfile (angularRieszAnisotropy n) (ψ - φ) * Real.cos (((n + 1 : ℕ) : ℝ) * φ)) =
      (angularRieszCoefficient n / 2) * Real.cos (((n + 1 : ℕ) : ℝ) * ψ) := by
  simpa only [Nat.add_sub_cancel, angularRieszCoefficient] using
    angularRieszProfile_cos_average (angularRieszAnisotropy_mem n).1 (angularRieszAnisotropy_mem n).2
      (n + 1) (by omega) ψ

theorem angularRieszProfile_selected_sin_average (n : ℕ) (ψ : ℝ) :
    (1 / (2 * Real.pi)) * (∫ φ in (0 : ℝ)..(2 * Real.pi),
      angularRieszProfile (angularRieszAnisotropy n) (ψ - φ) * Real.sin (((n + 1 : ℕ) : ℝ) * φ)) =
      (angularRieszCoefficient n / 2) * Real.sin (((n + 1 : ℕ) : ℝ) * ψ) := by
  simpa only [Nat.add_sub_cancel, angularRieszCoefficient] using
    angularRieszProfile_sin_average (angularRieszAnisotropy_mem n).1 (angularRieszAnisotropy_mem n).2
      (n + 1) (by omega) ψ

theorem angularRiesz_average_coefficient_lower (n : ℕ) :
    1 / (8 * ((n : ℝ) + 1)) ≤ angularRieszCoefficient n / 2 := by
  have h := div_le_div_of_nonneg_right (angularRieszCoefficient_lower n) (by norm_num : (0 : ℝ) ≤ 2)
  have he : 1 / (8 * ((n : ℝ) + 1)) = (1 / (4 * ((n : ℝ) + 1))) / 2 := by
    field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
    ring
  rw [he]
  exact h

theorem angularRieszCoefficient_pos (n : ℕ) : 0 < angularRieszCoefficient n :=
  lt_of_lt_of_le (by positivity) (angularRieszCoefficient_lower n)

/-- An actual cosine reconstruction by rotated anisotropic reflection
profiles, with no harmonic identity as a premise. -/
theorem cos_eq_angularRiesz_rotation_average (n : ℕ) (ψ : ℝ) :
    Real.cos (((n + 1 : ℕ) : ℝ) * ψ) =
      (2 / angularRieszCoefficient n) * ((1 / (2 * Real.pi)) *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), angularRieszProfile (angularRieszAnisotropy n) (ψ - φ) *
          Real.cos (((n + 1 : ℕ) : ℝ) * φ)) := by
  rw [angularRieszProfile_selected_cos_average]
  field_simp [(angularRieszCoefficient_pos n).ne']

theorem sin_eq_angularRiesz_rotation_average (n : ℕ) (ψ : ℝ) :
    Real.sin (((n + 1 : ℕ) : ℝ) * ψ) =
      (2 / angularRieszCoefficient n) * ((1 / (2 * Real.pi)) *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), angularRieszProfile (angularRieszAnisotropy n) (ψ - φ) *
          Real.sin (((n + 1 : ℕ) : ℝ) * φ)) := by
  rw [angularRieszProfile_selected_sin_average]
  field_simp [(angularRieszCoefficient_pos n).ne']

end
end KernelSeq
