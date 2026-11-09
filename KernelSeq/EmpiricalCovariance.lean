import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Empirical covariance and response representer

Finite-sample operators on an arbitrary real inner product space.
The rank-one square and variance majorant enter the covariance concentration bound.
-/

open scoped BigOperators
open InnerProductSpace

namespace KernelSeq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Empirical covariance of feature vectors, including the empty-sample convention. -/
noncomputable def empiricalCovariance {n : ℕ} (x : Fin n → H) : H →L[ℝ] H :=
  (n : ℝ)⁻¹ • ∑ i, rankOne ℝ (x i) (x i)

/-- The empirical response representer for real response values. -/
noncomputable def empiricalRepresenter {n : ℕ} (x : Fin n → H) (y : Fin n → ℝ) : H :=
  (n : ℝ)⁻¹ • ∑ i, y i • x i

theorem empiricalCovariance_apply {n : ℕ} (x : Fin n → H) (h : H) :
    empiricalCovariance x h = (n : ℝ)⁻¹ • ∑ i, inner ℝ (x i) h • x i := by
  simp [empiricalCovariance]

/-- The empirical covariance is a positive operator in the infinite-dimensional space. -/
theorem empiricalCovariance_isPositive {n : ℕ} (x : Fin n → H) :
    (empiricalCovariance x).IsPositive := by
  apply ContinuousLinearMap.IsPositive.smul_of_nonneg
  · exact ContinuousLinearMap.isPositive_sum _ (fun i _ => isPositive_rankOne_self (x i))
  · positivity

/-- The empirical covariance quadratic form is the empirical mean squared prediction. -/
theorem empiricalCovariance_quadratic {n : ℕ} (x : Fin n → H) (h : H) :
    inner ℝ h (empiricalCovariance x h) =
      (n : ℝ)⁻¹ * ∑ i, (inner ℝ (x i) h) ^ 2 := by
  rw [empiricalCovariance_apply, inner_smul_right, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [inner_smul_right, real_inner_comm, pow_two]

/-- Operator norm bounded by the mean squared feature norm. -/
theorem norm_empiricalCovariance_le {n : ℕ} (x : Fin n → H) :
    ‖empiricalCovariance x‖ ≤ (n : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := by
  calc
    ‖empiricalCovariance x‖ = (n : ℝ)⁻¹ * ‖∑ i, rankOne ℝ (x i) (x i)‖ := by
      simp [empiricalCovariance, norm_smul]
    _ ≤ (n : ℝ)⁻¹ * ∑ i, ‖rankOne ℝ (x i) (x i)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = _ := by simp [pow_two]

/-- A bounded kernel's feature bound gives the manuscript's empirical spectral bound. -/
theorem norm_empiricalCovariance_le_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n → H) (κ : ℝ) (hx : ∀ i, ‖x i‖ ^ 2 ≤ κ ^ 2) :
    ‖empiricalCovariance x‖ ≤ κ ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    ‖empiricalCovariance x‖ ≤ (n : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := norm_empiricalCovariance_le x
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, κ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hx i) (by positivity)
    _ = κ ^ 2 := by simp [hn0]

/-- Exact residual identity used to express the empirical right-hand side fluctuation. -/
theorem empiricalRepresenter_sub_covariance {n : ℕ}
    (x : Fin n → H) (y : Fin n → ℝ) (h : H) :
    empiricalRepresenter x y - empiricalCovariance x h =
      empiricalRepresenter x (fun i => y i - inner ℝ (x i) h) := by
  rw [empiricalCovariance_apply]
  simp [empiricalRepresenter, sub_smul, Finset.sum_sub_distrib, smul_sub]

/-- The square of a positive rank-one operator, with no finite-dimensional restriction. -/
theorem rankOne_square (x : H) :
    (rankOne ℝ x x).comp (rankOne ℝ x x) = ‖x‖ ^ 2 • rankOne ℝ x x := by
  ext h
  simp [smul_smul, mul_comm]

/-- The rank-one variance-majorant inequality used before matrix Bernstein. -/
theorem rankOne_square_le {x : H} {L : ℝ} (hx : ‖x‖ ^ 2 ≤ L) :
    (rankOne ℝ x x).comp (rankOne ℝ x x) ≤ L • rankOne ℝ x x := by
  rw [rankOne_square, ContinuousLinearMap.le_def, ← sub_smul]
  exact (isPositive_rankOne_self x).smul_of_nonneg (sub_nonneg.mpr hx)

/-- Conjugation by an actual bounded operator preserves the rank-one formula. -/
theorem conjugate_rankOne [CompleteSpace H] (R : H →L[ℝ] H) (x : H) :
    R.comp ((rankOne ℝ x x).comp R.adjoint) = rankOne ℝ (R x) (R x) := by
  ext h
  simp [R.adjoint_inner_right]

end KernelSeq
