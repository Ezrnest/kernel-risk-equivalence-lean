import KernelSeq.WalshLpBounds
import KernelSeq.WalshRieszLp

/-!
# The proved centered matching-exponent Walsh estimate

The actual transform with its initial mean omitted differs from the proved
retained-prefix transform by two genuine conditional averages. Their
contraction and the true field triangle inequality cost a fixed constant.
No martingale, weak-type, Fourier or transform-bound certificate is assumed.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {n : ℕ} {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H] [Fintype ι]

omit [FiniteDimensional ℝ H] in
theorem finiteFieldSchattenNorm_walshPrefixAverage_le (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (k : ℕ) {q : ℝ} (hq : 2 ≤ q) :
    finiteFieldSchattenNorm b (walshPrefixAverage k F) q ≤ finiteFieldSchattenNorm b F q := by
  unfold finiteFieldSchattenNorm
  exact Real.rpow_le_rpow (finiteFieldSchattenMoment_nonneg b _ q)
    (finiteFieldSchattenMoment_walshPrefixAverage_le b F k hq) (by positivity)

/-- Actual zero-start transform with a natural-number sign sequence. -/
def walshCenteredNatTransform {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : ℕ → ℝ) (N : ℕ) (F : WalshCube n → V) : WalshCube n → V :=
  fun ω => ∑ k ∈ Finset.range N, σ k • (walshPrefixAverage (k + 1) F ω - walshPrefixAverage k F ω)

/-- Exact initial-mean correction, keeping both conditional averages. -/
theorem walshCenteredNatTransform_succ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : ℕ → ℝ) (N : ℕ) (F : WalshCube n → V) :
    walshCenteredNatTransform σ (N + 1) F =
      walshPrefixTransformLinearMap (fun k => σ (k + 1)) N F +
        (σ 0 - 1) • walshPrefixAverage 1 F + (-σ 0) • walshPrefixAverage 0 F := by
  funext ω
  simp only [walshCenteredNatTransform, walshPrefixTransformLinearMap,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    walshPrefixLinearMap_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply]
  rw [Finset.sum_range_succ']
  module

/-- The actual centered natural-index transform has a linear-in-q bound. -/
theorem walshCenteredNatTransform_dyadic_norm_le (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N m : ℕ) :
    finiteFieldSchattenNorm b (walshCenteredNatTransform σ N F) (dyadicSchattenExponent m) ≤
      (133 * dyadicSchattenExponent m) * finiteFieldSchattenNorm b F (dyadicSchattenExponent m) := by
  let q := dyadicSchattenExponent m
  have hq : 2 ≤ q := dyadicSchattenExponent_ge_two m
  have hFn := finiteFieldSchattenNorm_nonneg b F q
  cases N with
  | zero =>
    have hz : walshCenteredNatTransform σ 0 F = 0 := by funext ω; simp only [walshCenteredNatTransform, Finset.range_zero, Finset.sum_empty, Pi.zero_apply]
    rw [hz, finiteFieldSchattenNorm_zero b hq]
    positivity
  | succ N =>
    have hT := walshPrefixTransformLinearMap_dyadic_norm_le b F (fun k => σ (k + 1))
      (fun k => hσ (k + 1)) N m
    have hP := finiteFieldSchattenNorm_walshPrefixAverage_le b F 1 hq
    have hP0 := finiteFieldSchattenNorm_walshPrefixAverage_le b F 0 hq
    have habs : |σ 0 - 1| ≤ 2 := by
      have h := abs_sub (σ 0) 1
      simpa only [hσ 0, abs_one, one_add_one_eq_two] using h
    rw [walshCenteredNatTransform_succ]
    have htri := (finiteFieldSchattenNorm_add_le b
      (walshPrefixTransformLinearMap (fun k => σ (k + 1)) N F + (σ 0 - 1) • walshPrefixAverage 1 F)
      ((-σ 0) • walshPrefixAverage 0 F) hq).trans (add_le_add
        (finiteFieldSchattenNorm_add_le b _ _ hq) le_rfl)
    rw [finiteFieldSchattenNorm_smul b _ _ hq, finiteFieldSchattenNorm_smul b _ _ hq,
      abs_neg, hσ 0, one_mul] at htri
    have hcor := (mul_le_mul_of_nonneg_right habs (finiteFieldSchattenNorm_nonneg b _ q)).trans
      (mul_le_mul_of_nonneg_left hP (by norm_num : 0 ≤ (2 : ℝ)))
    change _ ≤ 133 * q * finiteFieldSchattenNorm b F q
    change finiteFieldSchattenNorm b (walshPrefixTransformLinearMap (fun k => σ (k + 1)) N F) q ≤
      130 * q * finiteFieldSchattenNorm b F q at hT
    nlinarith [mul_nonneg (show 0 ≤ q - 1 by linarith) hFn]

/-- Extend the actual finite signs by one outside the cube's coordinates. -/
def walshFiniteSignExtend (σ : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then σ ⟨k, hk⟩ else 1

theorem walshFiniteSignExtend_abs (σ : Fin n → ℝ) (hσ : ∀ j, |σ j| = 1) (k : ℕ) :
    |walshFiniteSignExtend σ k| = 1 := by
  unfold walshFiniteSignExtend
  split_ifs with hk
  · exact hσ ⟨k, hk⟩
  · exact abs_one

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem walshCenteredTransform_eq_nat (σ : Fin n → ℝ) (F : WalshCube n → H →L[ℝ] H) :
    walshCenteredTransform σ F = walshCenteredNatTransform (walshFiniteSignExtend σ) n F := by
  funext ω
  unfold walshCenteredTransform walshCenteredNatTransform
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [walshFiniteSignExtend, dif_pos j.isLt, Fin.eta]

/-- The actual finite-sign centered transform, including the zero-bit cube. -/
theorem walshCenteredTransform_dyadic_moment_le (b : HilbertBasis ι ℝ H)
    (n m : ℕ) (σ : Fin n → ℝ) (hσ : ∀ j, |σ j| = 1) (F : WalshCube n → H →L[ℝ] H) :
    finiteFieldSchattenMoment b (walshCenteredTransform σ F) (dyadicSchattenExponent m) ≤
      (133 * dyadicSchattenExponent m) ^ (dyadicSchattenExponent m) *
        finiteFieldSchattenMoment b F (dyadicSchattenExponent m) := by
  rw [walshCenteredTransform_eq_nat]
  have hq := dyadicSchattenExponent_ge_two m
  have hq0 : 0 < dyadicSchattenExponent m := by linarith
  have h := Real.rpow_le_rpow (finiteFieldSchattenNorm_nonneg b _ _)
    (walshCenteredNatTransform_dyadic_norm_le b F (walshFiniteSignExtend σ)
      (walshFiniteSignExtend_abs σ hσ) n m) hq0.le
  rwa [Real.mul_rpow (by positivity) (finiteFieldSchattenNorm_nonneg b F _),
    finiteFieldSchattenNorm_rpow b _ hq0, finiteFieldSchattenNorm_rpow b F hq0] at h

/-- A genuine constructor discharges the precise general Walsh estimate
used by the matching-exponent Riesz representation. -/
theorem finiteWalshLpTransformBound_proved : FiniteWalshLpTransformBound 133 where
  constant_nonneg := by norm_num
  bound := by
    intro ι _ H _ _ _ b n m σ hσ F
    letI : FiniteDimensional ℝ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
    exact walshCenteredTransform_dyadic_moment_le b n m σ hσ F

end
end KernelSeq
