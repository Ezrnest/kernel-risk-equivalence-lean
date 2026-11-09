import KernelSeq.SpectralCounting
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual spectral counts from a coercive finite subspace

This is the finite-subspace counting argument for concrete high-dimensional
kernel models. The high-coordinate map is constructed from the actual
covariance eigenbasis; its injectivity is proved by Parseval and coercivity.
No eigenvalue-count or minmax theorem is supplied as a certificate.
-/

open MeasureTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

section AdjointTransfer

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Coercivity of `S S*` on a prediction direction gives the same coercivity
of `S* S` on its actual adjoint image. This uses genuine Cauchy--Schwarz,
without assuming that the prediction subspace is invariant. -/
theorem adjoint_image_coercivity (S : H →L[ℝ] E) {c : ℝ} (_hc : 0 < c) (x : E)
    (hcoercive : c * ‖x‖ ^ 2 ≤ ‖S.adjoint x‖ ^ 2) :
    c * ‖S.adjoint x‖ ^ 2 ≤
      inner ℝ (S.adjoint x) ((S.adjoint.comp S) (S.adjoint x)) := by
  by_cases hx : x = 0
  · simp only [hx, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, inner_zero_left, le_refl]
  let y := S (S.adjoint x)
  have ha : inner ℝ x y = ‖S.adjoint x‖ ^ 2 := by
    simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply, RCLike.re_to_real, y] using
      (S.adjoint.apply_norm_sq_eq_inner_adjoint_right x).symm
  have hcs := real_inner_mul_inner_self_le x y
  rw [ha, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hp := mul_le_mul_of_nonneg_right hcoercive (sq_nonneg ‖S.adjoint x‖)
  have hh : ‖x‖ ^ 2 * (c * ‖S.adjoint x‖ ^ 2) ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    nlinarith only [hcs, hp]
  have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)
  have hcancel := (mul_le_mul_iff_right₀ hxnorm).mp hh
  calc
    c * ‖S.adjoint x‖ ^ 2 ≤ ‖y‖ ^ 2 := hcancel
    _ = _ := by
      simpa only [y, ContinuousLinearMap.comp_apply, RCLike.re_to_real] using
        S.apply_norm_sq_eq_inner_adjoint_right (S.adjoint x)

end AdjointTransfer

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

omit [TopologicalSpace.SeparableSpace H] in
theorem featureCovariance_quadratic_eq_spectral (k : X → H) (hk : MemLp k 2 μ) (x : H) :
    inner ℝ x (populationCovariance (featureEmbedding μ k hk) x) =
      ∑' i : FeatureCovarianceIndex k hk, i.1 * (featureCovarianceBasis k hk).repr x i ^ 2 := by
  let T := populationCovariance (featureEmbedding μ k hk)
  let b := featureCovarianceBasis k hk
  have hdiag (i : FeatureCovarianceIndex k hk) : inner ℝ (b i) (T x) = i.1 * inner ℝ (b i) x := by
    have he : T (b i) = i.1 • b i :=
      compactEigenbasis_eigen T (populationCovariance_feature_isCompact μ k hk)
        (populationCovariance_isPositive (featureEmbedding μ k hk)).isSymmetric i
    calc
      inner ℝ (b i) (T x) = inner ℝ (T (b i)) x :=
        ((populationCovariance_isPositive (featureEmbedding μ k hk)).isSymmetric _ _).symm
      _ = _ := by rw [he, inner_smul_left, conj_trivial]
  rw [← b.tsum_inner_mul_inner x (T x)]
  apply tsum_congr
  intro i
  rw [hdiag, HilbertBasis.repr_apply_apply, real_inner_comm x (b i)]
  ring

omit [TopologicalSpace.SeparableSpace H] in
theorem summable_featureCovariance_quadratic (k : X → H) (hk : MemLp k 2 μ) (x : H) :
    Summable (fun i : FeatureCovarianceIndex k hk => i.1 * (featureCovarianceBasis k hk).repr x i ^ 2) := by
  let T := populationCovariance (featureEmbedding μ k hk)
  let b := featureCovarianceBasis k hk
  apply (b.summable_inner_mul_inner x (T x)).congr
  intro i
  have hdiag : inner ℝ (b i) (T x) = i.1 * inner ℝ (b i) x := by
    have he : T (b i) = i.1 • b i :=
      compactEigenbasis_eigen T (populationCovariance_feature_isCompact μ k hk)
        (populationCovariance_isPositive (featureEmbedding μ k hk)).isSymmetric i
    calc
      inner ℝ (b i) (T x) = inner ℝ (T (b i)) x :=
        ((populationCovariance_isPositive (featureEmbedding μ k hk)).isSymmetric _ _).symm
      _ = _ := by rw [he, inner_smul_left, conj_trivial]
  rw [hdiag, HilbertBasis.repr_apply_apply, real_inner_comm x (b i)]
  ring

/-- A c-coercive subspace forces at least its dimension many actual
eigenvalues above c/2. The factor two avoids any spectral-boundary convention. -/
theorem finrank_le_featureSpectralCount_of_subspace_coercive
    (k : X → H) (hk : MemLp k 2 μ) (W : Submodule ℝ H) [FiniteDimensional ℝ W]
    {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ x : W, c * ‖(x : H)‖ ^ 2 ≤
      inner ℝ (x : H) (populationCovariance (featureEmbedding μ k hk) (x : H))) :
    Module.finrank ℝ W ≤ featureSpectralCount k hk (c / 2) := by
  classical
  have hτ : 0 < c / 2 := by positivity
  let S := {i : PredictionSingularIndex (featureEmbedding μ k hk) | c / 2 ≤ i.1.1}
  letI : Fintype S := (finite_featureSpectrum_above k hk hτ).fintype
  let b := featureCovarianceBasis k hk
  let F : W →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun x i => b.repr (x : H) i.1.1
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro a x; ext i; simp }
  have hker : ∀ x : W, F x = 0 → x = 0 := by
    intro x hx
    have hhigh (i : FeatureCovarianceIndex k hk) (hi : c / 2 ≤ i.1) : b.repr (x : H) i = 0 := by
      have hpos : 0 < i.1 := hτ.trans_le hi
      let j : S := ⟨⟨i, hpos⟩, hi⟩
      have hh := congrFun hx j
      exact hh
    have hpoint (i : FeatureCovarianceIndex k hk) :
        i.1 * b.repr (x : H) i ^ 2 ≤ (c / 2) * b.repr (x : H) i ^ 2 := by
      by_cases hi : c / 2 ≤ i.1
      · rw [hhigh i hi]
        simp
      · exact mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hi)) (sq_nonneg _)
    have hsum := (summable_featureCovariance_quadratic k hk (x : H)).tsum_le_tsum
      hpoint ((hilbertBasis_coefficients_sq_summable b (x : H)).mul_left (c / 2))
    rw [← featureCovariance_quadratic_eq_spectral, tsum_mul_left,
      ← hilbertBasis_norm_sq_eq_tsum b (x : H)] at hsum
    have hh : c * ‖(x : H)‖ ^ 2 ≤ c * (‖(x : H)‖ ^ 2 / 2) := by
      nlinarith only [hcoercive x, hsum]
    have hhalf := (mul_le_mul_iff_right₀ hc).mp hh
    have hxnorm : ‖(x : H)‖ = 0 := by nlinarith [norm_nonneg (x : H)]
    exact Subtype.ext (norm_eq_zero.mp hxnorm)
  have hinj : Function.Injective F := by
    intro x y hxy
    have hz : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker (x - y) hz)
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := F) hinj
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  change Module.finrank ℝ W ≤ Nat.card S
  rw [Nat.card_eq_fintype_card]
  exact hdim

/-- A finite prediction subspace with true `S S*` coercivity supplies actual
population eigenvalues. Its adjoint image has the same dimension: injectivity
and the transferred feature coercivity are proved, not assumed. -/
theorem finrank_le_featureSpectralCount_of_prediction_subspace
    (k : X → H) (hk : MemLp k 2 μ) (W : Submodule ℝ (Lp ℝ 2 μ))
    [FiniteDimensional ℝ W] {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ x : W, c * ‖(x : Lp ℝ 2 μ)‖ ^ 2 ≤
      ‖(featureEmbedding μ k hk).adjoint (x : Lp ℝ 2 μ)‖ ^ 2) :
    Module.finrank ℝ W ≤ featureSpectralCount k hk (c / 2) := by
  let S := featureEmbedding μ k hk
  let F : W →ₗ[ℝ] H := S.adjoint.toLinearMap.comp W.subtype
  have hF : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have h := hcoercive x
    change S.adjoint (x : Lp ℝ 2 μ) = 0 at hx
    rw [hx, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    have hn : ‖(x : Lp ℝ 2 μ)‖ = 0 := by
      have := (mul_le_mul_iff_right₀ hc).mp (by simpa using h : c * ‖(x : Lp ℝ 2 μ)‖ ^ 2 ≤ c * 0)
      nlinarith [sq_nonneg ‖(x : Lp ℝ 2 μ)‖]
    exact Subtype.ext (norm_eq_zero.mp hn)
  have hdim : Module.finrank ℝ (LinearMap.range F) = Module.finrank ℝ W :=
    LinearMap.finrank_range_of_inj hF
  rw [← hdim]
  apply finrank_le_featureSpectralCount_of_subspace_coercive k hk (LinearMap.range F) hc
  intro y
  obtain ⟨x, hx⟩ := y.property
  have heq : (y : H) = S.adjoint (x : Lp ℝ 2 μ) := hx.symm
  rw [heq]
  exact adjoint_image_coercivity S hc (x : Lp ℝ 2 μ) (hcoercive x)

end
end KernelSeq
