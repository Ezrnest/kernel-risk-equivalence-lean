import KernelFoundations.CompactSpectral
import Mathlib.Tactic.Module

/-!
# Bounded spectral multipliers and covariance intertwining
-/

namespace KernelFoundations

variable {H E ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- Bounded operators agreeing on a Hilbert basis agree everywhere, including
for an infinite or uncountable basis. -/
theorem continuousLinearMap_eq_of_hilbertBasis (b : HilbertBasis ι ℝ H)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : H →L[ℝ] E) (h : ∀ i, F (b i) = G (b i)) : F = G := by
  ext x
  have hF := F.hasSum (b.hasSum_repr x)
  have hG := G.hasSum (b.hasSum_repr x)
  have hterms : (fun i => F (b.repr x i • b i)) =
      (fun i => G (b.repr x i • b i)) := by
    funext i
    simp only [map_smul, h i]
  exact hF.unique (hterms ▸ hG)

/-- The scalar profile is needed only on the true nonnegative spectrum. -/
theorem compact_profile_weight_bound (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ) (K : ℝ)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K)
    (i : CompactSpectralIndex T) : ‖φ i.1‖ ≤ K := by
  apply hφ
  exact ⟨compactEigenvalue_nonneg T hc hp i,
    (le_abs_self i.1).trans (compactEigenvalue_norm_le T hc hp.isSymmetric i)⟩

/-- A bounded scalar profile on the spectrum defines a continuous linear
operator on the real Hilbert space. -/
noncomputable def compactSpectralMultiplier (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) : H →L[ℝ] H :=
  hilbertDiagonal (compactEigenbasis T hc hp.isSymmetric) (fun i => φ i.1) K hK
    (compact_profile_weight_bound T hc hp φ K hφ)

@[simp]
theorem compactSpectralMultiplier_repr (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K)
    (v : H) (i : CompactSpectralIndex T) :
    (compactEigenbasis T hc hp.isSymmetric).repr
      (compactSpectralMultiplier T hc hp φ K hK hφ v) i =
      φ i.1 * (compactEigenbasis T hc hp.isSymmetric).repr v i :=
  hilbertDiagonal_repr _ _ _ _ _ _ _

theorem compactSpectralMultiplier_norm_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) :
    ‖compactSpectralMultiplier T hc hp φ K hK hφ‖ ≤ K :=
  hilbertDiagonal_norm_le _ _ _ _ _

/-- Spectral action on every eigenvector, not just the selected basis vectors. -/
theorem compactSpectralMultiplier_eigen (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K)
    {v : H} {t : ℝ} (hv : T v = t • v) :
    compactSpectralMultiplier T hc hp φ K hK hφ v = φ t • v := by
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  rw [compactSpectralMultiplier_repr]
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hcoeff : i.1 * (compactEigenbasis T hc hp.isSymmetric).repr v i =
      t * (compactEigenbasis T hc hp.isSymmetric).repr v i := by
    rw [← compactEigenbasis_repr_apply T hc hp.isSymmetric, hv]
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i.1 = t
  · rw [hi]
  · have hz : (compactEigenbasis T hc hp.isSymmetric).repr v i = 0 := by
      apply (mul_eq_zero.mp (show (i.1 - t) *
        (compactEigenbasis T hc hp.isSymmetric).repr v i = 0 by nlinarith)).resolve_left
      exact sub_ne_zero.mpr hi
    simp only [hz, mul_zero]


end KernelFoundations
