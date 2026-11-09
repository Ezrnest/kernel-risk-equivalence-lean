import KernelSeq.CompactSpectral
import KernelSeq.ResidualFilter
import Mathlib.Tactic.Module

/-!
# Bounded spectral profiles and the population residual identity

An actual bounded spectral multiplier on a positive compact real-Hilbert
operator, constructed from the spectral basis rather than an assumed real CFC
instance. Discontinuous bounded profiles are allowed. Measurability in a
varying/random operator is a separate obligation.

The population residual identity follows by spectral intertwining across
the bounded feature embedding. Both covariance operators are adjoint products.
-/

namespace KernelSeq

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

/-- Bounded measurable profiles from the manuscript act on the actual real
Hilbert space. Borel regularity is unnecessary for constructing a single map. -/
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

section Intertwining

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Actual spectral residual identity for `T = S* S` and `L = S S*`.
It allows a nontrivial null space and a discontinuous profile. -/
theorem population_residual_spectral_identity (S : H →L[ℝ] E)
    (hcT : IsCompactOperator (S.adjoint.comp S))
    (hcL : IsCompactOperator (S.comp S.adjoint))
    (φ : ℝ → ℝ) (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.adjoint.comp S‖, |φ t| ≤ K)
    (hψ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖,
      |ResidualFilter.residual φ t| ≤ B) (f : E) :
    f - S (compactSpectralMultiplier (S.adjoint.comp S) hcT
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ K hK hφ (S.adjoint f)) =
    compactSpectralMultiplier (S.comp S.adjoint) hcL
      (ContinuousLinearMap.isPositive_self_comp_adjoint S)
      (ResidualFilter.residual φ) B hB hψ f := by
  let T := S.adjoint.comp S
  let L := S.comp S.adjoint
  have hpT : T.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self S
  have hpL : L.IsPositive := ContinuousLinearMap.isPositive_self_comp_adjoint S
  let F := compactSpectralMultiplier T hcT hpT φ K hK hφ
  let Ψ := compactSpectralMultiplier L hcL hpL (ResidualFilter.residual φ) B hB hψ
  have heq : (ContinuousLinearMap.id ℝ E - S.comp (F.comp S.adjoint)) = Ψ := by
    apply continuousLinearMap_eq_of_hilbertBasis
      (compactEigenbasis L hcL hpL.isSymmetric)
    intro i
    have he := compactEigenbasis_eigen L hcL hpL.isSymmetric i
    have hadj : T (S.adjoint (compactEigenbasis L hcL hpL.isSymmetric i)) =
        i.1 • S.adjoint (compactEigenbasis L hcL hpL.isSymmetric i) := by
      change S.adjoint (L (compactEigenbasis L hcL hpL.isSymmetric i)) = _
      rw [he, map_smul]
    have hFe := compactSpectralMultiplier_eigen T hcT hpT φ K hK hφ hadj
    have hΨe := compactSpectralMultiplier_eigen L hcL hpL
      (ResidualFilter.residual φ) B hB hψ he
    change compactEigenbasis L hcL hpL.isSymmetric i -
      S (F (S.adjoint (compactEigenbasis L hcL hpL.isSymmetric i))) = _
    rw [hFe, map_smul]
    change compactEigenbasis L hcL hpL.isSymmetric i -
      φ i.1 • L (compactEigenbasis L hcL hpL.isSymmetric i) = _
    rw [he, hΨe]
    simp only [ResidualFilter.residual, ResidualFilter.shrinkage]
    module
  exact congrArg (fun A : E →L[ℝ] E => A f) heq

end Intertwining

namespace ResidualFilter

/-- A nonempty spectral interval forces the common size constant to be nonnegative. -/
theorem Contract.constant_nonneg {lam M ρ A : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) (hM : 0 ≤ M) : 0 ≤ A :=
  (abs_nonneg _).trans (h.spectral_size hlam ⟨le_rfl, hM⟩).1

/-- The manuscript's size condition supplies the bounded inverse profile needed
for actual operator construction, without assuming continuity of that profile. -/
theorem Contract.profile_bound {lam M ρ A : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) M) : |φ t| ≤ A / lam := by
  have hs : (t + lam) * |φ t| ≤ A := by
    simpa only [abs_mul, abs_of_nonneg (add_nonneg ht.1 hlam.le)] using
      (h.spectral_size hlam ht).1
  apply (le_div_iff₀ hlam).mpr
  nlinarith [mul_nonneg ht.1 (abs_nonneg (φ t))]

theorem SpectralFilter.residual_abs_le_one {M : ℝ} {φ : ℝ → ℝ}
    (h : SpectralFilter M φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |residual φ t| ≤ 1 := by
  have hq := h.shrinkage_mem t ht
  rw [residual, abs_of_nonneg (sub_nonneg.mpr hq.2)]
  linarith [hq.1]

end ResidualFilter

/-- The paper's inverse filter, now a constructed real bounded operator.
All constants and spectral bounds are precisely the existing scalar contract. -/
noncomputable def compactFilterOperator (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) : H →L[ℝ] H :=
  compactSpectralMultiplier T hc hp φ (A / lam)
    (div_nonneg (h.constant_nonneg hlam ((norm_nonneg T).trans hM)) hlam.le)
    (fun _ ht => h.profile_bound hlam ⟨ht.1, ht.2.trans hM⟩)

/-- The paper's bounded residual profile on an actual positive compact operator. -/
noncomputable def compactResidualOperator (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {M : ℝ} (hM : ‖T‖ ≤ M) (h : ResidualFilter.SpectralFilter M φ) : H →L[ℝ] H :=
  compactSpectralMultiplier T hc hp (ResidualFilter.residual φ) 1 zero_le_one
    (fun _ ht => h.residual_abs_le_one ⟨ht.1, ht.2.trans hM⟩)

/-- Spectral intertwining specialized to exactly the manuscript's filter
assumptions; no bounded-profile or spectral-residual certificates are added. -/
theorem population_residual_filter_identity
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : H →L[ℝ] E)
    (hcT : IsCompactOperator (S.adjoint.comp S))
    (hcL : IsCompactOperator (S.comp S.adjoint))
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hMT : ‖S.adjoint.comp S‖ ≤ M) (hML : ‖S.comp S.adjoint‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) (f : E) :
    f - S (compactFilterOperator (S.adjoint.comp S) hcT
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hMT h (S.adjoint f)) =
    compactResidualOperator (S.comp S.adjoint) hcL
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hML hf f :=
  population_residual_spectral_identity S hcT hcL φ (A / lam) 1
    (div_nonneg (h.constant_nonneg hlam ((norm_nonneg _).trans hMT)) hlam.le) zero_le_one
    (fun _ ht => h.profile_bound hlam ⟨ht.1, ht.2.trans hMT⟩)
    (fun _ ht => hf.residual_abs_le_one ⟨ht.1, ht.2.trans hML⟩) f

end KernelSeq
