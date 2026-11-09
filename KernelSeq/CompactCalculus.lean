import KernelFoundations.CompactCalculus
import KernelSeq.CompactSpectral
import KernelSeq.ResidualFilter

/-!
# Spectral operators for residual filters
-/

namespace KernelSeq

export KernelFoundations (
  continuousLinearMap_eq_of_hilbertBasis compact_profile_weight_bound
  compactSpectralMultiplier compactSpectralMultiplier_repr
  compactSpectralMultiplier_norm_le compactSpectralMultiplier_eigen
)

variable {H E ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

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
