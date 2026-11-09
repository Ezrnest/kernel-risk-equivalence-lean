import KernelSeq.SpectralEnergy

/-!
# Supported targets and positive-spectrum energies

The compact spectral basis includes the entire null space, even when the
prediction space is not separable. A target in the closure of the actual
prediction range is orthogonal to that null space. Consequently its spectral
energies can be indexed by the positive eigenvalues alone, exactly as in the
manuscript. No separability assumption is placed on the prediction space.
-/

namespace KernelSeq

open Submodule TopologicalSpace

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The manuscript indexes the positive eigenvalues, with their multiplicities. -/
abbrev PositiveSpectralIndex (T : E →L[ℝ] E) :=
  {i : CompactSpectralIndex T // 0 < i.1}

/-- The source support used in the manuscript agrees with the closure of the
actual prediction range, without any closed-range assumption. -/
theorem closure_range_self_comp_adjoint (S : H →L[ℝ] E) :
    (S.comp S.adjoint).range.topologicalClosure = S.range.topologicalClosure := by
  calc
    (S.comp S.adjoint).range.topologicalClosure = (S.comp S.adjoint).kerᗮ := by
      simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
        using (S.comp S.adjoint).orthogonal_ker.symm
    _ = S.adjoint.kerᗮ := by rw [S.ker_self_comp_adjoint]
    _ = S.range.topologicalClosure := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using S.adjoint.orthogonal_ker

/-- Zero eigenvectors of the actual population operator are orthogonal to every
target in the closure of the prediction range. -/
theorem inner_zero_of_mem_closure_range_of_self_comp_adjoint_eq_zero
    (S : H →L[ℝ] E) {f v : E} (hf : f ∈ S.range.topologicalClosure)
    (hv : (S.comp S.adjoint) v = 0) : inner ℝ v f = 0 := by
  have hvker : v ∈ S.adjoint.ker := by
    rw [← S.ker_self_comp_adjoint]
    exact hv
  have hvorth : v ∈ S.rangeᗮ := by
    rw [S.orthogonal_range]
    exact hvker
  have hvcl : v ∈ S.range.topologicalClosureᗮ := by
    simpa only [Submodule.orthogonal_closure] using hvorth
  exact (Submodule.mem_orthogonal' _ _).mp hvcl f hf

/-- An actual supported target has zero coordinates in the zero eigenspace. -/
theorem compactEigenbasis_zero_coefficient (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) {f : E}
    (hf : f ∈ S.range.topologicalClosure) (i : CompactSpectralIndex (S.comp S.adjoint))
    (hi : i.1 = 0) :
    (compactEigenbasis (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i = 0 := by
  rw [HilbertBasis.repr_apply_apply]
  apply inner_zero_of_mem_closure_range_of_self_comp_adjoint_eq_zero S hf
  rw [compactEigenbasis_eigen, hi, zero_smul]

/-- Every weighted coefficient series of a supported target reduces exactly to
the positive spectrum. The equality needs no countability or summability premise. -/
theorem tsum_spectral_coefficients_eq_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) {f : E}
    (hf : f ∈ S.range.topologicalClosure) (w : ℝ → ℝ) :
    (∑' i : CompactSpectralIndex (S.comp S.adjoint),
      w i.1 * (compactEigenbasis (S.comp S.adjoint) hc
        (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i ^ 2) =
      ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
        w i.1.1 * (compactEigenbasis (S.comp S.adjoint) hc
          (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 := by
  symm
  apply tsum_subtype_eq_of_support_subset
    (s := {i : CompactSpectralIndex (S.comp S.adjoint) | 0 < i.1})
    (f := fun i => w i.1 * (compactEigenbasis (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i ^ 2)
  intro i hi
  change 0 < i.1
  have hn := compactEigenvalue_nonneg (S.comp S.adjoint) hc
    (ContinuousLinearMap.isPositive_self_comp_adjoint S) i
  by_contra hnpos
  have hz : i.1 = 0 := le_antisymm (le_of_not_gt hnpos) hn
  have hc0 := compactEigenbasis_zero_coefficient S hc hf i hz
  exact hi (by simp only [hc0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero])

/-- Parseval for supported targets, with the manuscript's positive-spectrum index. -/
theorem norm_sq_eq_positive_spectral_coefficients (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) {f : E}
    (hf : f ∈ S.range.topologicalClosure) :
    ‖f‖ ^ 2 = ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
      (compactEigenbasis (S.comp S.adjoint) hc
        (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 := by
  rw [hilbertBasis_norm_sq_eq_tsum (compactEigenbasis (S.comp S.adjoint) hc
    (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric)]
  simpa only [one_mul] using tsum_spectral_coefficients_eq_positive S hc hf (fun _ => 1)

/-- Square summability on the positive spectrum follows from actual coordinates;
it is not an additional target assumption. -/
theorem summable_positive_spectral_coefficients (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (f : E) :
    Summable (fun i : PositiveSpectralIndex (S.comp S.adjoint) =>
      (compactEigenbasis (S.comp S.adjoint) hc
        (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2) := by
  exact (hilbertBasis_coefficients_sq_summable (compactEigenbasis (S.comp S.adjoint) hc
    (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric) f).subtype _

/-- Every bounded multiplier has a genuinely summable positive spectral energy,
even if the full ambient Hilbert basis is uncountable. -/
theorem compactSpectralMultiplier_positive_energy_summable (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K) (f : E) :
    Summable (fun i : PositiveSpectralIndex (S.comp S.adjoint) =>
      φ i.1.1 ^ 2 * (compactEigenbasis (S.comp S.adjoint) hc
        (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2) := by
  have hs := hilbertBasis_coefficients_sq_summable (compactEigenbasis (S.comp S.adjoint) hc
    (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric)
    (compactSpectralMultiplier (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ f)
  simp_rw [compactSpectralMultiplier_repr, mul_pow] at hs
  exact hs.subtype _

/-- The positive-spectrum regularized source energy is summable for every target. -/
theorem regularized_target_positive_summable (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (f : E)
    {lam α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) :
    Summable (fun i : PositiveSpectralIndex (S.comp S.adjoint) =>
      (lam / (i.1.1 + lam)) ^ α * (compactEigenbasis (S.comp S.adjoint) hc
        (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2) := by
  apply summable_regularized_coefficients (M := ‖S.comp S.adjoint‖)
    (fun i => i.1.1) _ hlam hα _
    (summable_positive_spectral_coefficients S hc f)
  intro i
  exact ⟨i.2.le, (le_abs_self i.1.1).trans
    (compactEigenvalue_norm_le (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric i.1)⟩

/-- The actual bounded multiplier energy has no contribution from the null space
when the target has the manuscript's source support. -/
theorem compactSpectralMultiplier_norm_sq_eq_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |φ t| ≤ K)
    {f : E} (hf : f ∈ S.range.topologicalClosure) :
    ‖compactSpectralMultiplier (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ K hK hφ f‖ ^ 2 =
      ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
        φ i.1.1 ^ 2 * (compactEigenbasis (S.comp S.adjoint) hc
          (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 := by
  rw [compactSpectralMultiplier_norm_sq_eq_tsum]
  exact tsum_spectral_coefficients_eq_positive S hc hf (fun t => φ t ^ 2)

/-- The manuscript's residual bias is exactly a positive-spectrum energy. -/
theorem compactResidualOperator_norm_sq_eq_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ)
    {M : ℝ} (hM : ‖S.comp S.adjoint‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) {f : E}
    (hf : f ∈ S.range.topologicalClosure) :
    ‖compactResidualOperator (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hM hfilter f‖ ^ 2 =
      ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
        ResidualFilter.residual φ i.1.1 ^ 2 * (compactEigenbasis (S.comp S.adjoint) hc
          (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 := by
  exact compactSpectralMultiplier_norm_sq_eq_positive S hc _ _ _ _ hf

/-- The auxiliary weighted residual energy also reduces to the positive spectrum. -/
theorem compactResidualWeightOperator_norm_sq_eq_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ)
    {lam M α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α)
    (hM : ‖S.comp S.adjoint‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) {f : E}
    (hf : f ∈ S.range.topologicalClosure) :
    ‖compactResidualWeightOperator (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα hM hfilter f‖ ^ 2 =
      ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
        residualWeight lam α φ i.1.1 ^ 2 * (compactEigenbasis (S.comp S.adjoint) hc
          (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 := by
  exact compactSpectralMultiplier_norm_sq_eq_positive S hc _ _ _ _ hf

/-- The regularized source series has exactly the manuscript's positive indices. -/
theorem regularized_target_series_eq_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) {f : E}
    (hf : f ∈ S.range.topologicalClosure) (lam α : ℝ) :
    (∑' i : CompactSpectralIndex (S.comp S.adjoint),
      (lam / (i.1 + lam)) ^ α * (compactEigenbasis (S.comp S.adjoint) hc
        (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i ^ 2) =
      ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
        (lam / (i.1.1 + lam)) ^ α * (compactEigenbasis (S.comp S.adjoint) hc
          (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 :=
  tsum_spectral_coefficients_eq_positive S hc hf (fun t => (lam / (t + lam)) ^ α)

/-- The actual weighted target estimate now has exactly the positive-spectrum
source energy used in the paper, with summability inherited from Parseval. -/
theorem compactResidualWeightOperator_norm_sq_le_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) (φ : ℝ → ℝ)
    {lam M ρ A α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α) (hαρ : α / 2 ≤ ρ)
    (hM : ‖S.comp S.adjoint‖ ≤ M) (hfilter : ResidualFilter.SpectralFilter M φ)
    (h : ResidualFilter.Contract lam M ρ A φ) {f : E}
    (hf : f ∈ S.range.topologicalClosure) :
    ‖compactResidualWeightOperator (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα hM hfilter f‖ ^ 2 ≤
      (A + 1) ^ 2 * ∑' i : PositiveSpectralIndex (S.comp S.adjoint),
        (lam / (i.1.1 + lam)) ^ α * (compactEigenbasis (S.comp S.adjoint) hc
          (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric).repr f i.1 ^ 2 := by
  rw [← regularized_target_series_eq_positive S hc hf]
  exact compactResidualWeightOperator_norm_sq_le (S.comp S.adjoint) hc
    (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα hαρ hM hfilter h f

/-- Positive-eigenvalue basis vectors lie in the actual prediction range,
not merely in its closure. -/
theorem compactEigenbasis_mem_range_of_positive (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint))
    (i : PositiveSpectralIndex (S.comp S.adjoint)) :
    compactEigenbasis (S.comp S.adjoint) hc
      (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric i.1 ∈ S.range := by
  refine ⟨i.1.1⁻¹ • S.adjoint (compactEigenbasis (S.comp S.adjoint) hc
    (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric i.1), ?_⟩
  rw [map_smul]
  change i.1.1⁻¹ • (S.comp S.adjoint) _ = _
  rw [compactEigenbasis_eigen, smul_smul, inv_mul_cancel₀ (ne_of_gt i.2), one_smul]

/-- Only the positive spectral index is countable when the RKHS is separable.
The prediction space, and its zero eigenspace, may remain nonseparable. -/
theorem positiveSpectralIndex_countable [SeparableSpace H] (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.comp S.adjoint)) :
    Countable (PositiveSpectralIndex (S.comp S.adjoint)) := by
  let V := S.range.topologicalClosure
  have hsep : TopologicalSpace.IsSeparable (V : Set E) := by
    change TopologicalSpace.IsSeparable (closure (Set.range S))
    exact (TopologicalSpace.isSeparable_range S.continuous).closure
  letI : SeparableSpace V := hsep.separableSpace
  let b := compactEigenbasis (S.comp S.adjoint) hc
    (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric
  let v : PositiveSpectralIndex (S.comp S.adjoint) → V := fun i =>
    ⟨b i.1, S.range.le_topologicalClosure (compactEigenbasis_mem_range_of_positive S hc i)⟩
  have hd : Pairwise (fun i j : PositiveSpectralIndex (S.comp S.adjoint) =>
      Disjoint (Metric.ball (v i) (1 / 2 : ℝ)) (Metric.ball (v j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs := norm_sub_sq_real (b i.1) (b j.1)
    rw [b.orthonormal.norm_eq_one i.1, b.orthonormal.norm_eq_one j.1,
      b.orthonormal.inner_eq_zero (fun h => hij (Subtype.ext h))] at hs
    rw [dist_eq_norm]
    change 1 / 2 + 1 / 2 ≤ ‖b i.1 - b j.1‖
    nlinarith [norm_nonneg (b i.1 - b j.1)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.nonempty_ball.mpr (by norm_num))

end KernelSeq
