import KernelFoundations.TargetSupport

/-!
# The actual positive singular system of the prediction embedding

Starting with the constructed eigenbasis of `T = S* S`, its positive spectral
vectors give `e_i = S v_i / sqrt(t_i)`. They form a Hilbert basis of the actual
closed prediction range and are eigenvectors of `L = S S*`. No separability of
the ambient prediction space, nor existence of a singular basis, is assumed.
-/

namespace KernelFoundations

open Submodule TopologicalSpace

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The positive covariance eigenvalues, retaining the actual multiplicities. -/
abbrev PredictionSingularIndex (S : H →L[ℝ] E) :=
  PositiveSpectralIndex (S.adjoint.comp S)

/-- The prediction subspace used by the source support assumption. -/
abbrev PredictionRange (S : H →L[ℝ] E) := S.range.topologicalClosure

noncomputable def singularDomainBasis (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) :
    HilbertBasis (CompactSpectralIndex (S.adjoint.comp S)) ℝ H :=
  compactEigenbasis (S.adjoint.comp S) hc
    (ContinuousLinearMap.isPositive_adjoint_comp_self S).isSymmetric

/-- The normalized image lies in the actual prediction range, even before
taking its closure. Only positive eigenvalues are divided by their square root. -/
noncomputable def predictionSingularVector (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (i : PredictionSingularIndex S) :
    PredictionRange S :=
  ⟨(Real.sqrt i.1.1)⁻¹ • S (singularDomainBasis S hc i.1),
    S.range.le_topologicalClosure ⟨(Real.sqrt i.1.1)⁻¹ • singularDomainBasis S hc i.1,
      by rw [map_smul]; rfl⟩⟩

@[simp]
theorem predictionSingularVector_coe (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (i : PredictionSingularIndex S) :
    (predictionSingularVector S hc i : E) =
      (Real.sqrt i.1.1)⁻¹ • S (singularDomainBasis S hc i.1) := rfl

/-- The actual adjoint products determine all image-vector inner products. -/
theorem singularDomainBasis_image_inner (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S))
    (i j : CompactSpectralIndex (S.adjoint.comp S)) :
    inner ℝ (S (singularDomainBasis S hc i)) (S (singularDomainBasis S hc j)) =
      j.1 * inner ℝ (singularDomainBasis S hc i) (singularDomainBasis S hc j) := by
  rw [← S.adjoint_inner_right]
  change inner ℝ (singularDomainBasis S hc i)
    ((S.adjoint.comp S) (singularDomainBasis S hc j)) = _
  rw [singularDomainBasis, compactEigenbasis_eigen, inner_smul_right]

/-- The normalized positive images are genuinely orthonormal in the closed
prediction range. The ambient space may be nonseparable. -/
theorem predictionSingularVector_orthonormal (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) :
    Orthonormal ℝ (predictionSingularVector S hc) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℝ ((Real.sqrt i.1.1)⁻¹ • S (singularDomainBasis S hc i.1))
    ((Real.sqrt j.1.1)⁻¹ • S (singularDomainBasis S hc j.1)) = _
  rw [inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  rw [singularDomainBasis_image_inner]
  by_cases hij : i = j
  · subst j
    simp only [real_inner_self_eq_norm_sq,
      (singularDomainBasis S hc).orthonormal.norm_eq_one, one_pow, mul_one]
    have hs : Real.sqrt i.1.1 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr i.2)
    field_simp
    simpa using (Real.sq_sqrt i.2.le).symm
  · rw [(singularDomainBasis S hc).orthonormal.inner_eq_zero
      (fun h => hij (Subtype.ext h)), if_neg hij]
    simp

/-- Zero covariance eigenvectors map to zero under the actual embedding. -/
theorem singularDomainBasis_image_eq_zero (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S))
    (i : CompactSpectralIndex (S.adjoint.comp S)) (hi : i.1 = 0) :
    S (singularDomainBasis S hc i) = 0 := by
  have he : (S.adjoint.comp S) (singularDomainBasis S hc i) =
      i.1 • singularDomainBasis S hc i := compactEigenbasis_eigen _ hc
        (ContinuousLinearMap.isPositive_adjoint_comp_self S).isSymmetric i
  have hn : ‖S (singularDomainBasis S hc i)‖ ^ 2 = 0 := by
    rw [S.apply_norm_sq_eq_inner_adjoint_right]
    change inner ℝ (singularDomainBasis S hc i)
      ((S.adjoint.comp S) (singularDomainBasis S hc i)) = 0
    rw [he, hi, zero_smul, inner_zero_right]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

/-- Completeness in the actual prediction range is derived from the full
domain eigenbasis, with the zero domain eigenspace handled explicitly. -/
theorem predictionSingularVector_orthogonal_eq_bot (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) :
    (span ℝ (Set.range (predictionSingularVector S hc)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  have hcoeff (i : CompactSpectralIndex (S.adjoint.comp S)) :
      (singularDomainBasis S hc).repr (S.adjoint (z : E)) i = 0 := by
    rw [HilbertBasis.repr_apply_apply, S.adjoint_inner_right]
    by_cases hi : 0 < i.1
    · have hzi := (Submodule.mem_orthogonal _ z).mp hz _
        (subset_span (Set.mem_range_self (⟨i, hi⟩ : PredictionSingularIndex S)))
      change inner ℝ ((Real.sqrt i.1)⁻¹ • S (singularDomainBasis S hc i)) (z : E) = 0 at hzi
      rw [inner_smul_left] at hzi
      simp only [conj_trivial] at hzi
      exact (mul_eq_zero.mp hzi).resolve_left (inv_ne_zero
        (ne_of_gt (Real.sqrt_pos.mpr hi)))
    · have hi0 : i.1 = 0 := le_antisymm (le_of_not_gt hi)
        (compactEigenvalue_nonneg (S.adjoint.comp S) hc
          (ContinuousLinearMap.isPositive_adjoint_comp_self S) i)
      rw [singularDomainBasis_image_eq_zero S hc i hi0, inner_zero_left]
  have hadj : S.adjoint (z : E) = 0 := by
    apply (singularDomainBasis S hc).repr.injective
    ext i
    simp only [hcoeff, map_zero, lp.coeFn_zero, Pi.zero_apply]
  have hzorth : (z : E) ∈ S.rangeᗮ := by
    rw [S.orthogonal_range]
    exact hadj
  have hzorthcl : (z : E) ∈ (PredictionRange S)ᗮ := by
    simpa only [PredictionRange, Submodule.orthogonal_closure] using hzorth
  have hzz := (Submodule.mem_orthogonal _ (z : E)).mp hzorthcl (z : E) z.property
  have hz0 : (z : E) = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hzz
  change z = 0
  exact Subtype.ext hz0

/-- The actual positive singular system is a Hilbert basis of the actual
closed prediction range. Its existence is proved, not assumed. -/
noncomputable def predictionSingularBasis (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) :
    HilbertBasis (PredictionSingularIndex S) ℝ (PredictionRange S) :=
  HilbertBasis.mkOfOrthogonalEqBot (predictionSingularVector_orthonormal S hc)
    (predictionSingularVector_orthogonal_eq_bot S hc)

@[simp]
theorem predictionSingularBasis_apply (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (i : PredictionSingularIndex S) :
    predictionSingularBasis S hc i = predictionSingularVector S hc i := by
  simp only [predictionSingularBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The constructed prediction vectors are actual positive eigenvectors of
`L = S S*`, with exactly the eigenvalues and multiplicities of `T = S* S`. -/
theorem predictionSingularBasis_eigen (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (i : PredictionSingularIndex S) :
    (S.comp S.adjoint) (predictionSingularBasis S hc i : E) =
      i.1.1 • (predictionSingularBasis S hc i : E) := by
  rw [predictionSingularBasis_apply]
  change (S.comp S.adjoint) ((Real.sqrt i.1.1)⁻¹ • S (singularDomainBasis S hc i.1)) = _
  rw [map_smul]
  change (Real.sqrt i.1.1)⁻¹ • S ((S.adjoint.comp S) (singularDomainBasis S hc i.1)) = _
  have he : (S.adjoint.comp S) (singularDomainBasis S hc i.1) =
      i.1.1 • singularDomainBasis S hc i.1 := compactEigenbasis_eigen _ hc
        (ContinuousLinearMap.isPositive_adjoint_comp_self S).isSymmetric i.1
  simp only [he, map_smul, predictionSingularVector_coe, smul_smul]
  congr 1
  ring

/-- The embedding has the actual singular-vector action `S v_i = sqrt(t_i) e_i`. -/
theorem singularDomainBasis_image (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (i : PredictionSingularIndex S) :
    S (singularDomainBasis S hc i.1) =
      Real.sqrt i.1.1 • (predictionSingularBasis S hc i : E) := by
  rw [predictionSingularBasis_apply]
  change S (singularDomainBasis S hc i.1) =
    Real.sqrt i.1.1 • ((Real.sqrt i.1.1)⁻¹ • S (singularDomainBasis S hc i.1))
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr i.2)), one_smul]

/-- The actual adjoint has the matching action `S* e_i = sqrt(t_i) v_i`. -/
theorem predictionSingularBasis_adjoint (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (i : PredictionSingularIndex S) :
    S.adjoint (predictionSingularBasis S hc i : E) =
      Real.sqrt i.1.1 • singularDomainBasis S hc i.1 := by
  rw [predictionSingularBasis_apply]
  change S.adjoint ((Real.sqrt i.1.1)⁻¹ • S (singularDomainBasis S hc i.1)) = _
  rw [map_smul]
  change (Real.sqrt i.1.1)⁻¹ • (S.adjoint.comp S) (singularDomainBasis S hc i.1) = _
  have he : (S.adjoint.comp S) (singularDomainBasis S hc i.1) =
      i.1.1 • singularDomainBasis S hc i.1 := compactEigenbasis_eigen _ hc
        (ContinuousLinearMap.isPositive_adjoint_comp_self S).isSymmetric i.1
  rw [he, smul_smul]
  have hcoef : (Real.sqrt i.1.1)⁻¹ * i.1.1 = Real.sqrt i.1.1 := by
    calc
      (Real.sqrt i.1.1)⁻¹ * i.1.1 =
          (Real.sqrt i.1.1)⁻¹ * (Real.sqrt i.1.1 * Real.sqrt i.1.1) := by
        rw [Real.mul_self_sqrt i.2.le]
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr i.2)), one_mul]
  rw [hcoef]

/-- Supported targets have the genuine sequence coefficients in this basis. -/
theorem predictionSingularBasis_coefficient (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) {f : E}
    (hf : f ∈ PredictionRange S) (i : PredictionSingularIndex S) :
    (predictionSingularBasis S hc).repr ⟨f, hf⟩ i =
      (Real.sqrt i.1.1)⁻¹ * inner ℝ (singularDomainBasis S hc i.1) (S.adjoint f) := by
  rw [HilbertBasis.repr_apply_apply, predictionSingularBasis_apply]
  change inner ℝ ((Real.sqrt i.1.1)⁻¹ • S (singularDomainBasis S hc i.1)) f = _
  rw [inner_smul_left]
  simp only [conj_trivial, S.adjoint_inner_right]

/-- The supported coefficient sequence is square summable by
actual Hilbert-basis Parseval, not an additional source-energy hypothesis. -/
theorem predictionSingularBasis_coefficients_summable (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) {f : E}
    (hf : f ∈ PredictionRange S) :
    Summable (fun i : PredictionSingularIndex S =>
      inner ℝ (predictionSingularBasis S hc i : E) f ^ 2) := by
  simpa only [HilbertBasis.repr_apply_apply, Submodule.coe_inner] using
    hilbertBasis_coefficients_sq_summable (predictionSingularBasis S hc) (⟨f, hf⟩ : PredictionRange S)

/-- The exact supported-target Parseval identity in the positive `T` spectrum. -/
theorem predictionSingularBasis_parseval (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) {f : E}
    (hf : f ∈ PredictionRange S) :
    ‖f‖ ^ 2 = ∑' i : PredictionSingularIndex S,
      inner ℝ (predictionSingularBasis S hc i : E) f ^ 2 := by
  simpa only [HilbertBasis.repr_apply_apply, Submodule.coe_inner, Submodule.coe_norm] using
    hilbertBasis_norm_sq_eq_tsum (predictionSingularBasis S hc) (⟨f, hf⟩ : PredictionRange S)

/-- The actual supported vector is reconstructed by its positive sequence
coefficients in the ambient prediction space, however large its null space is. -/
theorem predictionSingularBasis_hasSum (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) {f : E}
    (hf : f ∈ PredictionRange S) :
    HasSum (fun i : PredictionSingularIndex S =>
      inner ℝ (predictionSingularBasis S hc i : E) f • (predictionSingularBasis S hc i : E)) f := by
  have h := (PredictionRange S).subtypeL.hasSum
    ((predictionSingularBasis S hc).hasSum_repr (⟨f, hf⟩ : PredictionRange S))
  simpa only [HilbertBasis.repr_apply_apply, Submodule.coe_inner, map_smul,
    Submodule.subtypeL_apply] using h

/-- Separability is needed only when the positive sequence index is to be
enumerated; it is assumed on the domain, never on the prediction space. -/
theorem predictionSingularIndex_countable [SeparableSpace H] (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) : Countable (PredictionSingularIndex S) := by
  letI := compactSpectralIndex_countable (S.adjoint.comp S) hc
    (ContinuousLinearMap.isPositive_adjoint_comp_self S).isSymmetric
  infer_instance

end KernelFoundations
