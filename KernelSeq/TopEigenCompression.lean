import KernelSeq.FiniteSpectralCompression

/-!
# A genuine leading eigenvector in finite spectral compressions

A nonzero positive compact operator has a basis eigenvector at its actual
operator norm. Finite spectral compressions containing that vector preserve
the norm exactly. This prevents replacing the variance-majorant norm by a
loose upper bound inside the intrinsic-dimension ratio.
-/

open Filter Topology LinearMap Module.End

namespace KernelSeq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The positive top spectral value is an actual eigenvalue, including on an
infinite-dimensional real Hilbert space. -/
theorem positive_compact_norm_hasEigenvalue (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hT : T.IsPositive) (hn : 0 < ‖T‖) :
    HasEigenvalue (T : Module.End ℝ H) ‖T‖ := by
  have hne : T ≠ 0 := by simpa only [norm_pos_iff] using hn
  have hex : ∃ μ : ℝ, HasEigenvalue (T : Module.End ℝ H) μ ∧ μ ≠ 0 := by
    by_contra! h
    exact hne ((T.eq_zero_of_forall_hasEigenvalue_eq_zero hc hT.isSymmetric).mp h)
  obtain ⟨μ, hμ, hμ0⟩ := hex
  have hspec : (spectrum ℝ T).Nonempty := ⟨μ, (hc.hasEigenvalue_iff_mem_spectrum hμ0).mp hμ⟩
  have hr := Real.spectralRadius_mem_spectrum_or hspec
  rw [T.spectralRadius_eq_nnnorm hT.isSelfAdjoint, ENNReal.coe_toReal] at hr
  rcases hr with hp | hm
  · exact (hc.hasEigenvalue_iff_mem_spectrum hn.ne').mpr hp
  · have he := (hc.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hn.ne')).mpr hm
    have hnonneg := eigenvalue_nonneg_of_nonneg he (fun x => hT.inner_nonneg_right x)
    change 0 ≤ -‖T‖ at hnonneg
    linarith

/-- One of the actually constructed full-basis indices realizes the operator
norm; a top-eigenvector certificate is not a model hypothesis. -/
theorem exists_compactEigenvalue_eq_norm (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hT : T.IsPositive) (hn : 0 < ‖T‖) :
    ∃ j : CompactSpectralIndex T, j.1 = ‖T‖ := by
  let b := compactEigenbasis T hc hT.isSymmetric
  obtain ⟨x, hx, hx0⟩ := (positive_compact_norm_hasEigenvalue T hc hT hn).exists_hasEigenvector
  have hTx : T x = ‖T‖ • x := mem_eigenspace_iff.mp
    (show x ∈ eigenspace (T : Module.End ℝ H) ‖T‖ by
      simpa only [mem_genEigenspace_one] using hx)
  have hcoord : ∃ j, b.repr x j ≠ 0 := by
    by_contra! hz
    apply hx0
    apply b.repr.injective
    ext j
    simpa using hz j
  obtain ⟨j, hj⟩ := hcoord
  refine ⟨j, ?_⟩
  have he := congrArg (fun y => b.repr y j) hTx
  change b.repr (T x) j = b.repr (‖T‖ • x) j at he
  rw [compactEigenbasis_repr_apply, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at he
  exact (mul_right_cancel₀ hj he)

/-- Actual finite compressions preserve the true top norm eventually along the
directed set of finite spectral selections. -/
theorem positive_compact_compression_norm_eventually_eq (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hT : T.IsPositive) (hn : 0 < ‖T‖) :
    ∀ᶠ s : Finset (CompactSpectralIndex T) in atTop,
      ‖finiteBasisProjection (compactEigenbasis T hc hT.isSymmetric) s * T *
        finiteBasisProjection (compactEigenbasis T hc hT.isSymmetric) s‖ = ‖T‖ := by
  classical
  obtain ⟨j, hj⟩ := exists_compactEigenvalue_eq_norm T hc hT hn
  filter_upwards [eventually_ge_atTop ({j} : Finset (CompactSpectralIndex T))] with s hs
  apply finiteBasisCompression_norm_eq_of_basis_eigen _ s T j
  · exact hs (Finset.mem_singleton_self j)
  · simpa only [hj] using compactEigenbasis_eigen T hc hT.isSymmetric j

end KernelSeq
