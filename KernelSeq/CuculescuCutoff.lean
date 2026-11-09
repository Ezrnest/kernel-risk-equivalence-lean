import KernelSeq.SpectralBlocks
import KernelSeq.FiniteOperatorTrace

/-!
# Actual finite Cuculescu spectral cutoffs

The one-step cutoff is constructed from the actual compressed positive
operator. On the full ambient space it is `e - 1_(lam,∞)(eXe)`; this preserves
the zero eigenspace inside the corner without adding the kernel outside it.
It is the finite-dimensional spectral step in Randrianantoanina,
Proposition 2.4, https://arxiv.org/pdf/math/0111264.

The resulting projection/order/trace statements are proved here. A martingale
terminal tail bound requires a further adapted finite-average identity; no
martingale transform or weak-(1,1) bound is asserted by this module.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section
attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H]

omit [FiniteDimensional ℝ H] in
theorem cuculescuCompression_positive (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (hX : X.IsPositive) : (e * X * e).IsPositive := by
  have h := hX.conj_adjoint e
  change (e * X * e.adjoint).IsPositive at h
  simpa only [ContinuousLinearMap.isSelfAdjoint_iff'.mp he] using h

/-- The actual discarded strict-high spectral projection of the compression. -/
def cuculescuDrop (e X : H →L[ℝ] H) (he : IsSelfAdjoint e) (hX : X.IsPositive)
    (lam : ℝ) : H →L[ℝ] H :=
  compactSpectralProjection (e * X * e)
    (isCompactOperator_of_locallyCompactSpace_dom _)
    (cuculescuCompression_positive e X he hX) (Set.Ioi lam)

/-- The actual cutoff inside the preceding projection's corner. -/
def cuculescuCutoff (e X : H →L[ℝ] H) (he : IsSelfAdjoint e) (hX : X.IsPositive)
    (lam : ℝ) : H →L[ℝ] H := e - cuculescuDrop e X he hX lam

theorem cuculescuDrop_idempotent (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (hX : X.IsPositive) (lam : ℝ) :
    IsIdempotentElem (cuculescuDrop e X he hX lam) :=
  compactSpectralProjection_isIdempotent _ _ _ _

theorem cuculescuDrop_selfAdjoint (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (hX : X.IsPositive) (lam : ℝ) :
    IsSelfAdjoint (cuculescuDrop e X he hX lam) :=
  (compactSpectralProjection_isSymmetric _ _ _ _).isSelfAdjoint

theorem cuculescuDrop_positive (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (hX : X.IsPositive) (lam : ℝ) :
    (cuculescuDrop e X he hX lam).IsPositive :=
  (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint (cuculescuDrop_idempotent e X he hX lam)).mpr
    (cuculescuDrop_selfAdjoint e X he hX lam)

/-- Strictly positive compressed eigenvectors lie in the preceding corner. -/
theorem cuculescuDrop_left_absorb (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) : e * cuculescuDrop e X he hX lam = cuculescuDrop e X he hX lam := by
  let T := e * X * e
  let hc : IsCompactOperator T := isCompactOperator_of_locallyCompactSpace_dom T
  let hp : T.IsPositive := cuculescuCompression_positive e X he hX
  let b := compactEigenbasis T hc hp.isSymmetric
  have heT : e * T = T := by dsimp only [T]; simp only [← mul_assoc, he2.eq]
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨i, rfl⟩
  have hPi : cuculescuDrop e X he hX lam (b i) =
      (if lam < i.1 then (1 : ℝ) else 0) • b i := by
    simpa only [cuculescuDrop, compactSpectralProjection, T, hc, hp, b, Set.mem_Ioi] using
      compactSpectralMultiplier_eigen T hc hp (fun t => if t ∈ Set.Ioi lam then 1 else 0)
        1 zero_le_one (fun _ _ => by split_ifs <;> norm_num)
        (compactEigenbasis_eigen T hc hp.isSymmetric i)
  simp only [mul_apply_eq_comp, hPi, map_smul]
  by_cases hi : lam < i.1
  · have hμ : i.1 ≠ 0 := ne_of_gt (lt_of_le_of_lt hlam hi)
    have hTi := congrArg (fun A : H →L[ℝ] H => A (b i)) heT
    have hbi : T (b i) = i.1 • b i := compactEigenbasis_eigen T hc hp.isSymmetric i
    simp only [mul_apply_eq_comp, hbi, map_smul] at hTi
    have hfix : e (b i) = b i := by
      have hh := congrArg (fun v : H => i.1⁻¹ • v) hTi
      simpa only [smul_smul, inv_mul_cancel₀ hμ, one_smul] using hh
    simp only [if_pos hi, one_smul, hfix]
  · simp only [if_neg hi, zero_smul]

theorem cuculescuDrop_right_absorb (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) : cuculescuDrop e X he hX lam * e = cuculescuDrop e X he hX lam := by
  have h := congrArg star (cuculescuDrop_left_absorb e X he he2 hX lam hlam)
  simpa only [star_mul, he.star_eq, (cuculescuDrop_selfAdjoint e X he hX lam).star_eq] using h

theorem cuculescuCutoff_selfAdjoint (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (hX : X.IsPositive) (lam : ℝ) :
    IsSelfAdjoint (cuculescuCutoff e X he hX lam) :=
  he.sub (cuculescuDrop_selfAdjoint e X he hX lam)

theorem cuculescuCutoff_idempotent (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) : IsIdempotentElem (cuculescuCutoff e X he hX lam) := by
  have hl := cuculescuDrop_left_absorb e X he he2 hX lam hlam
  have hr := cuculescuDrop_right_absorb e X he he2 hX lam hlam
  have hd := (cuculescuDrop_idempotent e X he hX lam).eq
  change (e - cuculescuDrop e X he hX lam) * (e - cuculescuDrop e X he hX lam) = e - cuculescuDrop e X he hX lam
  rw [sub_mul, mul_sub, mul_sub, he2.eq, hl, hr, hd]
  abel

theorem cuculescuCutoff_positive (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) : (cuculescuCutoff e X he hX lam).IsPositive :=
  (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint (cuculescuCutoff_idempotent e X he he2 hX lam hlam)).mpr
    (cuculescuCutoff_selfAdjoint e X he hX lam)

theorem cuculescuCutoff_le (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (hX : X.IsPositive) (lam : ℝ) :
    cuculescuCutoff e X he hX lam ≤ e := by
  apply (ContinuousLinearMap.le_def _ _).mpr
  simpa only [cuculescuCutoff, sub_sub_cancel] using cuculescuDrop_positive e X he hX lam

theorem cuculescuCutoff_left_absorb (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) : e * cuculescuCutoff e X he hX lam = cuculescuCutoff e X he hX lam := by
  rw [cuculescuCutoff, mul_sub, he2.eq, cuculescuDrop_left_absorb e X he he2 hX lam hlam]

theorem cuculescuCutoff_right_absorb (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) : cuculescuCutoff e X he hX lam * e = cuculescuCutoff e X he hX lam := by
  rw [cuculescuCutoff, sub_mul, he2.eq, cuculescuDrop_right_absorb e X he he2 hX lam hlam]

/-- The actual new cutoff commutes with the compressed positive operator,
although the original positive operator need not commute with the corner. -/
theorem cuculescuCutoff_commutes_compression (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive) (lam : ℝ) :
    cuculescuCutoff e X he hX lam * (e * X * e) =
      (e * X * e) * cuculescuCutoff e X he hX lam := by
  have hl : e * (e * X * e) = e * X * e := by simp only [← mul_assoc, he2.eq]
  have hr : (e * X * e) * e = e * X * e := by simp only [mul_assoc, he2.eq]
  have hd := compactSpectralProjection_commutes (e * X * e)
    (isCompactOperator_of_locallyCompactSpace_dom _) (cuculescuCompression_positive e X he hX) (Set.Ioi lam)
  change cuculescuDrop e X he hX lam * (e * X * e) =
    (e * X * e) * cuculescuDrop e X he hX lam at hd
  rw [cuculescuCutoff, sub_mul, mul_sub, hl, hr, hd]

omit [FiniteDimensional ℝ H] in
/-- The quadratic form of an actual orthogonal projection is the squared
norm of its projected vector. -/
theorem orthogonalOperatorProjection_inner (P : H →L[ℝ] H)
    (hP : IsSelfAdjoint P) (hP2 : IsIdempotentElem P) (x : H) :
    inner ℝ x (P x) = ‖P x‖ ^ 2 := by
  have hp := congrArg (fun A : H →L[ℝ] H => A x) hP2.eq
  change P (P x) = P x at hp
  calc
    _ = inner ℝ x (P (P x)) := by rw [hp]
    _ = inner ℝ (P x) (P x) := ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP) x (P x)).symm
    _ = _ := real_inner_self_eq_norm_sq _

/-- The discarded component satisfies the actual strict-high quadratic
lower bound, with a weak inequality at the threshold. -/
theorem cuculescuDrop_compression_lower (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    lam • cuculescuDrop e X he hX lam ≤
      cuculescuDrop e X he hX lam * X * cuculescuDrop e X he hX lam := by
  let T := e * X * e
  let hc : IsCompactOperator T := isCompactOperator_of_locallyCompactSpace_dom T
  let hp : T.IsPositive := cuculescuCompression_positive e X he hX
  let D := cuculescuDrop e X he hX lam
  have hD : IsSelfAdjoint D := cuculescuDrop_selfAdjoint e X he hX lam
  have hD2 : IsIdempotentElem D := cuculescuDrop_idempotent e X he hX lam
  have hDl : e * D = D := cuculescuDrop_left_absorb e X he he2 hX lam hlam
  have hDr : D * e = D := cuculescuDrop_right_absorb e X he he2 hX lam hlam
  have hDTD : D * T * D = D * X * D := by
    calc
      _ = ((D * e) * X) * (e * D) := by dsimp only [T]; noncomm_ring
      _ = _ := by rw [hDl, hDr]
  have hDXD : IsSelfAdjoint (D * X * D) := by
    have h := hX.conj_adjoint D
    change (D * X * D.adjoint).IsPositive at h
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hD] at h
    exact h.isSelfAdjoint
  apply (real_loewner_iff_quadratic _ _ ((show IsSelfAdjoint lam from isSelfAdjoint_iff.mpr rfl).smul hD) hDXD).mpr
  intro x
  let y : SpectralSubspace T hc hp (Set.Ioi lam) := ⟨D x, ⟨x, rfl⟩⟩
  have hy := spectralRestriction_quadratic_lower T hc hp (Set.Ioi lam) lam (fun _ ht => ht.le) y
  change lam * ‖D x‖ ^ 2 ≤ inner ℝ (D x) (T (D x)) at hy
  rw [← hDTD]
  simp only [smul_apply, inner_smul_right, mul_apply_eq_comp]
  rw [orthogonalOperatorProjection_inner D hD hD2 x]
  calc
    _ ≤ inner ℝ (D x) (T (D x)) := hy
    _ = _ := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hD) x (T (D x))

/-- The retained corner is genuinely bounded by the cutoff threshold. The
zero eigenspace is retained only inside the preceding corner. -/
theorem cuculescuCutoff_compression_upper (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    cuculescuCutoff e X he hX lam * X * cuculescuCutoff e X he hX lam ≤
      lam • cuculescuCutoff e X he hX lam := by
  let T := e * X * e
  let hc : IsCompactOperator T := isCompactOperator_of_locallyCompactSpace_dom T
  let hp : T.IsPositive := cuculescuCompression_positive e X he hX
  let D := cuculescuDrop e X he hX lam
  let q := cuculescuCutoff e X he hX lam
  let P := compactSpectralProjection T hc hp (Set.Icc 0 lam)
  have hq : IsSelfAdjoint q := cuculescuCutoff_selfAdjoint e X he hX lam
  have hq2 : IsIdempotentElem q := cuculescuCutoff_idempotent e X he he2 hX lam hlam
  have hql : e * q = q := cuculescuCutoff_left_absorb e X he he2 hX lam hlam
  have hqr : q * e = q := cuculescuCutoff_right_absorb e X he he2 hX lam hlam
  have hqTq : q * T * q = q * X * q := by
    calc
      _ = ((q * e) * X) * (e * q) := by dsimp only [T]; noncomm_ring
      _ = _ := by rw [hql, hqr]
  have hP : P = 1 - D := by
    ext x
    apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
    ext i
    change (compactEigenbasis T hc hp.isSymmetric).repr
      (compactSpectralProjection T hc hp (Set.Icc 0 lam) x) i =
      (compactEigenbasis T hc hp.isSymmetric).repr
        ((1 - compactSpectralProjection T hc hp (Set.Ioi lam)) x) i
    simp only [compactSpectralProjection_repr, _root_.sub_apply, one_apply_eq_self,
      map_sub, lp.coeFn_sub, Pi.sub_apply]
    have hi := compactEigenvalue_nonneg T hc hp i
    by_cases ht : i.1 ≤ lam
    · simp [Set.mem_Icc, Set.mem_Ioi, hi, ht, not_lt.mpr ht]
    · simp [Set.mem_Icc, Set.mem_Ioi, hi, ht, lt_of_not_ge ht]
  have hDq : D * q = 0 := by
    change D * (e - D) = 0
    rw [mul_sub, cuculescuDrop_right_absorb e X he he2 hX lam hlam,
      (cuculescuDrop_idempotent e X he hX lam).eq, sub_self]
  have hPq : P * q = q := by rw [hP, sub_mul, one_mul, hDq, sub_zero]
  have hqXq : IsSelfAdjoint (q * X * q) := by
    have h := hX.conj_adjoint q
    change (q * X * q.adjoint).IsPositive at h
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hq] at h
    exact h.isSelfAdjoint
  apply (real_loewner_iff_quadratic _ _ hqXq
    ((show IsSelfAdjoint lam from isSelfAdjoint_iff.mpr rfl).smul hq)).mpr
  intro x
  let y : LowSpectralSpace T hc hp lam := ⟨q x, ⟨q x, by
    exact congrArg (fun A : H →L[ℝ] H => A x) hPq⟩⟩
  have hy := (lowSpectralRestriction T hc hp lam).le_of_opNorm_le
    (lowSpectralRestriction_norm_le T hc hp lam hlam) y
  change ‖T (q x)‖ ≤ lam * ‖q x‖ at hy
  rw [← hqTq]
  simp only [smul_apply, inner_smul_right, mul_apply_eq_comp]
  calc
    _ = inner ℝ (q x) (T (q x)) :=
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hq) x (T (q x))).symm
    _ ≤ ‖q x‖ * ‖T (q x)‖ := real_inner_le_norm _ _
    _ ≤ ‖q x‖ * (lam * ‖q x‖) := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = lam * inner ℝ x (q x) := by rw [orthogonalOperatorProjection_inner q hq hq2 x]; ring

/-- The true one-step trace payment: discarded rank costs at most the
original positive operator's energy on that discarded projection. -/
theorem cuculescuDrop_trace_bound {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    lam * basisTrace b (e - cuculescuCutoff e X he hX lam) ≤
      basisTrace b (X * (e - cuculescuCutoff e X he hX lam)) := by
  have h := finiteBasisTrace_mono b _ _ (cuculescuDrop_compression_lower e X he he2 hX lam hlam)
  have hcycle := finiteBasisTrace_mul_cycle b (cuculescuDrop e X he hX lam) X
    (cuculescuDrop e X he hX lam)
  rw [(cuculescuDrop_idempotent e X he hX lam).eq] at hcycle
  have hswap := finiteBasisTrace_mul_comm b (cuculescuDrop e X he hX lam) X
  simp only [← finiteBasisTraceCLM_apply, map_smul, smul_eq_mul] at h
  simp only [finiteBasisTraceCLM_apply] at h
  simpa only [cuculescuCutoff, sub_sub_cancel, hcycle, hswap] using h

end
end KernelSeq
