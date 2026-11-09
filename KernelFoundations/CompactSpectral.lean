import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import KernelFoundations.RealOperatorRoots
import KernelFoundations.RegularizedComparison

/-!
# Eigenvector Hilbert bases for real compact selfadjoint operators

The index set below is constructed from the actual eigenspaces. No choice of an
eigenbasis is a hypothesis, and the ambient Hilbert space may be infinite dimensional.
The zero eigenspace is retained, so no injectivity assumption is needed.
-/

open LinearMap Module.End Submodule TopologicalSpace

namespace KernelFoundations

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def eigenspaceBasisSet (T : H →L[ℝ] H) (μ : ℝ) :
    Set (eigenspace (T : Module.End ℝ H) μ) :=
  (exists_hilbertBasis ℝ (eigenspace (T : Module.End ℝ H) μ)).choose

noncomputable def eigenspaceHilbertBasis (T : H →L[ℝ] H) (μ : ℝ) :
    HilbertBasis (eigenspaceBasisSet T μ) ℝ (eigenspace (T : Module.End ℝ H) μ) :=
  (exists_hilbertBasis ℝ (eigenspace (T : Module.End ℝ H) μ)).choose_spec.choose

/-- The index keeps both the eigenvalue and an orthonormal-basis index inside its eigenspace. -/
abbrev CompactSpectralIndex (T : H →L[ℝ] H) := Σ μ : ℝ, eigenspaceBasisSet T μ

noncomputable def compactEigenvector (T : H →L[ℝ] H) (i : CompactSpectralIndex T) : H :=
  eigenspaceHilbertBasis T i.1 i.2

theorem compactEigenvector_eigen (T : H →L[ℝ] H) (i : CompactSpectralIndex T) :
    T (compactEigenvector T i) = i.1 • compactEigenvector T i :=
  (mem_eigenspace_iff.mp (eigenspaceHilbertBasis T i.1 i.2).property)

theorem compactEigenvector_orthonormal (T : H →L[ℝ] H) (hT : T.IsSymmetric) :
    Orthonormal ℝ (compactEigenvector T) :=
  hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun μ => (eigenspaceHilbertBasis T μ).orthonormal)

/-- Completeness follows from the compact spectral theorem, including a possibly
infinite-dimensional kernel. -/
theorem compactEigenvector_orthogonal_eq_bot (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsSymmetric) :
    (span ℝ (Set.range (compactEigenvector T)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hxEigen : ∀ μ : ℝ, x ∈ (eigenspace (T : Module.End ℝ H) μ)ᗮ := by
    intro μ
    apply (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp
    have hsum := (eigenspaceHilbertBasis T μ).hasSum_orthogonalProjectionOnto x
    have hz : ∀ i : eigenspaceBasisSet T μ,
        inner ℝ ((eigenspaceHilbertBasis T μ i : eigenspace (T : Module.End ℝ H) μ) : H) x = 0 := by
      intro i
      exact (Submodule.mem_orthogonal _ x).mp hx _
        (subset_span (Set.mem_range_self (⟨μ, i⟩ : CompactSpectralIndex T)))
    simp only [hz, zero_smul] at hsum
    exact hsum.unique (hasSum_zero)
  have hAll : x ∈ (⨆ μ : ℝ, eigenspace (T : Module.End ℝ H) μ)ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    exact (Submodule.mem_iInf _).mpr hxEigen
  simpa only [T.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hT] using hAll

/-- An actual eigenvector Hilbert basis, constructed for every compact symmetric
bounded real operator. -/
noncomputable def compactEigenbasis (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsSymmetric) :
    HilbertBasis (CompactSpectralIndex T) ℝ H :=
  HilbertBasis.mkOfOrthogonalEqBot (compactEigenvector_orthonormal T hT)
    (compactEigenvector_orthogonal_eq_bot T hcompact hT)

@[simp]
theorem compactEigenbasis_apply (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsSymmetric) (i : CompactSpectralIndex T) :
    compactEigenbasis T hcompact hT i = compactEigenvector T i := by
  simp only [compactEigenbasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem compactEigenbasis_eigen (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsSymmetric) (i : CompactSpectralIndex T) :
    T (compactEigenbasis T hcompact hT i) = i.1 • compactEigenbasis T hcompact hT i := by
  simpa only [compactEigenbasis_apply] using compactEigenvector_eigen T i

theorem compactEigenvalue_norm_le (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsSymmetric) (i : CompactSpectralIndex T) :
    ‖i.1‖ ≤ ‖T‖ := by
  have h := T.le_opNorm (compactEigenbasis T hcompact hT i)
  simpa only [compactEigenbasis_eigen, norm_smul,
    (compactEigenbasis T hcompact hT).orthonormal.norm_eq_one, mul_one] using h

theorem compactEigenvalue_nonneg (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (i : CompactSpectralIndex T) :
    0 ≤ i.1 := by
  have h := hT.inner_nonneg_right (compactEigenbasis T hcompact hT.isSymmetric i)
  simpa only [compactEigenbasis_eigen, inner_smul_right, real_inner_self_eq_norm_sq,
    (compactEigenbasis T hcompact hT.isSymmetric).orthonormal.norm_eq_one,
    one_pow, mul_one] using h

section Diagonal

variable {ι : Type*} (b : HilbertBasis ι ℝ H)

/-- A bounded real scalar multiplier transported through an actual Hilbert basis. -/
noncomputable def hilbertDiagonal (w : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ i, ‖w i‖ ≤ K) : H →L[ℝ] H :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun i => w i • ContinuousLinearMap.id ℝ ℝ) hK
      (fun i => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hw i)).comp
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

omit [CompleteSpace H] in
@[simp]
theorem hilbertDiagonal_repr (w : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ i, ‖w i‖ ≤ K) (x : H) (i : ι) :
    b.repr (hilbertDiagonal b w K hK hw x) i = w i * b.repr x i := by
  simp [hilbertDiagonal]

omit [CompleteSpace H] in
theorem hilbertDiagonal_norm_le (w : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ i, ‖w i‖ ≤ K) : ‖hilbertDiagonal b w K hK hw‖ ≤ K := by
  let M := lp.mapCLM 2 (fun i => w i • ContinuousLinearMap.id ℝ ℝ) hK
    (fun i => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hw i)
  have hM : ‖M‖ ≤ K := lp.norm_mapCLM_le 2 _ hK _
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  change ‖b.repr.symm (M (b.repr x))‖ ≤ K * ‖x‖
  rw [b.repr.symm.norm_map, ← b.repr.norm_map x]
  exact M.le_of_opNorm_le hM _

omit [CompleteSpace H] in
theorem hilbertDiagonal_isSymmetric (w : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ i, ‖w i‖ ≤ K) : (hilbertDiagonal b w K hK hw).IsSymmetric := by
  intro x y
  have hcoeff (z : H) (i : ι) :
      inner ℝ (b i) (hilbertDiagonal b w K hK hw z) = w i * inner ℝ (b i) z := by
    simpa only [HilbertBasis.repr_apply_apply] using hilbertDiagonal_repr b w K hK hw z i
  apply (b.hasSum_inner_mul_inner (hilbertDiagonal b w K hK hw x) y).unique
  convert b.hasSum_inner_mul_inner x (hilbertDiagonal b w K hK hw y) using 1
  ext i
  rw [real_inner_comm (b i) (hilbertDiagonal b w K hK hw x), hcoeff, hcoeff,
    real_inner_comm x (b i)]
  ring
  rfl

omit [CompleteSpace H] in
theorem hilbertDiagonal_nonneg (w : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ i, ‖w i‖ ≤ K) (hnonneg : ∀ i, 0 ≤ w i) :
    0 ≤ hilbertDiagonal b w K hK hw := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨hilbertDiagonal_isSymmetric b w K hK hw, ?_⟩
  intro x
  change 0 ≤ inner ℝ (hilbertDiagonal b w K hK hw x) x
  rw [← b.repr.inner_map_map, lp.inner_eq_tsum]
  apply tsum_nonneg
  intro i
  simp only [hilbertDiagonal_repr, RCLike.inner_apply, conj_trivial]
  nlinarith [hnonneg i, sq_nonneg (b.repr x i)]

end Diagonal

theorem compactEigenbasis_repr_apply (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsSymmetric) (x : H)
    (i : CompactSpectralIndex T) :
    (compactEigenbasis T hcompact hT).repr (T x) i =
      i.1 * (compactEigenbasis T hcompact hT).repr x i := by
  calc
    (compactEigenbasis T hcompact hT).repr (T x) i =
        inner ℝ (compactEigenbasis T hcompact hT i) (T x) :=
      (compactEigenbasis T hcompact hT).repr_apply_apply _ _
    _ = inner ℝ (T (compactEigenbasis T hcompact hT i)) x := (hT _ _).symm
    _ = i.1 * inner ℝ (compactEigenbasis T hcompact hT i) x := by
      rw [compactEigenbasis_eigen, inner_smul_left, conj_trivial]
    _ = i.1 * (compactEigenbasis T hcompact hT).repr x i :=
      congrArg (fun r : ℝ => i.1 * r)
        ((compactEigenbasis T hcompact hT).repr_apply_apply x i).symm

theorem compact_regularized_sqrt_weight_bound (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsSymmetric) (lam : ℝ)
    (i : CompactSpectralIndex T) :
    ‖Real.sqrt (i.1 + lam)‖ ≤ Real.sqrt (‖T‖ + lam) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  simpa only [add_comm] using add_le_add_right ((le_abs_self i.1).trans
    (compactEigenvalue_norm_le T hcompact hT i)) lam

/-- The actual real-Hilbert spectral square root of a regularized positive
compact operator. The compactness assumption is only on `T`, not on `T + lam I`. -/
noncomputable def compactRegularizedSqrt (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) : H →L[ℝ] H :=
  hilbertDiagonal (compactEigenbasis T hcompact hT.isSymmetric)
    (fun i => Real.sqrt (i.1 + lam)) (Real.sqrt (‖T‖ + lam)) (Real.sqrt_nonneg _)
    (compact_regularized_sqrt_weight_bound T hcompact hT.isSymmetric lam)

@[simp]
theorem compactRegularizedSqrt_repr (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (x : H)
    (i : CompactSpectralIndex T) :
    (compactEigenbasis T hcompact hT.isSymmetric).repr
      (compactRegularizedSqrt T hcompact hT lam x) i =
        Real.sqrt (i.1 + lam) * (compactEigenbasis T hcompact hT.isSymmetric).repr x i :=
  hilbertDiagonal_repr _ _ _ _ _ _ _

theorem compactRegularizedSqrt_nonneg (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) :
    0 ≤ compactRegularizedSqrt T hcompact hT lam :=
  hilbertDiagonal_nonneg _ _ _ _ _ (fun _ => Real.sqrt_nonneg _)

theorem compactRegularizedSqrt_norm_le (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) :
    ‖compactRegularizedSqrt T hcompact hT lam‖ ≤ Real.sqrt (‖T‖ + lam) :=
  hilbertDiagonal_norm_le _ _ _ _ _

theorem compactRegularizedSqrt_isSelfAdjoint (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) :
    IsSelfAdjoint (compactRegularizedSqrt T hcompact hT lam) :=
  (hilbertDiagonal_isSymmetric _ _ _ _ _).isSelfAdjoint

/-- The constructed operator squares exactly to `T + lam I`, including `lam = 0`. -/
theorem compactRegularizedSqrt_sq (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 ≤ lam) :
    compactRegularizedSqrt T hcompact hT lam * compactRegularizedSqrt T hcompact hT lam =
      T + lam • (1 : H →L[ℝ] H) := by
  ext x
  apply (compactEigenbasis T hcompact hT.isSymmetric).repr.injective
  ext i
  rw [mul_apply_eq_comp, compactRegularizedSqrt_repr, compactRegularizedSqrt_repr]
  simp only [_root_.add_apply, _root_.smul_apply,
    one_apply_eq_self, map_add, map_smul, lp.coeFn_add, lp.coeFn_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, compactEigenbasis_repr_apply]
  rw [← mul_assoc, Real.mul_self_sqrt (add_nonneg (compactEigenvalue_nonneg T hcompact hT i) hlam)]
  ring

/-- Positive regularization makes the constructed selfadjoint square root an actual unit. -/
theorem compactRegularizedSqrt_isUnit (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (compactRegularizedSqrt T hcompact hT lam) := by
  rw [← isUnit_mul_self_iff, compactRegularizedSqrt_sq T hcompact hT lam hlam.le]
  exact regularized_isUnit_real T ((ContinuousLinearMap.nonneg_iff_isPositive T).mpr hT) lam hlam

/-- The actual inverse square root in the real bounded-operator ring. -/
noncomputable def compactRegularizedInvSqrt (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) : H →L[ℝ] H :=
  Ring.inverse (compactRegularizedSqrt T hcompact hT lam)

theorem compactRegularizedInvSqrt_isSelfAdjoint (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) :
    IsSelfAdjoint (compactRegularizedInvSqrt T hcompact hT lam) :=
  (compactRegularizedSqrt_isSelfAdjoint T hcompact hT lam).ringInverse

theorem compactRegularizedSqrt_mul_invSqrt (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    compactRegularizedSqrt T hcompact hT lam * compactRegularizedInvSqrt T hcompact hT lam = 1 :=
  Ring.mul_inverse_cancel _ (compactRegularizedSqrt_isUnit T hcompact hT lam hlam)

theorem compactRegularizedInvSqrt_mul_sqrt (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    compactRegularizedInvSqrt T hcompact hT lam * compactRegularizedSqrt T hcompact hT lam = 1 :=
  Ring.inverse_mul_cancel _ (compactRegularizedSqrt_isUnit T hcompact hT lam hlam)

/-- The inverse square root acts by the inverse square root of each regularized
eigenvalue in the constructed coordinates. -/
@[simp]
theorem compactRegularizedInvSqrt_repr (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (x : H) (i : CompactSpectralIndex T) :
    (compactEigenbasis T hcompact hT.isSymmetric).repr
      (compactRegularizedInvSqrt T hcompact hT lam x) i =
        (Real.sqrt (i.1 + lam))⁻¹ * (compactEigenbasis T hcompact hT.isSymmetric).repr x i := by
  have hn : Real.sqrt (i.1 + lam) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (compactEigenvalue_nonneg T hcompact hT i) hlam))
  have hx : compactRegularizedSqrt T hcompact hT lam
      (compactRegularizedInvSqrt T hcompact hT lam x) = x :=
    congrArg (fun f : H →L[ℝ] H => f x) (compactRegularizedSqrt_mul_invSqrt T hcompact hT lam hlam)
  have hc : Real.sqrt (i.1 + lam) * (compactEigenbasis T hcompact hT.isSymmetric).repr
      (compactRegularizedInvSqrt T hcompact hT lam x) i =
        (compactEigenbasis T hcompact hT.isSymmetric).repr x i := by
    simpa only [compactRegularizedSqrt_repr] using
      congrArg (fun y : H => (compactEigenbasis T hcompact hT.isSymmetric).repr y i) hx
  calc
    _ = (Real.sqrt (i.1 + lam))⁻¹ * (Real.sqrt (i.1 + lam) *
        (compactEigenbasis T hcompact hT.isSymmetric).repr
          (compactRegularizedInvSqrt T hcompact hT lam x) i) := by
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = _ := by rw [hc]

theorem compactRegularizedInvSqrt_sq (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    compactRegularizedInvSqrt T hcompact hT lam * compactRegularizedInvSqrt T hcompact hT lam =
      Ring.inverse (T + lam • (1 : H →L[ℝ] H)) := by
  calc
    _ = Ring.inverse (compactRegularizedSqrt T hcompact hT lam *
        compactRegularizedSqrt T hcompact hT lam) :=
      (Ring.inverse_mul (Or.inl (compactRegularizedSqrt_isUnit T hcompact hT lam hlam))).symm
    _ = _ := congrArg Ring.inverse (compactRegularizedSqrt_sq T hcompact hT lam hlam.le)

/-- Whitening by the constructed inverse square root gives the identity exactly. -/
theorem compactRegularizedInvSqrt_normalizes (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    compactRegularizedInvSqrt T hcompact hT lam * (T + lam • (1 : H →L[ℝ] H)) *
      compactRegularizedInvSqrt T hcompact hT lam = 1 := by
  rw [← compactRegularizedSqrt_sq T hcompact hT lam hlam.le]
  calc
    _ = (compactRegularizedInvSqrt T hcompact hT lam * compactRegularizedSqrt T hcompact hT lam) *
        (compactRegularizedSqrt T hcompact hT lam * compactRegularizedInvSqrt T hcompact hT lam) := by
      simp only [mul_assoc]
    _ = 1 := by rw [compactRegularizedInvSqrt_mul_sqrt T hcompact hT lam hlam,
                    compactRegularizedSqrt_mul_invSqrt T hcompact hT lam hlam, one_mul]

theorem compactRegularizedInvSqrt_adjoint_normalizes (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    (compactRegularizedInvSqrt T hcompact hT lam).adjoint.comp
      ((T + lam • (1 : H →L[ℝ] H)).comp (compactRegularizedInvSqrt T hcompact hT lam)) = 1 := by
  change (compactRegularizedInvSqrt T hcompact hT lam).adjoint *
    ((T + lam • (1 : H →L[ℝ] H)) * compactRegularizedInvSqrt T hcompact hT lam) = 1
  rw [(compactRegularizedInvSqrt_isSelfAdjoint T hcompact hT lam).adjoint_eq, ← mul_assoc]
  exact compactRegularizedInvSqrt_normalizes T hcompact hT lam hlam

/-- Conjugating the actual normalized perturbation back by the constructed root
recovers the perturbation, rather than assuming this factorization. -/
theorem compactRegularizedInvSqrt_factorization (T C : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    (compactRegularizedSqrt T hcompact hT lam).adjoint.comp
      ((compactRegularizedInvSqrt T hcompact hT lam * C *
        compactRegularizedInvSqrt T hcompact hT lam).comp
          (compactRegularizedSqrt T hcompact hT lam)) = C :=
  inverse_root_factorization_real _ C (compactRegularizedSqrt_isSelfAdjoint T hcompact hT lam)
    (compactRegularizedSqrt_isUnit T hcompact hT lam hlam)

theorem compactRegularizedInvSqrt_nonneg (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ compactRegularizedInvSqrt T hcompact hT lam := by
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (compactRegularizedSqrt_nonneg T hcompact hT lam)).adjoint_conj
      (compactRegularizedInvSqrt T hcompact hT lam)
  have ha := (compactRegularizedInvSqrt_isSelfAdjoint T hcompact hT lam).adjoint_eq
  change ((compactRegularizedInvSqrt T hcompact hT lam).adjoint *
    (compactRegularizedSqrt T hcompact hT lam * compactRegularizedInvSqrt T hcompact hT lam)).IsPositive at hp
  rw [ha, compactRegularizedSqrt_mul_invSqrt T hcompact hT lam hlam, mul_one] at hp
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp

/-- The sharp regularization norm bound for the constructed inverse square root. -/
theorem compactRegularizedInvSqrt_norm_le (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    ‖compactRegularizedInvSqrt T hcompact hT lam‖ ≤ 1 / Real.sqrt lam := by
  have hs : ‖compactRegularizedInvSqrt T hcompact hT lam‖ ^ 2 ≤ 1 / lam := by
    calc
      _ = ‖(compactRegularizedInvSqrt T hcompact hT lam).adjoint.comp
          (compactRegularizedInvSqrt T hcompact hT lam)‖ := by
        rw [ContinuousLinearMap.norm_adjoint_comp_self, pow_two]
      _ = ‖compactRegularizedInvSqrt T hcompact hT lam *
          compactRegularizedInvSqrt T hcompact hT lam‖ := by
        rw [(compactRegularizedInvSqrt_isSelfAdjoint T hcompact hT lam).adjoint_eq]
        rfl
      _ = ‖Ring.inverse (T + lam • (1 : H →L[ℝ] H))‖ :=
        congrArg norm (compactRegularizedInvSqrt_sq T hcompact hT lam hlam)
      _ ≤ 1 / lam := regularized_inverse_norm_le_real T
        ((ContinuousLinearMap.nonneg_iff_isPositive T).mpr hT) lam hlam
  have h := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq (norm_nonneg _)] at h
  simpa only [one_div, Real.sqrt_inv] using h

/-- In a separable ambient Hilbert space, the constructed full eigenbasis is countable. -/
theorem compactSpectralIndex_countable [SeparableSpace H] (T : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsSymmetric) :
    Countable (CompactSpectralIndex T) := by
  let b := compactEigenbasis T hcompact hT
  have hd : Pairwise (fun i j : CompactSpectralIndex T =>
      Disjoint (Metric.ball (b i) (1 / 2 : ℝ)) (Metric.ball (b j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs := norm_sub_sq_real (b i) (b j)
    rw [b.orthonormal.norm_eq_one i, b.orthonormal.norm_eq_one j,
      b.orthonormal.inner_eq_zero hij] at hs
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (b i - b j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.nonempty_ball.mpr (by norm_num))

/-- Loewner order of actual real selfadjoint maps is equivalent to order of all
their quadratic forms. No real functional-calculus instance is required. -/
theorem real_loewner_iff_quadratic (A B : H →L[ℝ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    A ≤ B ↔ ∀ x, inner ℝ x (A x) ≤ inner ℝ x (B x) := by
  constructor
  · intro h x
    have hp := ((ContinuousLinearMap.le_def A B).mp h).inner_nonneg_right x
    change 0 ≤ inner ℝ x (B x - A x) at hp
    rw [inner_sub_right] at hp
    exact sub_nonneg.mp hp
  · intro h
    apply (ContinuousLinearMap.le_def A B).mpr
    apply (ContinuousLinearMap.isPositive_iff' _).mpr
    refine ⟨hB.sub hA, fun x => ?_⟩
    change 0 ≤ inner ℝ (B x - A x) x
    rw [inner_sub_left, real_inner_comm x (B x), real_inner_comm x (A x)]
    exact sub_nonneg.mpr (h x)

/-- Relative quadratic-form comparison for infinite-dimensional
real covariance operators, using a constructed inverse square root. -/
theorem compact_regularized_relative_comparison_real (T TX : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (x : H) :
    let a := T + lam • (1 : H →L[ℝ] H)
    let b := TX + lam • (1 : H →L[ℝ] H)
    let R := compactRegularizedSqrt T hcompact hT lam
    let δ := ‖Ring.inverse R * (b - a) * Ring.inverse R‖
    (1 - δ) * inner ℝ x (a x) ≤ inner ℝ x (b x) ∧
      inner ℝ x (b x) ≤ (1 + δ) * inner ℝ x (a x) := by
  have h := invertible_root_relative_comparison_real
    (compactRegularizedSqrt T hcompact hT lam) (TX + lam • (1 : H →L[ℝ] H))
    (compactRegularizedSqrt_isSelfAdjoint T hcompact hT lam)
    (compactRegularizedSqrt_isUnit T hcompact hT lam hlam) x
  simpa only [compactRegularizedSqrt_sq T hcompact hT lam hlam.le] using h

/-- The same comparison in the actual real Loewner order. -/
theorem compact_regularized_loewner_comparison_real (T TX : H →L[ℝ] H)
    (hcompact : IsCompactOperator T) (hT : T.IsPositive) (hTX : IsSelfAdjoint TX)
    (lam : ℝ) (hlam : 0 < lam) :
    let a := T + lam • (1 : H →L[ℝ] H)
    let b := TX + lam • (1 : H →L[ℝ] H)
    let R := compactRegularizedSqrt T hcompact hT lam
    let δ := ‖Ring.inverse R * (b - a) * Ring.inverse R‖
    (1 - δ) • a ≤ b ∧ b ≤ (1 + δ) • a := by
  dsimp only
  have hs : IsSelfAdjoint (lam • (1 : H →L[ℝ] H)) :=
    (show IsSelfAdjoint lam from by simp [IsSelfAdjoint]).smul (IsSelfAdjoint.one _)
  have ha := hT.isSelfAdjoint.add hs
  have hb := hTX.add hs
  constructor
  · apply (real_loewner_iff_quadratic _ _
      ((show IsSelfAdjoint (1 - ‖Ring.inverse (compactRegularizedSqrt T hcompact hT lam) *
          (TX + lam • (1 : H →L[ℝ] H) - (T + lam • 1)) *
          Ring.inverse (compactRegularizedSqrt T hcompact hT lam)‖) from by
        simp [IsSelfAdjoint]).smul ha) hb).mpr
    intro x
    simpa only [_root_.smul_apply, inner_smul_right] using
      (compact_regularized_relative_comparison_real T TX hcompact hT lam hlam x).1
  · apply (real_loewner_iff_quadratic _ _ hb
      ((show IsSelfAdjoint (1 + ‖Ring.inverse (compactRegularizedSqrt T hcompact hT lam) *
          (TX + lam • (1 : H →L[ℝ] H) - (T + lam • 1)) *
          Ring.inverse (compactRegularizedSqrt T hcompact hT lam)‖) from by
        simp [IsSelfAdjoint]).smul ha)).mpr
    intro x
    simpa only [_root_.smul_apply, inner_smul_right] using
      (compact_regularized_relative_comparison_real T TX hcompact hT lam hlam x).2

end KernelFoundations
