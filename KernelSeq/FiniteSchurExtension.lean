import KernelSeq.DiscreteDOI
import KernelSeq.SchattenCompression
import KernelSeq.CovarianceCompression

/-!
# Label-preserving finite Schur compressions and their extension

Finite coordinate subspaces use the original basis indices and vectors. Schur
multiplication commutes with the genuine rectangular compression. Uniform
finite-dimensional Schatten multiplier bounds are explicit theorem premises;
the finite-to-infinite passage uses actual HS reconstruction and singular-power
Fatou bounds, not Schatten-space completeness or an assumed infinite HMS bound.
-/

open Filter Topology Submodule
open scoped BigOperators ENNReal

namespace KernelSeq

noncomputable section

variable {ι κ η H E F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The genuine finite Hilbert basis retains exactly the original labels. -/
def finiteSpectralLabelBasis (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    HilbertBasis s ℝ (FiniteSpectralSubspace b s) := by
  classical
  let e : span ℝ (s.image b : Set H) ≃ₗᵢ[ℝ] FiniteSpectralSubspace b s :=
    LinearIsometryEquiv.ofEq _ _ (by rw [FiniteSpectralSubspace, Finset.coe_image])
  exact ((OrthonormalBasis.span b.orthonormal s).map e).toHilbertBasis

omit [CompleteSpace H] in
/-- Each selected finite-basis vector is exactly its original ambient vector. -/
@[simp]
theorem finiteSpectralLabelBasis_coe (b : HilbertBasis ι ℝ H) (s : Finset ι) (i : s) :
    (finiteSpectralLabelBasis b s i : H) = b i := by
  classical
  unfold finiteSpectralLabelBasis
  simp only [OrthonormalBasis.coe_toHilbertBasis, OrthonormalBasis.map_apply,
    LinearIsometryEquiv.coe_ofEq_apply, OrthonormalBasis.span_apply]

/-- The actual rectangular compression between two selected coordinate spans. -/
def finiteRectangularCompression (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (s : Finset ι) (t : Finset κ) (A : H →L[ℝ] E) :
    FiniteSpectralSubspace b s →L[ℝ] FiniteSpectralSubspace a t :=
  (finiteSpectralInclusion a t).adjoint.comp (A.comp (finiteSpectralInclusion b s))

omit [CompleteSpace H] in
/-- Compression retains the original cross-basis matrix coefficients. -/
theorem finiteRectangularCompression_entry (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (s : Finset ι) (t : Finset κ) (A : H →L[ℝ] E) (i : t) (j : s) :
    inner ℝ (finiteSpectralLabelBasis a t i)
      (finiteRectangularCompression b a s t A (finiteSpectralLabelBasis b s j)) =
      inner ℝ (a i) (A (b j)) := by
  rw [finiteRectangularCompression, ContinuousLinearMap.comp_apply,
    (finiteSpectralInclusion a t).adjoint_inner_right]
  change inner ℝ (finiteSpectralLabelBasis a t i : E)
    (A (finiteSpectralLabelBasis b s j : H)) = _
  rw [finiteSpectralLabelBasis_coe, finiteSpectralLabelBasis_coe]

/-- Actual HS columns of a finite rectangular compression, in the labelled
basis of its actual finite-dimensional domain. -/
def finiteRectangularColumns (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (s : Finset ι) (t : Finset κ) (c : HilbertSchmidtColumns ι E) :
    HilbertSchmidtColumns s (FiniteSpectralSubspace a t) :=
  hsOrthogonalCompressionColumns b (FiniteSpectralSubspace b s) (FiniteSpectralSubspace a t)
    (finiteSpectralLabelBasis b s) a c

theorem hilbertSchmidtOperator_finiteRectangularColumns
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (s : Finset ι) (t : Finset κ) (c : HilbertSchmidtColumns ι E) :
    hilbertSchmidtOperator (finiteSpectralLabelBasis b s) (finiteRectangularColumns b a s t c) =
      finiteRectangularCompression b a s t (hilbertSchmidtOperator b c) := by
  simpa only [finiteRectangularColumns, finiteRectangularCompression, finiteSpectralInclusion,
    Submodule.adjoint_subtypeL] using
    hilbertSchmidtOperator_orthogonalCompression b (FiniteSpectralSubspace b s)
      (FiniteSpectralSubspace a t) (finiteSpectralLabelBasis b s) a c

/-- The exact finite labelled Schur transform commutes with actual compression. -/
theorem finiteSchur_compression_compatible
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (M : κ → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K)
    (s : Finset ι) (t : Finset κ) (c : HilbertSchmidtColumns ι E) :
    hsSchurMultiplier (finiteSpectralLabelBasis a t) (fun (i : t) (j : s) => M i j) K hK
      (fun i j => hM i j) (finiteRectangularColumns b a s t c) =
      finiteRectangularColumns b a s t (hsSchurMultiplier a M K hK hM c) := by
  apply hilbertSchmidtOperator_injective (finiteSpectralLabelBasis b s)
  rw [hilbertSchmidtOperator_finiteRectangularColumns]
  apply hsSchurMultiplier_represents
  intro i j
  rw [finiteRectangularCompression_entry, hilbertSchmidtOperator_finiteRectangularColumns,
    finiteRectangularCompression_entry, hsSchurMultiplier_coefficient]

section Lift

variable (P : Submodule ℝ H) (Q : Submodule ℝ E) [CompleteSpace P] [CompleteSpace Q]

/-- Zero extension of a rectangular subspace operator by the two actual
inclusions. Its right factor is the actual adjoint inclusion. -/
def rectangularSubspaceLift (A : P →L[ℝ] Q) : H →L[ℝ] E :=
  Q.subtypeL.comp (A.comp P.subtypeL.adjoint)

omit [CompleteSpace E] [CompleteSpace Q] in
/-- The rectangular lift preserves the actual operator norm, including empty
finite selections and zero subspaces. -/
theorem rectangularSubspaceLift_norm (A : P →L[ℝ] Q) :
    ‖rectangularSubspaceLift P Q A‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro x
    change ‖(A (P.subtypeL.adjoint x) : E)‖ ≤ ‖A‖ * ‖x‖
    rw [Submodule.norm_coe]
    have hx : ‖P.subtypeL.adjoint x‖ ≤ ‖x‖ := by
      simpa only [Submodule.adjoint_subtypeL] using P.norm_orthogonalProjectionOnto_apply_le x
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg A))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (rectangularSubspaceLift P Q A))
    intro u
    have hid : P.subtypeL.adjoint (u : H) = u :=
      congrArg (fun B : P →L[ℝ] P => B u) P.subtypeₗᵢ.adjoint_comp_self
    have h := (rectangularSubspaceLift P Q A).le_opNorm (u : H)
    simpa only [rectangularSubspaceLift, ContinuousLinearMap.comp_apply, hid,
      Submodule.subtypeL_apply, Submodule.norm_coe] using h

/-- The actual HS columns of a zero-extended rectangular subspace operator. -/
def hsRectangularLiftColumns (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ P)
    (e : HilbertBasis η ℝ Q) (c : HilbertSchmidtColumns κ Q) : HilbertSchmidtColumns ι E :=
  hsLeftComposition Q.subtypeL (hsRightComposition d b e P.subtypeL.adjoint c)

theorem hilbertSchmidtOperator_rectangularLift (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ P)
    (e : HilbertBasis η ℝ Q) (c : HilbertSchmidtColumns κ Q) :
    hilbertSchmidtOperator b (hsRectangularLiftColumns P Q b d e c) =
      rectangularSubspaceLift P Q (hilbertSchmidtOperator d c) := by
  rw [hsRectangularLiftColumns, hilbertSchmidtOperator_leftComposition,
    hilbertSchmidtOperator_rightComposition]
  rfl

/-- The covariance of an actual lifted operator has range in its actual domain
subspace. This is the support fact used for nonzero singular coordinates. -/
theorem hsRectangularLift_covariance_mem (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ P)
    (e : HilbertBasis η ℝ Q) (c : HilbertSchmidtColumns κ Q) (x : H) :
    hsSingularCovariance b (hsRectangularLiftColumns P Q b d e c) x ∈ P := by
  rw [hsSingularCovariance, hilbertSchmidtOperator_rectangularLift]
  simp only [rectangularSubspaceLift, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply]
  exact Subtype.property _

/-- Lifting cannot increase the actual finite Schatten sum. Nonzero singular
vectors of the lift lie in the actual domain subspace; Jensen and Bessel apply
there. Thus no Schatten ideal or singular-value minmax theorem is assumed. -/
theorem hsRectangularLift_singularPower_le (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ P)
    (e : HilbertBasis η ℝ Q) (c : HilbertSchmidtColumns κ Q) {p : ℝ} (hp : 2 ≤ p) :
    (∑' i : HSSingularIndex b (hsRectangularLiftColumns P Q b d e c), i.1 ^ (p / 2)) ≤
      ∑' i : HSSingularIndex d c, i.1 ^ (p / 2) := by
  classical
  let C := hsRectangularLiftColumns P Q b d e c
  let J := {j : HSSingularIndex b C // j.1 ≠ 0}
  have hmem (j : J) : hsSingularBasis b C j.1 ∈ P := by
    have he := compactEigenbasis_eigen (hsSingularCovariance b C)
      (hsSingularCovariance_isCompact b C) (hsSingularCovariance_isPositive b C).isSymmetric j.1
    have hm := hsRectangularLift_covariance_mem P Q b d e c (hsSingularBasis b C j.1)
    change hsSingularCovariance b C (hsSingularBasis b C j.1) ∈ P at hm
    change hsSingularCovariance b C (hsSingularBasis b C j.1) = j.1.1 • hsSingularBasis b C j.1 at he
    rw [he] at hm
    have hmi := P.smul_mem (j.1.1)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ j.2, one_smul] using hmi
  let v : J → P := fun j => ⟨hsSingularBasis b C j.1, hmem j⟩
  have hv : Orthonormal ℝ v := by
    apply P.subtypeₗᵢ.orthonormal_comp_iff.mp
    exact (hsSingularBasis b C).orthonormal.comp Subtype.val Subtype.val_injective
  have henergy (j : J) : ‖hilbertSchmidtOperator d c (v j)‖ ^ 2 = j.1.1 := by
    have hh := hsSingularBasis_image_norm_sq b C j.1
    rw [hilbertSchmidtOperator_rectangularLift] at hh
    have hid : P.subtypeL.adjoint (v j : H) = v j :=
      congrArg (fun B : P →L[ℝ] P => B (v j)) P.subtypeₗᵢ.adjoint_comp_self
    change ‖rectangularSubspaceLift P Q (hilbertSchmidtOperator d c) (v j : H)‖ ^ 2 = _ at hh
    simpa only [rectangularSubspaceLift, ContinuousLinearMap.comp_apply, hid,
      Submodule.subtypeL_apply, Submodule.norm_coe] using hh
  have hsum : (∑' j : J, j.1.1 ^ (p / 2)) =
      ∑' j : HSSingularIndex b C, j.1 ^ (p / 2) := by
    apply tsum_subtype_eq_of_support_subset
      (f := fun j : HSSingularIndex b C => j.1 ^ (p / 2)) (s := {j | j.1 ≠ 0})
    intro j hj
    change j.1 ≠ 0
    intro hz
    exact hj (by change j.1 ^ (p / 2) = 0; rw [hz, Real.zero_rpow (by linarith : p / 2 ≠ 0)])
  rw [← hsum]
  apply Real.tsum_le_of_sum_le (fun j : J => Real.rpow_nonneg (hsSingularValue_nonneg b C j.1) _)
  intro s
  simpa only [henergy] using hs_orthonormal_power_sum_le d c hp v hv s

/-- The actual rectangular zero extension satisfies the finite Schatten bound
proved above at the norm level. -/
theorem hsSchattenNorm_rectangularLift_le (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ P)
    (e : HilbertBasis η ℝ Q) (c : HilbertSchmidtColumns κ Q) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (hsRectangularLiftColumns P Q b d e c) p ≤ hsSchattenNorm d c p :=
  Real.rpow_le_rpow (tsum_nonneg (fun i => Real.rpow_nonneg
    (hsSingularValue_nonneg b (hsRectangularLiftColumns P Q b d e c) i) _))
    (hsRectangularLift_singularPower_le P Q b d e c hp) (one_div_nonneg.mpr (by linarith))

end Lift

/-- Actual zero extension of a finite compression is its ambient two-sided
rectangular coordinate compression. -/
theorem finiteRectangularCompression_lift (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (s : Finset ι) (t : Finset κ) (A : H →L[ℝ] E) :
    rectangularSubspaceLift (FiniteSpectralSubspace b s) (FiniteSpectralSubspace a t)
      (finiteRectangularCompression b a s t A) =
      (finiteBasisProjection a t).comp (A.comp (finiteBasisProjection b s)) := by
  let I := finiteSpectralInclusion b s
  let J := finiteSpectralInclusion a t
  change J.comp ((J.adjoint.comp (A.comp I)).comp I.adjoint) = _
  have heq : J.comp ((J.adjoint.comp (A.comp I)).comp I.adjoint) =
      (J.comp J.adjoint).comp (A.comp (I.comp I.adjoint)) := by
    simp only [ContinuousLinearMap.comp_assoc]
  rw [heq, finiteSpectralInclusion_comp_adjoint, finiteSpectralInclusion_comp_adjoint]

omit [CompleteSpace H] in
/-- A right coordinate truncation reconstructs the true rectangular right
compression, with unrelated domain and codomain Hilbert spaces. -/
theorem hilbertSchmidtOperator_finiteDomainColumns (b : HilbertBasis ι ℝ H)
    (s : Finset ι) (c : HilbertSchmidtColumns ι E) :
    hilbertSchmidtOperator b (hsFiniteColumns s c) =
      (hilbertSchmidtOperator b c).comp (finiteBasisProjection b s) := by
  classical
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro j
  rw [hilbertSchmidtOperator_basis, hsFiniteColumns_apply]
  change (if j ∈ s then c j else 0) = hilbertSchmidtOperator b c (finiteBasisProjection b s (b j))
  rw [finiteBasisProjection_basis]
  split_ifs <;> simp only [hilbertSchmidtOperator_basis, map_zero]

omit [CompleteSpace H] in
/-- Right finite compression converges in operator norm for actual rectangular
HS operators. No countable basis enumeration is used. -/
theorem hs_rectangular_right_compression_tendsto (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    Tendsto (fun s : Finset ι => (hilbertSchmidtOperator b c).comp (finiteBasisProjection b s))
      atTop (𝓝 (hilbertSchmidtOperator b c)) := by
  have h := (hilbertSchmidtOperator b).continuous.continuousAt.tendsto.comp (hsFiniteColumns_tendsto c)
  change Tendsto (fun s : Finset ι => hilbertSchmidtOperator b (hsFiniteColumns s c))
    atTop (𝓝 (hilbertSchmidtOperator b c)) at h
  simpa only [hilbertSchmidtOperator_finiteDomainColumns] using h

/-- Left finite compression follows from the actual adjoint construction. -/
theorem hs_rectangular_left_compression_tendsto (b : HilbertBasis ι ℝ H)
    (a : HilbertBasis κ ℝ E) (c : HilbertSchmidtColumns ι E) :
    Tendsto (fun t : Finset κ => (finiteBasisProjection a t).comp (hilbertSchmidtOperator b c))
      atTop (𝓝 (hilbertSchmidtOperator b c)) := by
  have hr := hs_rectangular_right_compression_tendsto a (hsAdjointColumns b a c)
  simp only [hilbertSchmidtOperator_adjoint] at hr
  have hc : Continuous (fun A : E →L[ℝ] H => A.adjoint) := ContinuousLinearMap.adjoint.continuous
  have ht := hc.continuousAt.tendsto.comp hr
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    (finiteBasisProjection_isSelfAdjoint a _).adjoint_eq, Function.comp_def] using ht

omit [CompleteSpace H] [CompleteSpace E] in
/-- Deterministic rectangular compression error, with actual coordinate
projection norm bounds. -/
theorem finiteRectangularCompression_error_le (b : HilbertBasis ι ℝ H)
    (a : HilbertBasis κ ℝ E) (s : Finset ι) (t : Finset κ) (A : H →L[ℝ] E) :
    ‖(finiteBasisProjection a t).comp (A.comp (finiteBasisProjection b s)) - A‖ ≤
      ‖A.comp (finiteBasisProjection b s) - A‖ + ‖(finiteBasisProjection a t).comp A - A‖ := by
  have heq : (finiteBasisProjection a t).comp (A.comp (finiteBasisProjection b s)) - A =
      (finiteBasisProjection a t).comp (A.comp (finiteBasisProjection b s) - A) +
        ((finiteBasisProjection a t).comp A - A) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_sub]
    abel
  rw [heq]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (finiteBasisProjection_norm_le a t) (norm_nonneg (A.comp (finiteBasisProjection b s) - A))))

/-- Two independent finite spectral selections converge to the actual
rectangular HS operator in operator norm. -/
theorem hs_rectangular_compression_tendsto (b : HilbertBasis ι ℝ H)
    (a : HilbertBasis κ ℝ E) (c : HilbertSchmidtColumns ι E) :
    Tendsto (fun st : Finset ι × Finset κ => (finiteBasisProjection a st.2).comp
      ((hilbertSchmidtOperator b c).comp (finiteBasisProjection b st.1)))
      (atTop ×ˢ atTop) (𝓝 (hilbertSchmidtOperator b c)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := (tendsto_iff_norm_sub_tendsto_zero.mp (hs_rectangular_right_compression_tendsto b c)).comp
    (tendsto_fst (f := atTop) (g := (atTop : Filter (Finset κ))))
  have hl := (tendsto_iff_norm_sub_tendsto_zero.mp (hs_rectangular_left_compression_tendsto b a c)).comp
    (tendsto_snd (f := (atTop : Filter (Finset ι))) (g := atTop))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hr.add hl) (fun _ => norm_nonneg _)
  intro st
  exact finiteRectangularCompression_error_le b a st.1 st.2 _

/-- A uniform finite-dimensional Schur estimate on the genuine selected
coordinate spaces. This is a visible general multiplier leaf, not an
interaction estimate or an infinite-dimensional HMS conclusion. -/
def FiniteSchurSchattenBound (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (M : κ → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K)
    (p C : ℝ) : Prop :=
  ∀ (s : Finset ι) (t : Finset κ) (c : HilbertSchmidtColumns s (FiniteSpectralSubspace a t)),
    hsSchattenNorm (finiteSpectralLabelBasis b s)
      (hsSchurMultiplier (finiteSpectralLabelBasis a t) (fun (i : t) (j : s) => M i j)
        K hK (fun i j => hM i j) c) p ≤
      C * hsSchattenNorm (finiteSpectralLabelBasis b s) c p

/-- A uniform bound for all true finite rectangular Schur multipliers extends
to the actual infinite HS DOI with the same finite Schatten constant. The
input compression bound, actual Schur compatibility, actual lifted HS columns,
and pointwise-limit inheritance are all proved rather than assumed. No
Schatten Banach-space completeness or minmax theorem is used.

The kernel is a general bounded matrix on arbitrary Hilbert-basis index types.
Only the named finite-dimensional multiplier estimate remains a premise.
-/
theorem hsSchur_schatten_bound_of_finite
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (M : κ → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K)
    {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C)
    (hfinite : FiniteSchurSchattenBound b a M K hK hM p C)
    (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (hsSchurMultiplier a M K hK hM c) p ≤ C * hsSchattenNorm b c p := by
  let D := hsSchurMultiplier a M K hK hM c
  let cs := fun st : Finset ι × Finset κ => hsRectangularLiftColumns
    (FiniteSpectralSubspace b st.1) (FiniteSpectralSubspace a st.2) b
    (finiteSpectralLabelBasis b st.1) (finiteSpectralLabelBasis a st.2)
    (finiteRectangularColumns b a st.1 st.2 D)
  have hreconstruct (st : Finset ι × Finset κ) : hilbertSchmidtOperator b (cs st) =
      (finiteBasisProjection a st.2).comp ((hilbertSchmidtOperator b D).comp (finiteBasisProjection b st.1)) := by
    dsimp only [cs]
    rw [hilbertSchmidtOperator_rectangularLift, hilbertSchmidtOperator_finiteRectangularColumns,
      finiteRectangularCompression_lift]
  have hconv : ∀ x, Tendsto (fun st => hilbertSchmidtOperator b (cs st) x)
      (atTop ×ˢ atTop) (𝓝 (hilbertSchmidtOperator b D x)) := by
    intro x
    have ht : Tendsto (fun st : Finset ι × Finset κ => hilbertSchmidtOperator b (cs st))
        (atTop ×ˢ atTop) (𝓝 (hilbertSchmidtOperator b D)) := by
      simpa only [hreconstruct] using hs_rectangular_compression_tendsto b a D
    exact (continuous_id.clm_apply continuous_const).continuousAt.tendsto.comp ht
  apply hsSchattenNorm_le_of_pointwise_tendsto b D (atTop ×ˢ atTop) cs hp
    (mul_nonneg hC (Real.rpow_nonneg (tsum_nonneg
      (fun i : HSSingularIndex b c => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _)) _)) hconv
  apply Eventually.of_forall
  intro st
  calc
    _ ≤ hsSchattenNorm (finiteSpectralLabelBasis b st.1)
        (finiteRectangularColumns b a st.1 st.2 D) p :=
      hsSchattenNorm_rectangularLift_le _ _ b _ _ _ hp
    _ = hsSchattenNorm (finiteSpectralLabelBasis b st.1)
        (hsSchurMultiplier (finiteSpectralLabelBasis a st.2)
          (fun (i : st.2) (j : st.1) => M i j) K hK (fun i j => hM i j)
          (finiteRectangularColumns b a st.1 st.2 c)) p := by
      rw [finiteSchur_compression_compatible]
    _ ≤ C * hsSchattenNorm (finiteSpectralLabelBasis b st.1)
        (finiteRectangularColumns b a st.1 st.2 c) p := hfinite st.1 st.2 _
    _ ≤ C * hsSchattenNorm b c p := mul_le_mul_of_nonneg_left
      (hsSchattenNorm_orthogonalCompression_le b (FiniteSpectralSubspace b st.1)
        (FiniteSpectralSubspace a st.2) (finiteSpectralLabelBasis b st.1) a c hp) hC

end
end KernelSeq
