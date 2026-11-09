import KernelSeq.HilbertSchmidtIdeal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Actual finite spectral compressions and operator-norm convergence

Finite subsets of an arbitrary Hilbert basis give genuine orthogonal finite-rank
projections. Hilbert--Schmidt column truncation proves right-compression
convergence, and the actual adjoint proves left-compression convergence. These
give the operator-norm limit of the two-sided compressions, without countability
of the basis index or an assumed compression-limit certificate.
-/

open Filter Topology Submodule
open scoped ENNReal

namespace KernelSeq

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance : DecidableEq ι := Classical.decEq ι

/-- The actual coordinate projection onto a finite selection of basis vectors. -/
noncomputable def finiteBasisProjection (b : HilbertBasis ι ℝ H) (s : Finset ι) : H →L[ℝ] H := by
  classical
  exact hilbertDiagonal b (fun i => if i ∈ s then 1 else 0) 1 zero_le_one
    (fun i => by split_ifs <;> norm_num)

omit [CompleteSpace H] in
/-- The projection keeps exactly the selected coordinates. -/
theorem finiteBasisProjection_repr (b : HilbertBasis ι ℝ H) (s : Finset ι) (x : H) (i : ι) :
    b.repr (finiteBasisProjection b s x) i = if i ∈ s then b.repr x i else 0 := by
  classical
  rw [finiteBasisProjection, hilbertDiagonal_repr]
  split_ifs <;> simp

omit [CompleteSpace H] in
/-- Its actual action is the finite Hilbert-basis expansion. -/
theorem finiteBasisProjection_apply (b : HilbertBasis ι ℝ H) (s : Finset ι) (x : H) :
    finiteBasisProjection b s x = ∑ i ∈ s, b.repr x i • b i := by
  classical
  apply b.repr.injective
  ext j
  simp only [finiteBasisProjection_repr, map_sum, lp.coeFn_sum, Finset.sum_apply,
    map_smul, lp.coeFn_smul, Pi.smul_apply, b.repr_self, lp.single_apply, smul_eq_mul]
  simp [Pi.single_apply]

omit [CompleteSpace H] in
theorem finiteBasisProjection_basis (b : HilbertBasis ι ℝ H) (s : Finset ι) (j : ι) :
    finiteBasisProjection b s (b j) = if j ∈ s then b j else 0 := by
  classical
  rw [finiteBasisProjection_apply]
  simp [b.repr_self, Pi.single_apply]

omit [CompleteSpace H] in
/-- This is precisely the finite sum of the manuscript's rank-one projections. -/
theorem finiteBasisProjection_eq_sum_rankOne (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    finiteBasisProjection b s = ∑ i ∈ s, InnerProductSpace.rankOne ℝ (b i) (b i) := by
  ext x
  rw [finiteBasisProjection_apply]
  simp only [_root_.sum_apply, InnerProductSpace.rankOne_apply, HilbertBasis.repr_apply_apply]

theorem finiteBasisProjection_isSelfAdjoint (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    IsSelfAdjoint (finiteBasisProjection b s) := by
  classical
  exact (hilbertDiagonal_isSymmetric b _ _ _ _).isSelfAdjoint

omit [CompleteSpace H] in
theorem finiteBasisProjection_sq (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    finiteBasisProjection b s * finiteBasisProjection b s = finiteBasisProjection b s := by
  ext x
  apply b.repr.injective
  ext i
  simp only [mul_apply_eq_comp, finiteBasisProjection_repr]
  split_ifs <;> rfl

omit [CompleteSpace H] in
theorem finiteBasisProjection_norm_le (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    ‖finiteBasisProjection b s‖ ≤ 1 := by
  classical
  exact hilbertDiagonal_norm_le b _ _ _ _

omit [CompleteSpace H] in
theorem finiteBasisProjection_range_le (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    (finiteBasisProjection b s).range ≤ span ℝ (b '' (s : Set ι)) := by
  rintro _ ⟨x, rfl⟩
  change finiteBasisProjection b s x ∈ span ℝ (b '' (s : Set ι))
  rw [finiteBasisProjection_apply]
  apply sum_mem
  intro i hi
  exact smul_mem _ _ (subset_span ⟨i, hi, rfl⟩)

omit [CompleteSpace H] in
/-- Finite rank is proved from the actual range inclusion into a finite span. -/
theorem finiteBasisProjection_finiteDimensional_range (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    FiniteDimensional ℝ (finiteBasisProjection b s).range := by
  letI := FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image b)
  exact Submodule.finiteDimensional_of_le (finiteBasisProjection_range_le b s)

/-- The actual finitely supported Hilbert--Schmidt column family. -/
noncomputable def hsFiniteColumns (s : Finset ι) (c : HilbertSchmidtColumns ι H) :
    HilbertSchmidtColumns ι H := by
  classical
  exact ∑ i ∈ s, lp.single 2 i (c i)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem hsFiniteColumns_apply (s : Finset ι) (c : HilbertSchmidtColumns ι H) (j : ι) :
    hsFiniteColumns s c j = if j ∈ s then c j else 0 := by
  classical
  unfold hsFiniteColumns
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  exact Finset.sum_pi_single j (fun i => c i) s

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Column truncations converge in the actual Hilbert--Schmidt norm over the
directed set of all finite subsets, including uncountable index types. -/
theorem hsFiniteColumns_tendsto (c : HilbertSchmidtColumns ι H) :
    Tendsto (fun s : Finset ι => hsFiniteColumns s c) atTop (𝓝 c) := by
  classical
  exact lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) c

/-- These finite columns reconstruct exactly the right-compressed operator. -/
theorem hilbertSchmidtOperator_hsFiniteColumns (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (c : HilbertSchmidtColumns ι H) :
    hilbertSchmidtOperator b (hsFiniteColumns s c) =
      hilbertSchmidtOperator b c * finiteBasisProjection b s := by
  classical
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro j
  rw [hilbertSchmidtOperator_basis, hsFiniteColumns_apply]
  change (if j ∈ s then c j else 0) = hilbertSchmidtOperator b c (finiteBasisProjection b s (b j))
  rw [finiteBasisProjection_basis]
  split_ifs <;> simp only [hilbertSchmidtOperator_basis, map_zero]

/-- Right compression converges in actual operator norm, by the continuous
injection of the column Hilbert space into bounded operators. -/
theorem hs_right_compression_tendsto (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι H) :
    Tendsto (fun s : Finset ι => hilbertSchmidtOperator b c * finiteBasisProjection b s)
      atTop (𝓝 (hilbertSchmidtOperator b c)) := by
  have h := (hilbertSchmidtOperator b).continuous.continuousAt.tendsto.comp
    (hsFiniteColumns_tendsto c)
  change Tendsto (fun s : Finset ι => hilbertSchmidtOperator b (hsFiniteColumns s c))
    atTop (𝓝 (hilbertSchmidtOperator b c)) at h
  simpa only [hilbertSchmidtOperator_hsFiniteColumns] using h

/-- Left compression converges in actual operator norm by applying the right
result to the proved Hilbert--Schmidt columns of the actual adjoint. -/
theorem hs_left_compression_tendsto (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι H) :
    Tendsto (fun s : Finset ι => finiteBasisProjection b s * hilbertSchmidtOperator b c)
      atTop (𝓝 (hilbertSchmidtOperator b c)) := by
  let A := hilbertSchmidtOperator b c
  have hright : Tendsto (fun s : Finset ι => A.adjoint * finiteBasisProjection b s)
      atTop (𝓝 A.adjoint) := by
    simpa only [hilbertSchmidtOperator_adjoint] using
      hs_right_compression_tendsto b (hsAdjointColumns b b c)
  have hcont : Continuous (fun B : H →L[ℝ] H => B.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  have h := hcont.continuousAt.tendsto.comp hright
  have hadj (s : Finset ι) : (A.adjoint * finiteBasisProjection b s).adjoint =
      finiteBasisProjection b s * A := by
    change (A.adjoint.comp (finiteBasisProjection b s)).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp,
      (finiteBasisProjection_isSelfAdjoint b s).adjoint_eq, ContinuousLinearMap.adjoint_adjoint]
    rfl
  change Tendsto (fun s : Finset ι => (A.adjoint * finiteBasisProjection b s).adjoint)
    atTop (𝓝 A.adjoint.adjoint) at h
  simpa only [hadj, ContinuousLinearMap.adjoint_adjoint] using h

omit [CompleteSpace H] in
/-- A deterministic compression error estimate for arbitrary bounded operators;
the projection bound is proved above rather than supplied as a certificate. -/
theorem finiteBasisCompression_error_le (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (A : H →L[ℝ] H) :
    ‖finiteBasisProjection b s * A * finiteBasisProjection b s - A‖ ≤
      ‖A * finiteBasisProjection b s - A‖ + ‖finiteBasisProjection b s * A - A‖ := by
  let P := finiteBasisProjection b s
  have heq : P * A * P - A = P * (A * P - A) + (P * A - A) := by noncomm_ring
  change ‖P * A * P - A‖ ≤ _
  rw [heq]
  calc
    ‖P * (A * P - A) + (P * A - A)‖ ≤
        ‖P * (A * P - A)‖ + ‖P * A - A‖ := norm_add_le _ _
    _ ≤ ‖P‖ * ‖A * P - A‖ + ‖P * A - A‖ :=
      add_le_add (norm_mul_le _ _) le_rfl
    _ ≤ 1 * ‖A * P - A‖ + ‖P * A - A‖ := add_le_add
      (mul_le_mul_of_nonneg_right (finiteBasisProjection_norm_le b s) (norm_nonneg _)) le_rfl
    _ = _ := by rw [one_mul]

/-- The actual two-sided finite spectral compressions of every genuine HS
operator converge in operator norm along all finite subsets of the basis. -/
theorem hs_two_sided_compression_tendsto (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι H) :
    Tendsto (fun s : Finset ι =>
      finiteBasisProjection b s * hilbertSchmidtOperator b c * finiteBasisProjection b s)
      atTop (𝓝 (hilbertSchmidtOperator b c)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := tendsto_iff_norm_sub_tendsto_zero.mp (hs_right_compression_tendsto b c)
  have hl := tendsto_iff_norm_sub_tendsto_zero.mp (hs_left_compression_tendsto b c)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hr.add hl)
  · intro s
    exact norm_nonneg _
  · intro s
    exact finiteBasisCompression_error_le b s (hilbertSchmidtOperator b c)

omit [CompleteSpace H] in
/-- Compression cannot increase the actual operator norm. -/
theorem finiteBasisCompression_norm_le (b : HilbertBasis ι ℝ H) (s : Finset ι)
    (A : H →L[ℝ] H) :
    ‖finiteBasisProjection b s * A * finiteBasisProjection b s‖ ≤ ‖A‖ := by
  let P := finiteBasisProjection b s
  have hP : ‖P‖ ≤ 1 := finiteBasisProjection_norm_le b s
  have hPA : ‖P * A‖ ≤ ‖A‖ := (norm_mul_le _ _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hP (norm_nonneg A))
  have hprod : ‖P * A‖ * ‖P‖ ≤ ‖A‖ := by
    calc
      ‖P * A‖ * ‖P‖ ≤ ‖A‖ * 1 := mul_le_mul hPA hP (norm_nonneg P) (norm_nonneg A)
      _ = ‖A‖ := mul_one _
  exact (norm_mul_le _ _).trans hprod

omit [CompleteSpace H] in
/-- If the finite spectral set contains a genuine basis eigenvector realizing
the positive top eigenvalue, the compressed norm equals the original norm.
Existence of that eigenvector is not assumed by any compression-limit theorem. -/
theorem finiteBasisCompression_norm_eq_of_basis_eigen (b : HilbertBasis ι ℝ H)
    (s : Finset ι) (A : H →L[ℝ] H) (j : ι) (hj : j ∈ s)
    (he : A (b j) = ‖A‖ • b j) :
    ‖finiteBasisProjection b s * A * finiteBasisProjection b s‖ = ‖A‖ := by
  apply le_antisymm (finiteBasisCompression_norm_le b s A)
  have hec : (finiteBasisProjection b s * A * finiteBasisProjection b s) (b j) = ‖A‖ • b j := by
    simp only [mul_apply_eq_comp, finiteBasisProjection_basis, if_pos hj, he, map_smul]
  have h := (finiteBasisProjection b s * A * finiteBasisProjection b s).le_opNorm (b j)
  simpa only [hec, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg A),
    b.orthonormal.norm_eq_one, mul_one] using h

end KernelSeq
