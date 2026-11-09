import KernelSeq.HilbertSchmidtInvariant
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# The Hilbert--Schmidt ideal and compactness

Both sides of the ideal inequality refer to the actual reconstructed bounded
operators. Right composition is built from the actual adjoint, left composition,
and the actual adjoint again. No countability or separability assumption is used.
-/

open scoped ENNReal

namespace KernelSeq

variable {ι κ η H E F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Postcomposing every Hilbert--Schmidt column by a bounded map is an actual
bounded linear map on the column Hilbert spaces. -/
noncomputable def hsLeftComposition (B : E →L[ℝ] F) :
    HilbertSchmidtColumns ι E →L[ℝ] HilbertSchmidtColumns ι F :=
  lp.mapCLM 2 (fun _ => B) (norm_nonneg B) (fun _ => le_rfl)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem hsLeftComposition_apply (B : E →L[ℝ] F)
    (c : HilbertSchmidtColumns ι E) (i : ι) :
    hsLeftComposition B c i = B (c i) := by
  simp [hsLeftComposition]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The true left ideal bound in Hilbert--Schmidt norm. -/
theorem hsLeftComposition_norm_le (B : E →L[ℝ] F) (c : HilbertSchmidtColumns ι E) :
    ‖hsLeftComposition B c‖ ≤ ‖B‖ * ‖c‖ :=
  (hsLeftComposition B).le_of_opNorm_le
    (lp.norm_mapCLM_le 2 (fun _ => B) (norm_nonneg B) (fun _ => le_rfl)) c

omit [CompleteSpace H] in
/-- The transformed columns represent the actual postcomposition. -/
theorem hilbertSchmidtOperator_leftComposition (b : HilbertBasis ι ℝ H)
    (B : E →L[ℝ] F) (c : HilbertSchmidtColumns ι E) :
    hilbertSchmidtOperator b (hsLeftComposition B c) = B.comp (hilbertSchmidtOperator b c) := by
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro i
  simp only [hilbertSchmidtOperator_basis, hsLeftComposition_apply,
    ContinuousLinearMap.comp_apply]

/-- Precomposing an actual Hilbert--Schmidt operator, constructed without an
extra square-summability hypothesis on the new columns. The intermediate
codomain basis may be any Hilbert basis. -/
noncomputable def hsRightComposition (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ F) (e : HilbertBasis η ℝ E) (B : F →L[ℝ] H)
    (c : HilbertSchmidtColumns ι E) : HilbertSchmidtColumns κ E :=
  hsAdjointColumns e d (hsLeftComposition B.adjoint (hsAdjointColumns b e c))

/-- The true right ideal bound in Hilbert--Schmidt norm. -/
theorem hsRightComposition_norm_le (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ F) (e : HilbertBasis η ℝ E) (B : F →L[ℝ] H)
    (c : HilbertSchmidtColumns ι E) :
    ‖hsRightComposition b d e B c‖ ≤ ‖c‖ * ‖B‖ := by
  rw [hsRightComposition, hsAdjointColumns_norm]
  calc
    ‖hsLeftComposition B.adjoint (hsAdjointColumns b e c)‖ ≤
        ‖B.adjoint‖ * ‖hsAdjointColumns b e c‖ := hsLeftComposition_norm_le _ _
    _ = ‖c‖ * ‖B‖ := by rw [hsAdjointColumns_norm, LinearIsometryEquiv.norm_map]; ring

/-- The right-composed columns reconstruct exactly the actual precomposition. -/
theorem hilbertSchmidtOperator_rightComposition (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ F) (e : HilbertBasis η ℝ E) (B : F →L[ℝ] H)
    (c : HilbertSchmidtColumns ι E) :
    hilbertSchmidtOperator d (hsRightComposition b d e B c) =
      (hilbertSchmidtOperator b c).comp B := by
  rw [hsRightComposition, hilbertSchmidtOperator_adjoint,
    hilbertSchmidtOperator_leftComposition, hilbertSchmidtOperator_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_adjoint]

omit [CompleteSpace H] [CompleteSpace E] in
/-- Rank-one operators between two real Hilbert spaces factor through `ℝ`,
so they are compact without a finite-dimensional ambient space. -/
theorem isCompactOperator_rankOne_between (u : E) (v : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℝ u v) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℝ u)).comp_clm (innerSL ℝ v)

omit [CompleteSpace H] in
/-- A single column reconstructs its corresponding actual rank-one operator. -/
theorem hilbertSchmidtOperator_single [DecidableEq ι] (b : HilbertBasis ι ℝ H) (i : ι) (u : E) :
    hilbertSchmidtOperator b (lp.single 2 i u) = InnerProductSpace.rankOne ℝ u (b i) := by
  classical
  have hcol : hsRankOne b u (b i) = lp.single 2 i u := by
    ext j
    by_cases h : j = i
    · subst j
      simp [hsRankOne_apply, b.repr_self, lp.single_apply]
    · simp [hsRankOne_apply, b.repr_self, lp.single_apply, h]
  rw [← hcol, hilbertSchmidtOperator_rankOne]

omit [CompleteSpace H] in
/-- Hilbert--Schmidt operators are genuine operator-norm limits of finite sums
of rank-one operators. Convergence follows from `ℓ²` column convergence. -/
theorem hilbertSchmidtOperator_hasSum_rankOne (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    HasSum (fun i => InnerProductSpace.rankOne ℝ (c i) (b i)) (hilbertSchmidtOperator b c) := by
  classical
  simpa only [hilbertSchmidtOperator_single] using
    (hilbertSchmidtOperator b).hasSum (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) c)

omit [CompleteSpace H] in
/-- Every actual Hilbert--Schmidt operator is compact, for arbitrary Hilbert
spaces and arbitrary Hilbert-basis indices. -/
theorem hilbertSchmidtOperator_isCompact (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) : IsCompactOperator (hilbertSchmidtOperator b c) := by
  apply isCompactOperator_of_tendsto (hilbertSchmidtOperator_hasSum_rankOne b c)
  apply Filter.Eventually.of_forall
  intro s
  change (∑ i ∈ s, InnerProductSpace.rankOne ℝ (c i) (b i)) ∈
    compactOperator (RingHom.id ℝ) H E
  exact (compactOperator (RingHom.id ℝ) H E).sum_mem
    (fun i _ => isCompactOperator_rankOne_between (c i) (b i))

end KernelSeq
