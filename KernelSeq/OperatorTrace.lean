import KernelSeq.HilbertSchmidtIdeal

/-!
# Traces of actual Hilbert--Schmidt products and positive comparison

`basisTrace` is a diagonal sum in a specified Hilbert basis. Its linearity and
comparison statements below have explicit diagonal summability hypotheses.
For actual Hilbert--Schmidt products, diagonal summability and basis independence
are proved from the column Hilbert structure. This module does not construct
the full Banach ideal of trace-class operators.
-/

namespace KernelSeq

variable {ι κ η H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A specified-basis diagonal sum. Without summability this definition alone
does not assert that the operator is trace class or that the value is invariant. -/
noncomputable def basisTrace (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) : ℝ :=
  ∑' i, inner ℝ (b i) (A (b i))

/-- Addition of diagonal traces is justified by actual diagonal summability. -/
theorem basisTrace_add (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : Summable (fun i => inner ℝ (b i) (A (b i))))
    (hB : Summable (fun i => inner ℝ (b i) (B (b i)))) :
    basisTrace b (A + B) = basisTrace b A + basisTrace b B := by
  simpa only [basisTrace, _root_.add_apply, inner_add_right] using hA.tsum_add hB

/-- Subtraction is also stated only with summable diagonal series. -/
theorem basisTrace_sub (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : Summable (fun i => inner ℝ (b i) (A (b i))))
    (hB : Summable (fun i => inner ℝ (b i) (B (b i)))) :
    basisTrace b (A - B) = basisTrace b A - basisTrace b B := by
  simpa only [basisTrace, _root_.sub_apply, inner_sub_right] using hA.tsum_sub hB

/-- Scalar trace linearity, justified by the given convergent diagonal sum. -/
theorem basisTrace_smul (b : HilbertBasis ι ℝ H) (a : ℝ) (A : H →L[ℝ] H)
    (hA : Summable (fun i => inner ℝ (b i) (A (b i)))) :
    basisTrace b (a • A) = a * basisTrace b A := by
  simpa only [basisTrace, _root_.smul_apply, inner_smul_right, smul_eq_mul] using
    (hA.hasSum.const_smul a).tsum_eq

variable [CompleteSpace H] [CompleteSpace E]

/-- Actual Hilbert--Schmidt products have summable diagonals, and their trace
is the genuine inner product of their square-summable column families. -/
theorem hilbertSchmidtProduct_trace (b : HilbertBasis ι ℝ H)
    (c d : HilbertSchmidtColumns ι E) :
    Summable (fun i => inner ℝ (b i)
      (((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b d)) (b i))) ∧
      basisTrace b ((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b d)) =
        inner ℝ c d := by
  constructor
  · simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      hilbertSchmidtOperator_basis] using lp.summable_inner c d
  · simpa only [basisTrace, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, hilbertSchmidtOperator_basis] using
      (lp.inner_eq_tsum c d).symm

/-- The trace of `A* A` is its exact Hilbert--Schmidt energy. -/
theorem hilbertSchmidtSquare_trace (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    basisTrace b ((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b c)) =
      ‖c‖ ^ 2 := by
  rw [(hilbertSchmidtProduct_trace b c c).2, real_inner_self_eq_norm_sq]

/-- Rebase preserves addition because it reconstructs the same actual operator. -/
theorem hsRebase_add (b : HilbertBasis ι ℝ H) (g : HilbertBasis κ ℝ H)
    (c d : HilbertSchmidtColumns ι E) :
    hsRebase b g (c + d) = hsRebase b g c + hsRebase b g d := by
  ext j
  simp only [hsRebase_apply, map_add, _root_.add_apply, lp.coeFn_add, Pi.add_apply]

/-- Real polarization converts the proved norm invariance into genuine
Hilbert--Schmidt inner-product invariance. -/
theorem hsRebase_inner (b : HilbertBasis ι ℝ H) (g : HilbertBasis κ ℝ H)
    (c d : HilbertSchmidtColumns ι E) :
    inner ℝ (hsRebase b g c) (hsRebase b g d) = inner ℝ c d := by
  have h := norm_add_sq_real (hsRebase b g c) (hsRebase b g d)
  rw [← hsRebase_add, hsRebase_norm, hsRebase_norm, hsRebase_norm] at h
  linarith [norm_add_sq_real c d]

/-- Mixed products have summable diagonals in every Hilbert basis, with the
same trace. Neither index type nor ambient space is assumed separable. -/
theorem hilbertSchmidtProduct_trace_in_basis (b : HilbertBasis ι ℝ H)
    (g : HilbertBasis κ ℝ H) (c d : HilbertSchmidtColumns ι E) :
    Summable (fun j => inner ℝ (g j)
      (((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b d)) (g j))) ∧
      basisTrace g ((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b d)) =
        inner ℝ c d := by
  have h := hilbertSchmidtProduct_trace g (hsRebase b g c) (hsRebase b g d)
  simpa only [hilbertSchmidtOperator_rebase, hsRebase_inner] using h

/-- The actual mixed HS-product trace is independent of the chosen basis. -/
theorem hilbertSchmidtProduct_trace_basis_independent (b : HilbertBasis ι ℝ H)
    (g : HilbertBasis κ ℝ H) (c d : HilbertSchmidtColumns ι E) :
    basisTrace g ((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b d)) =
      basisTrace b ((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b d)) := by
  rw [(hilbertSchmidtProduct_trace_in_basis b g c d).2,
    (hilbertSchmidtProduct_trace b c d).2]

/-- The trace Cauchy--Schwarz inequality for actual mixed HS products. -/
theorem hilbertSchmidtProduct_trace_abs_le (b : HilbertBasis ι ℝ H)
    (g : HilbertBasis κ ℝ H) (c d : HilbertSchmidtColumns ι E) :
    |basisTrace g ((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b d))| ≤
      ‖c‖ * ‖d‖ := by
  rw [(hilbertSchmidtProduct_trace_in_basis b g c d).2]
  exact abs_real_inner_le_norm c d

/-- The square trace is the same Hilbert--Schmidt energy in any domain basis. -/
theorem hilbertSchmidtSquare_trace_in_basis (b : HilbertBasis ι ℝ H)
    (g : HilbertBasis κ ℝ H) (c : HilbertSchmidtColumns ι E) :
    basisTrace g ((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b c)) =
      ‖c‖ ^ 2 := by
  rw [(hilbertSchmidtProduct_trace_in_basis b g c c).2, real_inner_self_eq_norm_sq]

/-- The other square `A A*` also has genuinely summable diagonals, and its
trace equals the same energy for every codomain Hilbert basis. -/
theorem hilbertSchmidtSelfAdjointProduct_trace (b : HilbertBasis ι ℝ H)
    (e : HilbertBasis η ℝ E) (c : HilbertSchmidtColumns ι E) :
    Summable (fun k => inner ℝ (e k)
      (((hilbertSchmidtOperator b c).comp (hilbertSchmidtOperator b c).adjoint) (e k))) ∧
      basisTrace e ((hilbertSchmidtOperator b c).comp (hilbertSchmidtOperator b c).adjoint) =
        ‖c‖ ^ 2 := by
  have h := hilbertSchmidtProduct_trace e (hsAdjointColumns b e c) (hsAdjointColumns b e c)
  simpa only [hilbertSchmidtOperator_adjoint, ContinuousLinearMap.adjoint_adjoint,
    real_inner_self_eq_norm_sq, hsAdjointColumns_norm] using h

/-- The actual cyclic square identity `trace(A A*) = trace(A* A)`. -/
theorem hilbertSchmidtSquare_trace_cyclic (b : HilbertBasis ι ℝ H)
    (e : HilbertBasis η ℝ E) (c : HilbertSchmidtColumns ι E) :
    basisTrace e ((hilbertSchmidtOperator b c).comp (hilbertSchmidtOperator b c).adjoint) =
      basisTrace b ((hilbertSchmidtOperator b c).adjoint.comp (hilbertSchmidtOperator b c)) := by
  rw [(hilbertSchmidtSelfAdjointProduct_trace b e c).2, hilbertSchmidtSquare_trace]

omit [CompleteSpace H] in
/-- Domination by a positive operator with finite diagonal energy proves the
smaller positive operator's diagonal summability and trace comparison. This is
a theorem about actual Loewner order, not an assumed scalar comparison. -/
theorem positive_basisTrace_mono (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : 0 ≤ A) (hAB : A ≤ B)
    (hB : Summable (fun i => inner ℝ (b i) (B (b i)))) :
    Summable (fun i => inner ℝ (b i) (A (b i))) ∧ basisTrace b A ≤ basisTrace b B := by
  have hnonneg (i : ι) : 0 ≤ inner ℝ (b i) (A (b i)) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive A).mp hA).inner_nonneg_right (b i)
  have hle (i : ι) : inner ℝ (b i) (A (b i)) ≤ inner ℝ (b i) (B (b i)) := by
    have h := ((ContinuousLinearMap.le_def A B).mp hAB).inner_nonneg_right (b i)
    simpa only [_root_.sub_apply, inner_sub_right, sub_nonneg] using h
  have hsum := Summable.of_nonneg_of_le hnonneg hle hB
  exact ⟨hsum, hsum.tsum_le_tsum hle hB⟩

end KernelSeq
