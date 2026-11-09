import KernelSeq.HilbertSchmidt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Basis independence and adjoints of actual Hilbert--Schmidt operators

The proofs use Parseval and a nonnegative double series. Joint summability is
derived from the original column energy before interchanging the two sums.
All Hilbert bases and index types may be uncountable; neither ambient Hilbert
space is assumed separable.
-/

open scoped ENNReal

namespace KernelSeq

variable {ι κ η H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A square-summable column family gives a square-summable column family for
the actual adjoint, with exactly the same energy. The double-series convergence
is a conclusion of Parseval and the original column summability. -/
theorem hilbertBasis_adjoint_column_energy (b : HilbertBasis ι ℝ H)
    (e : HilbertBasis η ℝ E) (A : H →L[ℝ] E)
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)) :
    Summable (fun k => ‖A.adjoint (e k)‖ ^ 2) ∧
      (∑' k, ‖A.adjoint (e k)‖ ^ 2) = ∑' i, ‖A (b i)‖ ^ 2 := by
  let a : ι → η → ℝ := fun i k => inner ℝ (e k) (A (b i)) ^ 2
  have hrows (i : ι) : Summable (a i) := by
    simpa only [a, HilbertBasis.repr_apply_apply] using
      hilbertBasis_coefficients_sq_summable e (A (b i))
  have hrows_sum (i : ι) : (∑' k, a i k) = ‖A (b i)‖ ^ 2 := by
    simpa only [a, HilbertBasis.repr_apply_apply] using
      (hilbertBasis_norm_sq_eq_tsum e (A (b i))).symm
  have hpairs : Summable (fun p : ι × η => a p.1 p.2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg (inner ℝ (e p.2) (A (b p.1))))).2
    exact ⟨hrows, hA.congr (fun i => (hrows_sum i).symm)⟩
  have hcols_sum (k : η) : (∑' i, a i k) = ‖A.adjoint (e k)‖ ^ 2 := by
    calc
      (∑' i, a i k) = ∑' i, b.repr (A.adjoint (e k)) i ^ 2 := by
        apply tsum_congr
        intro i
        simp only [a, HilbertBasis.repr_apply_apply, A.adjoint_inner_right,
          real_inner_comm (A (b i)) (e k)]
      _ = ‖A.adjoint (e k)‖ ^ 2 := (hilbertBasis_norm_sq_eq_tsum b _).symm
  have hscols : Summable (fun k => ‖A.adjoint (e k)‖ ^ 2) := by
    exact hpairs.prod_symm.prod.congr hcols_sum
  refine ⟨hscols, ?_⟩
  calc
    (∑' k, ‖A.adjoint (e k)‖ ^ 2) = ∑' k, ∑' i, a i k :=
      tsum_congr (fun k => (hcols_sum k).symm)
    _ = ∑' i, ∑' k, a i k := hpairs.tsum_comm
    _ = ∑' i, ‖A (b i)‖ ^ 2 := tsum_congr hrows_sum

/-- The column energy of an actual operator is independent of the domain
Hilbert basis, and square summability in the new basis is derived. -/
theorem hilbertBasis_column_energy_invariant (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ H) (A : H →L[ℝ] E)
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)) :
    Summable (fun j => ‖A (d j)‖ ^ 2) ∧
      (∑' j, ‖A (d j)‖ ^ 2) = ∑' i, ‖A (b i)‖ ^ 2 := by
  obtain ⟨s, ⟨e⟩⟩ := exists_hilbertBasis ℝ E
  have ha := hilbertBasis_adjoint_column_energy b e A hA
  have hb := hilbertBasis_adjoint_column_energy e d A.adjoint ha.1
  simpa only [ContinuousLinearMap.adjoint_adjoint, ha.2] using hb

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The original Hilbert--Schmidt columns have genuinely summable energy. -/
theorem hsColumns_sq_summable (c : HilbertSchmidtColumns ι E) :
    Summable (fun i => ‖c i‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp c).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- The exact requested basis-invariant energy identity for the constructed
Hilbert--Schmidt operator, together with actual new-column summability. -/
theorem hilbertSchmidtOperator_basis_energy (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ H) (c : HilbertSchmidtColumns ι E) :
    Summable (fun j => ‖hilbertSchmidtOperator b c (d j)‖ ^ 2) ∧
      (∑' j, ‖hilbertSchmidtOperator b c (d j)‖ ^ 2) = ‖c‖ ^ 2 := by
  have hA : Summable (fun i => ‖hilbertSchmidtOperator b c (b i)‖ ^ 2) := by
    simpa only [hilbertSchmidtOperator_basis] using hsColumns_sq_summable c
  have h := hilbertBasis_column_energy_invariant b d (hilbertSchmidtOperator b c) hA
  simpa only [hilbertSchmidtOperator_basis, ← hsColumns_norm_sq] using h

/-- The very same actual operator written as square-summable columns in another
domain Hilbert basis. Membership in `ℓ²` is proved, not assumed. -/
noncomputable def hsRebase (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ H)
    (c : HilbertSchmidtColumns ι E) : HilbertSchmidtColumns κ E :=
  ⟨fun j => hilbertSchmidtOperator b c (d j),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hilbertSchmidtOperator_basis_energy b d c).1)⟩

@[simp]
theorem hsRebase_apply (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ H)
    (c : HilbertSchmidtColumns ι E) (j : κ) :
    hsRebase b d c j = hilbertSchmidtOperator b c (d j) := rfl

/-- Changing columns preserves the actual Hilbert--Schmidt norm exactly. -/
theorem hsRebase_norm (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ H)
    (c : HilbertSchmidtColumns ι E) : ‖hsRebase b d c‖ = ‖c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hsColumns_norm_sq]
  exact (hilbertSchmidtOperator_basis_energy b d c).2

/-- The rebased columns reconstruct the original bounded operator. -/
theorem hilbertSchmidtOperator_rebase (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ H) (c : HilbertSchmidtColumns ι E) :
    hilbertSchmidtOperator d (hsRebase b d c) = hilbertSchmidtOperator b c := by
  apply continuousLinearMap_eq_of_hilbertBasis d
  intro j
  rw [hilbertSchmidtOperator_basis, hsRebase_apply]

/-- The actual adjoint has square-summable columns with the original column
energy, without any restriction on the codomain basis index. -/
theorem hilbertSchmidtOperator_adjoint_energy (b : HilbertBasis ι ℝ H)
    (e : HilbertBasis η ℝ E) (c : HilbertSchmidtColumns ι E) :
    Summable (fun k => ‖(hilbertSchmidtOperator b c).adjoint (e k)‖ ^ 2) ∧
      (∑' k, ‖(hilbertSchmidtOperator b c).adjoint (e k)‖ ^ 2) = ‖c‖ ^ 2 := by
  have hA : Summable (fun i => ‖hilbertSchmidtOperator b c (b i)‖ ^ 2) := by
    simpa only [hilbertSchmidtOperator_basis] using hsColumns_sq_summable c
  have h := hilbertBasis_adjoint_column_energy b e (hilbertSchmidtOperator b c) hA
  simpa only [hilbertSchmidtOperator_basis, ← hsColumns_norm_sq] using h

/-- Actual Hilbert--Schmidt columns representing the adjoint operator. -/
noncomputable def hsAdjointColumns (b : HilbertBasis ι ℝ H) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) : HilbertSchmidtColumns η H :=
  ⟨fun k => (hilbertSchmidtOperator b c).adjoint (e k),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hilbertSchmidtOperator_adjoint_energy b e c).1)⟩

@[simp]
theorem hsAdjointColumns_apply (b : HilbertBasis ι ℝ H) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) (k : η) :
    hsAdjointColumns b e c k = (hilbertSchmidtOperator b c).adjoint (e k) := rfl

/-- Hilbert--Schmidt norm is exactly invariant under the actual adjoint. -/
theorem hsAdjointColumns_norm (b : HilbertBasis ι ℝ H) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) : ‖hsAdjointColumns b e c‖ = ‖c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hsColumns_norm_sq]
  exact (hilbertSchmidtOperator_adjoint_energy b e c).2

/-- The new columns reconstruct the actual adjoint, not merely an operator
whose norm happens to have the desired value. -/
theorem hilbertSchmidtOperator_adjoint (b : HilbertBasis ι ℝ H)
    (e : HilbertBasis η ℝ E) (c : HilbertSchmidtColumns ι E) :
    hilbertSchmidtOperator e (hsAdjointColumns b e c) = (hilbertSchmidtOperator b c).adjoint := by
  apply continuousLinearMap_eq_of_hilbertBasis e
  intro k
  rw [hilbertSchmidtOperator_basis, hsAdjointColumns_apply]

end KernelSeq
