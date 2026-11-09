import KernelSeq.SpectralEnergy
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Actual Hilbert--Schmidt columns and their bounded operators

Relative to a fixed complete orthonormal basis of the domain, a square-summable
family of columns is a Hilbert space. It defines an actual bounded operator by
the norm-convergent series `Σ <b_i,x> c_i`; its operator norm is bounded by its
column Hilbert norm. The construction is injective and recovers every column.
Rank-one operators have their exact Hilbert--Schmidt norm, not merely an
unrelated surrogate. Basis independence is proved in `HilbertSchmidtInvariant`;
the ideal operations are in `HilbertSchmidtIdeal`. The full Schatten calculus
remains a separate development.
-/

open scoped BigOperators ENNReal

namespace KernelSeq

/-- The Hilbert space of square-summable columns relative to a domain basis. -/
abbrev HilbertSchmidtColumns (ι E : Type*) [NormedAddCommGroup E] : Type _ :=
  lp (fun _ : ι => E) 2

variable {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The column norm is the genuine sum of squared column norms. -/
theorem hsColumns_norm_sq (c : HilbertSchmidtColumns ι E) :
    ‖c‖ ^ 2 = ∑' i, ‖c i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  simp only [real_inner_self_eq_norm_sq]

variable [CompleteSpace E]

/-- Hölder pairing of square-summable vector columns with scalar coordinates. -/
noncomputable def hsColumnPairing :
    HilbertSchmidtColumns ι E →L[ℝ] lp (fun _ : ι => ℝ) 2 →L[ℝ] E :=
  lp.dualPairing 2 2 (fun _ : ι => (ContinuousLinearMap.lsmul ℝ ℝ :
    ℝ →L[ℝ] E →L[ℝ] E).flip)
    (K := 1) (fun _ => by
      rw [ContinuousLinearMap.opNorm_flip]
      exact ContinuousLinearMap.opNorm_lsmul_le)

theorem hsColumnPairing_apply (c : HilbertSchmidtColumns ι E)
    (a : lp (fun _ : ι => ℝ) 2) :
    hsColumnPairing c a = ∑' i, a i • c i := rfl

theorem hsColumnPairing_norm_le :
    ‖(hsColumnPairing : HilbertSchmidtColumns ι E →L[ℝ]
      lp (fun _ : ι => ℝ) 2 →L[ℝ] E)‖ ≤ 1 :=
  lp.norm_dualPairing _ _

/-- The actual operator attached to Hilbert--Schmidt columns, bundled linearly
and continuously as a map of the entire column Hilbert space. -/
noncomputable def hilbertSchmidtOperator (b : HilbertBasis ι ℝ H) :
    HilbertSchmidtColumns ι E →L[ℝ] H →L[ℝ] E :=
  (ContinuousLinearMap.precompR H
    (hsColumnPairing : HilbertSchmidtColumns ι E →L[ℝ]
      lp (fun _ : ι => ℝ) 2 →L[ℝ] E)).flip
        b.repr.toContinuousLinearEquiv.toContinuousLinearMap

theorem hilbertSchmidtOperator_apply (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (x : H) :
    hilbertSchmidtOperator b c x = ∑' i, b.repr x i • c i := rfl

/-- The operator norm is bounded by the genuine Hilbert--Schmidt column norm. -/
theorem hilbertSchmidtOperator_le (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) : ‖hilbertSchmidtOperator b c‖ ≤ ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
  intro x
  let Q : HilbertSchmidtColumns ι E →L[ℝ] lp (fun _ : ι => ℝ) 2 →L[ℝ] E := hsColumnPairing
  have hQ : ‖Q‖ ≤ 1 := hsColumnPairing_norm_le
  have h := (Q c).le_of_opNorm_le (Q.le_of_opNorm_le hQ c) (b.repr x)
  change ‖Q c (b.repr x)‖ ≤ ‖c‖ * ‖x‖
  simpa only [one_mul, LinearIsometryEquiv.norm_map] using h

theorem hilbertSchmidtOperator_norm_le (b : HilbertBasis ι ℝ H) :
    ‖(hilbertSchmidtOperator b : HilbertSchmidtColumns ι E →L[ℝ] H →L[ℝ] E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro c
  simpa only [one_mul] using hilbertSchmidtOperator_le b c

/-- The column construction recovers every basis image exactly. -/
theorem hilbertSchmidtOperator_basis (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (i : ι) :
    hilbertSchmidtOperator b c (b i) = c i := by
  classical
  rw [hilbertSchmidtOperator_apply]
  simp [b.repr_self, Pi.single_apply]

/-- Distinct Hilbert--Schmidt columns cannot represent the same operator. -/
theorem hilbertSchmidtOperator_injective (b : HilbertBasis ι ℝ H) :
    Function.Injective (hilbertSchmidtOperator b : HilbertSchmidtColumns ι E → H →L[ℝ] E) := by
  intro c d h
  ext i
  rw [← hilbertSchmidtOperator_basis b c i, ← hilbertSchmidtOperator_basis b d i]
  exact congrArg (fun A : H →L[ℝ] E => A (b i)) h

/-- Rank-one Hilbert--Schmidt columns, constructed through an actual bounded
map on `ℓ²`, hence square summability is not an input assumption. -/
noncomputable def hsRankOne (b : HilbertBasis ι ℝ H) (u : E) (v : H) :
    HilbertSchmidtColumns ι E :=
  lp.mapCLM 2 (fun _ : ι => ContinuousLinearMap.toSpanSingleton ℝ u)
    (norm_nonneg u) (fun _ => by simp) (b.repr v)

omit [CompleteSpace E] in
@[simp]
theorem hsRankOne_apply (b : HilbertBasis ι ℝ H) (u : E) (v : H) (i : ι) :
    hsRankOne b u v i = b.repr v i • u := by
  simp [hsRankOne]

/-- These columns represent exactly the usual rank-one operator. -/
theorem hilbertSchmidtOperator_rankOne (b : HilbertBasis ι ℝ H) (u : E) (v : H) :
    hilbertSchmidtOperator b (hsRankOne b u v) = InnerProductSpace.rankOne ℝ u v := by
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro i
  rw [hilbertSchmidtOperator_basis, hsRankOne_apply, b.repr_apply_apply]
  simp [real_inner_comm]

omit [CompleteSpace E] in
theorem hsRankOne_norm_sq (b : HilbertBasis ι ℝ H) (u : E) (v : H) :
    ‖hsRankOne b u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [hsColumns_norm_sq]
  calc
    (∑' i, ‖hsRankOne b u v i‖ ^ 2) = ∑' i, b.repr v i ^ 2 * ‖u‖ ^ 2 := by
      apply tsum_congr
      intro i
      simp only [hsRankOne_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    _ = (∑' i, b.repr v i ^ 2) * ‖u‖ ^ 2 := tsum_mul_right
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by rw [← hilbertBasis_norm_sq_eq_tsum b v]; ring

omit [CompleteSpace E] in
/-- The exact Hilbert--Schmidt norm of a rank-one operator. -/
theorem hsRankOne_norm (b : HilbertBasis ι ℝ H) (u : E) (v : H) :
    ‖hsRankOne b u v‖ = ‖u‖ * ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mp
  rw [hsRankOne_norm_sq, mul_pow]

/-- Rank-one Hilbert--Schmidt columns are a genuine continuous bilinear map.
This supplies strong measurability of the random rank-one covariance in the
column Hilbert space, rather than assuming that measurability. -/
noncomputable def hsRankOneBilin (b : HilbertBasis ι ℝ H) :
    E →L[ℝ] H →L[ℝ] HilbertSchmidtColumns ι E :=
  (LinearMap.mk₂ ℝ (hsRankOne b)
    (by
      intro u v w
      ext i
      simp only [hsRankOne_apply, lp.coeFn_add, Pi.add_apply, smul_add])
    (by
      intro a u v
      ext i
      simp only [hsRankOne_apply, lp.coeFn_smul, Pi.smul_apply]
      exact smul_comm _ _ _)
    (by
      intro u v w
      ext i
      simp only [hsRankOne_apply, map_add, lp.coeFn_add, Pi.add_apply, add_smul])
    (by
      intro a u v
      ext i
      simp only [hsRankOne_apply, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        mul_smul])).mkContinuous₂ 1 (fun u v => by
          change ‖hsRankOne b u v‖ ≤ 1 * ‖u‖ * ‖v‖
          rw [hsRankOne_norm, one_mul])

omit [CompleteSpace E] in
@[simp]
theorem hsRankOneBilin_apply (b : HilbertBasis ι ℝ H) (u : E) (v : H) :
    hsRankOneBilin b u v = hsRankOne b u v := rfl

end KernelSeq
