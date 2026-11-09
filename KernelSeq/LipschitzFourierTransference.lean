import KernelSeq.LipschitzEvenSymbol
import KernelSeq.RectangularTriangularSchur

/-!
# Finite real phase transference for the fixed Lipschitz symbol

All phases are actual rotations on the real Hilbert direct sum `H ⊕ H`.
This module keeps the fixed-symbol Fourier multiplier estimate as an explicit
remaining analytic input. Phase conjugation and its inverse are constructed
and proved; they are not coefficient or norm certificates.
-/

open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

universe uν uι uH

variable {ι : Type uι} {H : Type uH}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Actual cosine diagonal for a finite family of real phases. -/
def realPhaseCos (b : HilbertBasis ι ℝ H) (u : ι → ℝ) : H →L[ℝ] H :=
  hilbertDiagonal b (fun i => Real.cos (u i)) 1 zero_le_one
    (fun i => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (u i))

/-- Actual sine diagonal for a finite family of real phases. -/
def realPhaseSin (b : HilbertBasis ι ℝ H) (u : ι → ℝ) : H →L[ℝ] H :=
  hilbertDiagonal b (fun i => Real.sin (u i)) 1 zero_le_one
    (fun i => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (u i))

theorem realPhaseCos_coefficient (b : HilbertBasis ι ℝ H) (u : ι → ℝ) (x : H) (i : ι) :
    inner ℝ (b i) (realPhaseCos b u x) = Real.cos (u i) * inner ℝ (b i) x := by
  simpa only [realPhaseCos, HilbertBasis.repr_apply_apply] using
    hilbertDiagonal_repr b (fun i => Real.cos (u i)) 1 zero_le_one
      (fun i => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (u i)) x i

theorem realPhaseSin_coefficient (b : HilbertBasis ι ℝ H) (u : ι → ℝ) (x : H) (i : ι) :
    inner ℝ (b i) (realPhaseSin b u x) = Real.sin (u i) * inner ℝ (b i) x := by
  simpa only [realPhaseSin, HilbertBasis.repr_apply_apply] using
    hilbertDiagonal_repr b (fun i => Real.sin (u i)) 1 zero_le_one
      (fun i => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (u i)) x i

/-- Genuine real block rotation implementing multiplication by the diagonal
complex phase, without introducing a complex Schatten space. -/
def realPhaseRotation (b : HilbertBasis ι ℝ H) (u : ι → ℝ) :
    WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ H H).symm.toContinuousLinearMap.comp
    (((realPhaseCos b u).comp (WithLp.fstL 2 ℝ H H) -
        (realPhaseSin b u).comp (WithLp.sndL 2 ℝ H H)).prod
      ((realPhaseSin b u).comp (WithLp.fstL 2 ℝ H H) +
        (realPhaseCos b u).comp (WithLp.sndL 2 ℝ H H)))

@[simp] theorem realPhaseRotation_fst (b : HilbertBasis ι ℝ H) (u : ι → ℝ)
    (z : WithLp 2 (H × H)) :
    (realPhaseRotation b u z).fst = realPhaseCos b u z.fst - realPhaseSin b u z.snd := rfl

@[simp] theorem realPhaseRotation_snd (b : HilbertBasis ι ℝ H) (u : ι → ℝ)
    (z : WithLp 2 (H × H)) :
    (realPhaseRotation b u z).snd = realPhaseSin b u z.fst + realPhaseCos b u z.snd := rfl

theorem realPhaseRotation_fst_coefficient (b : HilbertBasis ι ℝ H) (u : ι → ℝ)
    (z : WithLp 2 (H × H)) (i : ι) :
    inner ℝ (b i) (realPhaseRotation b u z).fst =
      Real.cos (u i) * inner ℝ (b i) z.fst - Real.sin (u i) * inner ℝ (b i) z.snd := by
  rw [realPhaseRotation_fst, inner_sub_right, realPhaseCos_coefficient, realPhaseSin_coefficient]

theorem realPhaseRotation_snd_coefficient (b : HilbertBasis ι ℝ H) (u : ι → ℝ)
    (z : WithLp 2 (H × H)) (i : ι) :
    inner ℝ (b i) (realPhaseRotation b u z).snd =
      Real.sin (u i) * inner ℝ (b i) z.fst + Real.cos (u i) * inner ℝ (b i) z.snd := by
  rw [realPhaseRotation_snd, inner_add_right, realPhaseSin_coefficient, realPhaseCos_coefficient]

variable [Fintype ι]

/-- Every constructed phase rotation is genuinely isometric. -/
theorem realPhaseRotation_norm (b : HilbertBasis ι ℝ H) (u : ι → ℝ)
    (z : WithLp 2 (H × H)) : ‖realPhaseRotation b u z‖ = ‖z‖ := by
  have heq : ‖realPhaseRotation b u z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    rw [← b.toOrthonormalBasis.sum_sq_inner_right, ← b.toOrthonormalBasis.sum_sq_inner_right,
      ← b.toOrthonormalBasis.sum_sq_inner_right, ← b.toOrthonormalBasis.sum_sq_inner_right]
    simp only [HilbertBasis.coe_toOrthonormalBasis, realPhaseRotation_fst_coefficient,
      realPhaseRotation_snd_coefficient, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi := Real.sin_sq_add_cos_sq (u i)
    nlinarith [sq_nonneg (inner ℝ (b i) z.fst), sq_nonneg (inner ℝ (b i) z.snd)]
  nlinarith [norm_nonneg (realPhaseRotation b u z), norm_nonneg z]

theorem realPhaseRotation_norm_le (b : HilbertBasis ι ℝ H) (u : ι → ℝ) :
    ‖realPhaseRotation b u‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [realPhaseRotation_norm, one_mul]

omit [Fintype ι] in
/-- The negative phase is the actual inverse, including empty bases. -/
theorem realPhaseRotation_neg_comp (b : HilbertBasis ι ℝ H) (u : ι → ℝ) :
    (realPhaseRotation b (fun i => -u i)).comp (realPhaseRotation b u) =
      ContinuousLinearMap.id ℝ (WithLp 2 (H × H)) := by
  ext z
  apply (WithLp.equiv 2 (H × H)).injective
  apply Prod.ext
  · apply b.repr.injective
    ext i
    simp only [HilbertBasis.repr_apply_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    change inner ℝ (b i) (realPhaseRotation b (fun i => -u i) (realPhaseRotation b u z)).fst =
      inner ℝ (b i) z.fst
    simp only [realPhaseRotation_fst_coefficient,
      realPhaseRotation_snd_coefficient, Real.cos_neg, Real.sin_neg]
    have hi := Real.sin_sq_add_cos_sq (u i)
    have hm := congrArg (fun r : ℝ => r * inner ℝ (b i) z.fst) hi
    nlinarith
  · apply b.repr.injective
    ext i
    simp only [HilbertBasis.repr_apply_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    change inner ℝ (b i) (realPhaseRotation b (fun i => -u i) (realPhaseRotation b u z)).snd =
      inner ℝ (b i) z.snd
    simp only [realPhaseRotation_fst_coefficient,
      realPhaseRotation_snd_coefficient, Real.cos_neg, Real.sin_neg]
    have hi := Real.sin_sq_add_cos_sq (u i)
    have hm := congrArg (fun r : ℝ => r * inner ℝ (b i) z.snd) hi
    nlinarith

/-- Actual phase conjugation on a real doubled operator. -/
def realPhaseConjugate (b : HilbertBasis ι ℝ H) (u : ι → ℝ)
    (A : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) :
    WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
  (realPhaseRotation b u).comp (A.comp (realPhaseRotation b (fun i => -u i)))

omit [Fintype ι] in
/-- Inverse conjugation recovers the actual original operator pointwise. -/
theorem realPhaseConjugate_neg (b : HilbertBasis ι ℝ H) (u : ι → ℝ)
    (A : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) :
    realPhaseConjugate b (fun i => -u i) (realPhaseConjugate b u A) = A := by
  have hinv (z : WithLp 2 (H × H)) :
      realPhaseRotation b (fun i => -u i) (realPhaseRotation b u z) = z :=
    congrArg (fun T : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) => T z)
      (realPhaseRotation_neg_comp b u)
  ext z
  simp only [realPhaseConjugate, ContinuousLinearMap.comp_apply, neg_neg]
  rw [hinv, hinv]

variable [CompleteSpace H]

/-- Actual phase conjugation is a Schatten contraction, proved by the actual
left/right ideal bounds and the constructed rotation norm bound. -/
theorem realPhaseConjugate_schatten_le (b : HilbertBasis ι ℝ H) (u : ι → ℝ)
    (A : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm (realProdBasis b b)
        (finiteOperatorColumns (realProdBasis b b) (realPhaseConjugate b u A)) p ≤
      hsSchattenNorm (realProdBasis b b) (finiteOperatorColumns (realProdBasis b b) A) p := by
  let d := realProdBasis b b
  have heq : finiteOperatorColumns d (realPhaseConjugate b u A) =
      hsLeftComposition (realPhaseRotation b u)
        (hsRightComposition d d d (realPhaseRotation b (fun i => -u i))
          (finiteOperatorColumns d A)) := by
    apply hilbertSchmidtOperator_injective d
    rw [hilbertSchmidtOperator_finiteOperatorColumns, hilbertSchmidtOperator_leftComposition,
      hilbertSchmidtOperator_rightComposition, hilbertSchmidtOperator_finiteOperatorColumns]
    rfl
  rw [heq]
  calc
    _ ≤ ‖realPhaseRotation b u‖ * hsSchattenNorm d (finiteOperatorColumns d A) p *
        ‖realPhaseRotation b (fun i => -u i)‖ :=
      hsSchattenNorm_twoSidedComposition_le d d d _ _ _ hp
    _ ≤ 1 * hsSchattenNorm d (finiteOperatorColumns d A) p * 1 := by
      have hs := hsSchattenNorm_nonneg d (finiteOperatorColumns d A) p
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (realPhaseRotation_norm_le b u) hs)
        (realPhaseRotation_norm_le b (fun i => -u i))
        (norm_nonneg (realPhaseRotation b (fun i => -u i))) (by simpa only [one_mul] using hs)
    _ = _ := by ring

/-- The reverse contraction gives genuine phase invariance of the actual
finite Schatten quantity. -/
theorem realPhaseConjugate_schatten_eq (b : HilbertBasis ι ℝ H) (u : ι → ℝ)
    (A : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm (realProdBasis b b)
        (finiteOperatorColumns (realProdBasis b b) (realPhaseConjugate b u A)) p =
      hsSchattenNorm (realProdBasis b b) (finiteOperatorColumns (realProdBasis b b) A) p := by
  apply le_antisymm (realPhaseConjugate_schatten_le b u A hp)
  simpa only [realPhaseConjugate_neg] using
    realPhaseConjugate_schatten_le b (fun i => -u i) (realPhaseConjugate b u A) hp

omit [Fintype ι] in
/-- Averaging the actual inverse conjugation recovers the operator exactly.
No measurability of the phase family is needed because the integrand is
proved pointwise equal to the constant operator. -/
theorem integral_realPhaseConjugate_recover {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : HilbertBasis ι ℝ H)
    (u : Ω → ι → ℝ) (A : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) :
    (∫ ω, realPhaseConjugate b (fun i => -u ω i) (realPhaseConjugate b (u ω) A) ∂μ) = A := by
  simp only [realPhaseConjugate_neg, integral_const]
  simp

/-- The normalized two-dimensional parameter square for the Fourier estimate. -/
def fourierSquareMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))

instance fourierSquareProbability : IsProbabilityMeasure fourierSquareMeasure where
  measure_univ := by
    rw [fourierSquareMeasure, ← univ_prod_univ, Measure.prod_prod]
    simp [Real.volume_Icc]

/-- The actual two-dimensional integer phase, with the standard torus period. -/
def integerPlanePhase (k : ℤ × ℤ) (θ : ℝ × ℝ) : ℝ :=
  2 * Real.pi * ((k.1 : ℝ) * θ.1 + (k.2 : ℝ) * θ.2)

theorem integerPlanePhase_sub (k l : ℤ × ℤ) (θ : ℝ × ℝ) :
    integerPlanePhase (k - l) θ = integerPlanePhase k θ - integerPlanePhase l θ := by
  simp only [integerPlanePhase, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

variable {ν : Type uν} [Fintype ν]

/-- Actual finite matrix-valued real trigonometric polynomial. Frequencies may
repeat and the coefficient index may be empty. -/
def realMatrixTrigPolynomial (k : ν → ℤ × ℤ) (C S : ν → H →L[ℝ] H)
    (θ : ℝ × ℝ) : H →L[ℝ] H :=
  ∑ j, (Real.cos (integerPlanePhase (k j) θ) • C j +
    Real.sin (integerPlanePhase (k j) θ) • S j)

/-- Actual coefficientwise Fourier action of the one fixed symbol constructed
in `LipschitzEvenSymbol`. It is not a Schur-multiplier certificate. -/
def fixedEvenFourierPolynomial (k : ν → ℤ × ℤ) (C S : ν → H →L[ℝ] H)
    (θ : ℝ × ℝ) : H →L[ℝ] H :=
  realMatrixTrigPolynomial k
    (fun j => lipschitzEvenSymbol (k j).1 (k j).2 • C j)
    (fun j => lipschitzEvenSymbol (k j).1 (k j).2 • S j) θ

/-- The precise remaining analytic Fourier input. It asks only for the fixed
smooth even planar symbol on finite real matrix-valued trigonometric
polynomials, at dyadic Schatten exponents. The outer norm is L2 in the torus
parameter. This universal Fourier estimate remains unproved here. -/
structure FixedEvenFourierL2Bound (C : ℝ) : Prop where
  constant_nonneg : 0 ≤ C
  bound : ∀ {ν : Type uν} {ι : Type uι} [Fintype ν] [Fintype ι]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ) (X Y : ν → H →L[ℝ] H) (n : ℕ),
    (∫ θ, hsSchattenNorm b
      (finiteOperatorColumns b (fixedEvenFourierPolynomial k X Y θ)) ((2 : ℝ) ^ (n + 1)) ^ 2
        ∂fourierSquareMeasure) ≤
      (C * (2 : ℝ) ^ (n + 1)) ^ 2 *
        (∫ θ, hsSchattenNorm b
          (finiteOperatorColumns b (realMatrixTrigPolynomial k X Y θ)) ((2 : ℝ) ^ (n + 1)) ^ 2
            ∂fourierSquareMeasure)

/-- Actual real block implementation of a complex matrix `B + i C`. -/
def realComplexBlock (B C : H →L[ℝ] H) :
    WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ H H).symm.toContinuousLinearMap.comp
    ((B.comp (WithLp.fstL 2 ℝ H H) - C.comp (WithLp.sndL 2 ℝ H H)).prod
      (C.comp (WithLp.fstL 2 ℝ H H) + B.comp (WithLp.sndL 2 ℝ H H)))

omit [CompleteSpace H] in
@[simp] theorem realComplexBlock_fst (B C : H →L[ℝ] H) (z : WithLp 2 (H × H)) :
    (realComplexBlock B C z).fst = B z.fst - C z.snd := rfl

omit [CompleteSpace H] in
@[simp] theorem realComplexBlock_snd (B C : H →L[ℝ] H) (z : WithLp 2 (H × H)) :
    (realComplexBlock B C z).snd = C z.fst + B z.snd := rfl

@[simp] theorem realComplexBlock_entry_inl_inl (b : HilbertBasis ι ℝ H)
    (B C : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry (realProdBasis b b) (realComplexBlock B C) (Sum.inl i) (Sum.inl j) =
      finiteBasisEntry b B i j := by
  rw [finiteBasisEntry, realProdBasis_inl, realProdBasis_inl]
  change inner ℝ (WithLp.toLp 2 (b i, (0 : H))) (WithLp.toLp 2 (B (b j) - C 0, C (b j) + B 0)) = _
  simp only [map_zero, sub_zero, add_zero, WithLp.prod_inner_apply, inner_zero_left, add_zero]
  rfl

@[simp] theorem realComplexBlock_entry_inl_inr (b : HilbertBasis ι ℝ H)
    (B C : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry (realProdBasis b b) (realComplexBlock B C) (Sum.inl i) (Sum.inr j) =
      -finiteBasisEntry b C i j := by
  rw [finiteBasisEntry, realProdBasis_inl, realProdBasis_inr]
  change inner ℝ (WithLp.toLp 2 (b i, (0 : H))) (WithLp.toLp 2 (B 0 - C (b j), C 0 + B (b j))) = _
  simp only [map_zero, zero_sub, zero_add, WithLp.prod_inner_apply, inner_zero_left, add_zero,
    inner_neg_right]
  rfl

@[simp] theorem realComplexBlock_entry_inr_inl (b : HilbertBasis ι ℝ H)
    (B C : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry (realProdBasis b b) (realComplexBlock B C) (Sum.inr i) (Sum.inl j) =
      finiteBasisEntry b C i j := by
  rw [finiteBasisEntry, realProdBasis_inr, realProdBasis_inl]
  change inner ℝ (WithLp.toLp 2 ((0 : H), b i)) (WithLp.toLp 2 (B (b j) - C 0, C (b j) + B 0)) = _
  simp only [map_zero, sub_zero, add_zero, WithLp.prod_inner_apply, inner_zero_left, zero_add]
  rfl

@[simp] theorem realComplexBlock_entry_inr_inr (b : HilbertBasis ι ℝ H)
    (B C : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry (realProdBasis b b) (realComplexBlock B C) (Sum.inr i) (Sum.inr j) =
      finiteBasisEntry b B i j := by
  rw [finiteBasisEntry, realProdBasis_inr, realProdBasis_inr]
  change inner ℝ (WithLp.toLp 2 ((0 : H), b i)) (WithLp.toLp 2 (B 0 - C (b j), C 0 + B (b j))) = _
  simp only [map_zero, zero_sub, zero_add, WithLp.prod_inner_apply, inner_zero_left]
  rfl

/-- Diagonal doubling is the actual real form of a real operator. -/
def realDoubleOperator (A : H →L[ℝ] H) := realComplexBlock A 0

omit [Fintype ι] [CompleteSpace H] in
theorem realPhaseRotation_basis_inl (b : HilbertBasis ι ℝ H) (u : ι → ℝ) (j : ι) :
    realPhaseRotation b u (realProdInl (E := H) (b j)) =
      WithLp.toLp 2 (Real.cos (u j) • b j, Real.sin (u j) • b j) := by
  change WithLp.toLp 2 (realPhaseCos b u (b j) - realPhaseSin b u 0,
    realPhaseSin b u (b j) + realPhaseCos b u 0) = _
  simp only [map_zero, sub_zero, add_zero, realPhaseCos, realPhaseSin, hilbertDiagonal_eigen]

omit [Fintype ι] [CompleteSpace H] in
theorem realPhaseRotation_basis_inr (b : HilbertBasis ι ℝ H) (u : ι → ℝ) (j : ι) :
    realPhaseRotation b u (realProdInr (H := H) (b j)) =
      WithLp.toLp 2 (-(Real.sin (u j) • b j), Real.cos (u j) • b j) := by
  change WithLp.toLp 2 (realPhaseCos b u 0 - realPhaseSin b u (b j),
    realPhaseSin b u 0 + realPhaseCos b u (b j)) = _
  simp only [map_zero, zero_sub, zero_add, realPhaseCos, realPhaseSin, hilbertDiagonal_eigen]

theorem realProd_entry_inl_inl (b : HilbertBasis ι ℝ H)
    (B : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) (i j : ι) :
    finiteBasisEntry (realProdBasis b b) B (Sum.inl i) (Sum.inl j) =
      inner ℝ (b i) (B (realProdInl (E := H) (b j))).fst := by
  rw [finiteBasisEntry, realProdBasis_inl, realProdBasis_inl]
  simp only [realProdInl_apply, WithLp.prod_inner_apply, inner_zero_left, add_zero]
  rfl

theorem realProd_entry_inl_inr (b : HilbertBasis ι ℝ H)
    (B : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) (i j : ι) :
    finiteBasisEntry (realProdBasis b b) B (Sum.inl i) (Sum.inr j) =
      inner ℝ (b i) (B (realProdInr (H := H) (b j))).fst := by
  rw [finiteBasisEntry, realProdBasis_inl, realProdBasis_inr]
  simp only [realProdInl_apply, WithLp.prod_inner_apply, inner_zero_left, add_zero]
  rfl

theorem realProd_entry_inr_inl (b : HilbertBasis ι ℝ H)
    (B : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) (i j : ι) :
    finiteBasisEntry (realProdBasis b b) B (Sum.inr i) (Sum.inl j) =
      inner ℝ (b i) (B (realProdInl (E := H) (b j))).snd := by
  rw [finiteBasisEntry, realProdBasis_inr, realProdBasis_inl]
  simp only [realProdInr_apply, WithLp.prod_inner_apply, inner_zero_left, zero_add]
  rfl

theorem realProd_entry_inr_inr (b : HilbertBasis ι ℝ H)
    (B : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) (i j : ι) :
    finiteBasisEntry (realProdBasis b b) B (Sum.inr i) (Sum.inr j) =
      inner ℝ (b i) (B (realProdInr (H := H) (b j))).snd := by
  rw [finiteBasisEntry, realProdBasis_inr, realProdBasis_inr]
  simp only [realProdInr_apply, WithLp.prod_inner_apply, inner_zero_left, zero_add]
  rfl

/-- Phase conjugation of the actual doubled matrix has the genuine cosine
and sine difference kernels in its four real blocks. -/
theorem realPhaseConjugate_double_eq (b : HilbertBasis ι ℝ H) (u : ι → ℝ) (A : H →L[ℝ] H) :
    realPhaseConjugate b u (realDoubleOperator A) =
      realComplexBlock
        (finiteSchurOperator b (fun i j => Real.cos (u i - u j)) A)
        (finiteSchurOperator b (fun i j => Real.sin (u i - u j)) A) := by
  apply finiteBasisEntry_ext (realProdBasis b b)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp only [realComplexBlock_entry_inl_inl, realComplexBlock_entry_inl_inr,
      realComplexBlock_entry_inr_inl, realComplexBlock_entry_inr_inr, finiteSchurOperator_entry]
    simp only [realProd_entry_inl_inl, realProd_entry_inl_inr, realProd_entry_inr_inl,
      realProd_entry_inr_inr, realPhaseConjugate, ContinuousLinearMap.comp_apply,
      realPhaseRotation_fst_coefficient, realPhaseRotation_snd_coefficient,
      realPhaseRotation_basis_inl, realPhaseRotation_basis_inr, realDoubleOperator,
      realComplexBlock_fst, realComplexBlock_snd, realPhaseRotation_fst_coefficient,
      realPhaseRotation_snd_coefficient]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, _root_.zero_apply, map_smul, map_neg,
      smul_zero, neg_zero, sub_zero, zero_add, inner_smul_right, inner_neg_right, Real.cos_neg, Real.sin_neg,
      Real.cos_sub, Real.sin_sub, finiteBasisEntry]
    ring

omit [Fintype ι] [CompleteSpace H] in
@[simp] theorem phaseEntry_smul (b : HilbertBasis ι ℝ H) (r : ℝ) (A : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b (r • A) i j = r * finiteBasisEntry b A i j := by
  simp only [finiteBasisEntry, _root_.smul_apply, inner_smul_right]

omit [Fintype ι] [CompleteSpace H] in
@[simp] theorem phaseEntry_sum {J : Type*} [Fintype J] (b : HilbertBasis ι ℝ H)
    (A : J → H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b (∑ k, A k) i j = ∑ k, finiteBasisEntry b (A k) i j := by
  simp only [finiteBasisEntry, _root_.sum_apply, inner_sum]

omit [Fintype ι] [CompleteSpace H] in
@[simp] theorem phaseEntry_zero (b : HilbertBasis ι ℝ H) (i j : ι) :
    finiteBasisEntry b 0 i j = 0 := by simp [finiteBasisEntry]

/-- A genuine finite matrix unit in the original Hilbert basis. -/
def phaseMatrixUnit (b : HilbertBasis ι ℝ H) (i j : ι) : H →L[ℝ] H :=
  InnerProductSpace.rankOne ℝ (b i) (b j)

omit [Fintype ι] [CompleteSpace H] in
@[simp] theorem phaseMatrixUnit_entry [DecidableEq ι] (b : HilbertBasis ι ℝ H) (i j r s : ι) :
    finiteBasisEntry b (phaseMatrixUnit b i j) r s =
      (if r = i then 1 else 0) * (if j = s then 1 else 0) := by
  classical
  simp only [finiteBasisEntry, phaseMatrixUnit, InnerProductSpace.rankOne_apply,
    inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  ring

/-- Actual cosine coefficient of the phase polynomial. -/
def phaseCosCoefficient (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (ij : ι × ι) :
    WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
  finiteBasisEntry b A ij.1 ij.2 • realComplexBlock (phaseMatrixUnit b ij.1 ij.2) 0

/-- Actual sine coefficient of the phase polynomial. -/
def phaseSinCoefficient (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (ij : ι × ι) :
    WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
  finiteBasisEntry b A ij.1 ij.2 • realComplexBlock 0 (phaseMatrixUnit b ij.1 ij.2)

/-- The actual integer-frequency polynomial is exactly phase conjugation of
the actual doubled operator. No Fourier-identification premise is supplied. -/
theorem realMatrixTrigPolynomial_phase_eq (b : HilbertBasis ι ℝ H) (k : ι → ℤ × ℤ)
    (A : H →L[ℝ] H) (θ : ℝ × ℝ) :
    realMatrixTrigPolynomial (fun ij : ι × ι => k ij.1 - k ij.2)
      (phaseCosCoefficient b A) (phaseSinCoefficient b A) θ =
      realPhaseConjugate b (fun i => integerPlanePhase (k i) θ) (realDoubleOperator A) := by
  classical
  rw [realPhaseConjugate_double_eq]
  apply finiteBasisEntry_ext (realProdBasis b b)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp [realMatrixTrigPolynomial, phaseCosCoefficient, phaseSinCoefficient,
      finiteBasisEntry_add, Fintype.sum_prod_type, integerPlanePhase_sub, mul_ite]

/-- The Schur kernel selected by the actual integer planar grid. -/
def integerFixedEvenKernel (k : ι → ℤ × ℤ) (i j : ι) : ℝ :=
  lipschitzEvenSymbol (k i - k j).1 (k i - k j).2

/-- Fourier action on the actual phase polynomial is exactly phase
conjugation of the fixed-symbol Schur image. -/
theorem fixedEvenFourierPolynomial_phase_eq (b : HilbertBasis ι ℝ H) (k : ι → ℤ × ℤ)
    (A : H →L[ℝ] H) (θ : ℝ × ℝ) :
    fixedEvenFourierPolynomial (fun ij : ι × ι => k ij.1 - k ij.2)
      (phaseCosCoefficient b A) (phaseSinCoefficient b A) θ =
      realPhaseConjugate b (fun i => integerPlanePhase (k i) θ)
        (realDoubleOperator (finiteSchurOperator b (integerFixedEvenKernel k) A)) := by
  classical
  rw [realPhaseConjugate_double_eq]
  apply finiteBasisEntry_ext (realProdBasis b b)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp [fixedEvenFourierPolynomial, realMatrixTrigPolynomial, phaseCosCoefficient,
      phaseSinCoefficient, finiteBasisEntry_add, Fintype.sum_prod_type, integerPlanePhase_sub,
      integerFixedEvenKernel, mul_assoc, mul_comm, mul_ite, ite_mul]

private theorem phaseBlockLift_schatten_le (b : HilbertBasis ι ℝ H)
    (I : H →ₗᵢ[ℝ] WithLp 2 (H × H)) (P : WithLp 2 (H × H) →L[ℝ] H)
    (hP : ‖P‖ ≤ 1) (A : H →L[ℝ] H) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm (realProdBasis b b)
      (finiteOperatorColumns (realProdBasis b b) (I.toContinuousLinearMap.comp (A.comp P))) p ≤
        hsSchattenNorm b (finiteOperatorColumns b A) p := by
  let d := realProdBasis b b
  have heq : finiteOperatorColumns d (I.toContinuousLinearMap.comp (A.comp P)) =
      hsLeftComposition I.toContinuousLinearMap
        (hsRightComposition b d b P (finiteOperatorColumns b A)) := by
    apply hilbertSchmidtOperator_injective d
    rw [hilbertSchmidtOperator_finiteOperatorColumns, hilbertSchmidtOperator_leftComposition,
      hilbertSchmidtOperator_rightComposition, hilbertSchmidtOperator_finiteOperatorColumns]
  rw [heq]
  have hs := hsSchattenNorm_nonneg b (finiteOperatorColumns b A) p
  calc
    _ ≤ ‖I.toContinuousLinearMap‖ * hsSchattenNorm b (finiteOperatorColumns b A) p * ‖P‖ :=
      hsSchattenNorm_twoSidedComposition_le b d b P I.toContinuousLinearMap _ hp
    _ ≤ 1 * hsSchattenNorm b (finiteOperatorColumns b A) p * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right I.norm_toContinuousLinearMap_le hs) hP
        (norm_nonneg P) (by simpa only [one_mul] using hs)
    _ = _ := by ring

omit [CompleteSpace H] in
theorem realDoubleOperator_split (A : H →L[ℝ] H) :
    realDoubleOperator A =
      (realProdInl (E := H)).toContinuousLinearMap.comp (A.comp (WithLp.fstL 2 ℝ H H)) +
        (realProdInr (H := H)).toContinuousLinearMap.comp (A.comp (WithLp.sndL 2 ℝ H H)) := by
  ext z
  apply (WithLp.equiv 2 (H × H)).injective
  apply Prod.ext
  all_goals
    simp [realDoubleOperator, realComplexBlock, realProdInl, realProdInr,
      ContinuousLinearMap.comp_apply]

/-- Doubling costs at most two in the actual Schatten quantity. This follows
from actual block lifts and the triangle inequality, with no complex norm rule. -/
theorem realDoubleOperator_schatten_le (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H)
    {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm (realProdBasis b b)
      (finiteOperatorColumns (realProdBasis b b) (realDoubleOperator A)) p ≤
        2 * hsSchattenNorm b (finiteOperatorColumns b A) p := by
  rw [realDoubleOperator_split, finiteOperatorColumns_add]
  exact (hsSchattenNorm_add_le (realProdBasis b b) _ _ hp).trans
    ((add_le_add
      (phaseBlockLift_schatten_le b (realProdInl (E := H)) (WithLp.fstL 2 ℝ H H)
        realProd_fst_norm_le A hp)
      (phaseBlockLift_schatten_le b (realProdInr (H := H)) (WithLp.sndL 2 ℝ H H)
        realProd_snd_norm_le A hp)).trans_eq (by ring))

/-- Actual compression of the doubled operator recovers the original matrix,
and therefore its Schatten quantity cannot be smaller. -/
theorem schatten_le_realDoubleOperator (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H)
    {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteOperatorColumns b A) p ≤
      hsSchattenNorm (realProdBasis b b)
        (finiteOperatorColumns (realProdBasis b b) (realDoubleOperator A)) p := by
  let d := realProdBasis b b
  let c := finiteOperatorColumns d (realDoubleOperator A)
  have heq : hsCompressionColumns d b d (realProdInl (E := H)) (WithLp.fstL 2 ℝ H H) c =
      finiteOperatorColumns b A := by
    apply hilbertSchmidtOperator_injective b
    rw [hilbertSchmidtOperator_compression, hilbertSchmidtOperator_finiteOperatorColumns,
      hilbertSchmidtOperator_finiteOperatorColumns]
    ext x
    simp [realDoubleOperator, realComplexBlock, realProdInl, ContinuousLinearMap.comp_apply]
  have hc := hsSchattenNorm_compression_le d b d (realProdInl (E := H))
    (WithLp.fstL 2 ℝ H H) realProd_fst_norm_le c hp
  rwa [heq] at hc

/-- Actual integer-grid Schur transference. The only unproved hypothesis is
the explicitly named fixed-symbol Fourier L2 estimate on actual polynomials.
No finite Lipschitz Schur theorem or coefficient identification is assumed. -/
theorem integerFixedEvenSchur_dyadic_le {C : ℝ}
    (hF : FixedEvenFourierL2Bound.{uι, uι, uH} C)
    (b : HilbertBasis ι ℝ H) (k : ι → ℤ × ℤ) (n : ℕ) (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b (finiteSchurOperator b (integerFixedEvenKernel k) A))
        ((2 : ℝ) ^ (n + 1)) ≤
      (2 * C * (2 : ℝ) ^ (n + 1)) *
        hsSchattenNorm b (finiteOperatorColumns b A) ((2 : ℝ) ^ (n + 1)) := by
  let p : ℝ := (2 : ℝ) ^ (n + 1)
  have hp : 2 ≤ p := by
    dsimp only [p]
    simpa only [pow_one] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ n + 1)
  let d := realProdBasis b b
  let B := finiteSchurOperator b (integerFixedEvenKernel k) A
  have hfourier := hF.bound d (fun ij : ι × ι => k ij.1 - k ij.2)
    (phaseCosCoefficient b A) (phaseSinCoefficient b A) n
  simp only [realMatrixTrigPolynomial_phase_eq, fixedEvenFourierPolynomial_phase_eq] at hfourier
  change (∫ θ, hsSchattenNorm d
      (finiteOperatorColumns d (realPhaseConjugate b (fun i => integerPlanePhase (k i) θ)
        (realDoubleOperator B))) p ^ 2 ∂fourierSquareMeasure) ≤
    (C * p) ^ 2 * (∫ θ, hsSchattenNorm d
      (finiteOperatorColumns d (realPhaseConjugate b (fun i => integerPlanePhase (k i) θ)
        (realDoubleOperator A))) p ^ 2 ∂fourierSquareMeasure) at hfourier
  dsimp only [d] at hfourier
  simp only [realPhaseConjugate_schatten_eq b _ _ hp, integral_const,
    probReal_univ, smul_eq_mul, one_mul] at hfourier
  have hC : 0 ≤ C * p := mul_nonneg hF.constant_nonneg (by linarith)
  have hD : hsSchattenNorm d (finiteOperatorColumns d (realDoubleOperator B)) p ≤
      (C * p) * hsSchattenNorm d (finiteOperatorColumns d (realDoubleOperator A)) p := by
    have hA := hsSchattenNorm_nonneg d (finiteOperatorColumns d (realDoubleOperator A)) p
    have hB := hsSchattenNorm_nonneg d (finiteOperatorColumns d (realDoubleOperator B)) p
    nlinarith [mul_nonneg hC hA]
  calc
    _ ≤ hsSchattenNorm d (finiteOperatorColumns d (realDoubleOperator B)) p :=
      schatten_le_realDoubleOperator b B hp
    _ ≤ (C * p) * hsSchattenNorm d (finiteOperatorColumns d (realDoubleOperator A)) p := hD
    _ ≤ (C * p) * (2 * hsSchattenNorm b (finiteOperatorColumns b A) p) :=
      mul_le_mul_of_nonneg_left (realDoubleOperator_schatten_le b A hp) hC
    _ = _ := by ring

/-- The same genuine integer-grid bound on arbitrary actual finite HS columns. -/
theorem integerFixedEvenSchurColumns_dyadic_le {C : ℝ}
    (hF : FixedEvenFourierL2Bound.{uι, uι, uH} C)
    (b : HilbertBasis ι ℝ H) (k : ι → ℤ × ℤ) (n : ℕ) (c : HilbertSchmidtColumns ι H) :
    hsSchattenNorm b (finiteMatrixSchurColumns b (integerFixedEvenKernel k) c) ((2 : ℝ) ^ (n + 1)) ≤
      (2 * C * (2 : ℝ) ^ (n + 1)) * hsSchattenNorm b c ((2 : ℝ) ^ (n + 1)) := by
  have h := integerFixedEvenSchur_dyadic_le hF b k n (hilbertSchmidtOperator b c)
  rw [finiteOperatorColumns_hilbertSchmidtOperator] at h
  have heq : finiteOperatorColumns b
      (finiteSchurOperator b (integerFixedEvenKernel k) (hilbertSchmidtOperator b c)) =
        finiteMatrixSchurColumns b (integerFixedEvenKernel k) c := by
    apply hilbertSchmidtOperator_injective b
    rw [hilbertSchmidtOperator_finiteOperatorColumns]
    simp only [finiteSchurOperator, finiteOperatorColumns_hilbertSchmidtOperator]
  rwa [heq] at h

end
end KernelSeq
