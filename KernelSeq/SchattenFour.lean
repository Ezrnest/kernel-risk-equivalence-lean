import KernelSeq.TriangularSchur
import KernelSeq.FiniteOperatorTrace

/-!
# Genuine Schatten-four, HS and trace identities

The fourth singular-value power sum is identified with the actual HS energy
of `A* A`, using the constructed singular Hilbert basis and basis-invariant
column energy. This step holds for arbitrary real HS operators. For actual
finite operators, full trace cyclicity and the genuine HS inner-product
Cauchy--Schwarz inequality then prove the `S4 × S4 → S2` product estimate.
The actual Cotlar identity and positive-product trace additionally give a
dimension-free `S4` sign-multiplier bound with constant three.
No singular-value identification, product Hölder bound, or trace identity is
an input certificate. Empty finite bases and zero operators are included.
-/

open scoped BigOperators

namespace KernelSeq

noncomputable section

variable {ι H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual squared covariance has its genuine squared-eigenvalue HS
energy. The singular basis and its eigenvalue identity are already constructed. -/
theorem hsCovarianceColumns_norm_sq (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    ‖hsLeftComposition (hilbertSchmidtOperator b c).adjoint c‖ ^ 2 =
      ∑' i : HSSingularIndex b c, i.1 ^ 2 := by
  let d := hsLeftComposition (hilbertSchmidtOperator b c).adjoint c
  have he (i : HSSingularIndex b c) :
      ‖hilbertSchmidtOperator b d (hsSingularBasis b c i)‖ ^ 2 = i.1 ^ 2 := by
    rw [hilbertSchmidtOperator_leftComposition]
    change ‖hsSingularCovariance b c (hsSingularBasis b c i)‖ ^ 2 = _
    have heigen : hsSingularCovariance b c (hsSingularBasis b c i) = i.1 • hsSingularBasis b c i :=
      compactEigenbasis_eigen _ (hsSingularCovariance_isCompact b c)
        (hsSingularCovariance_isPositive b c).isSymmetric i
    rw [heigen]
    simp only [norm_smul, Real.norm_eq_abs, (hsSingularBasis b c).orthonormal.norm_eq_one,
      mul_one, sq_abs]
  have h := (hilbertSchmidtOperator_basis_energy b (hsSingularBasis b c) d).2
  simpa only [he] using h.symm

/-- The fourth power of the genuine Schatten-four quantity is the squared
HS norm of the actual covariance columns. -/
theorem hsSchattenNorm_four_pow (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b c 4 ^ 4 = ‖hsLeftComposition (hilbertSchmidtOperator b c).adjoint c‖ ^ 2 := by
  have h := hsSchattenNorm_rpow b c (by norm_num : 0 < (4 : ℝ))
  rw [hsCovarianceColumns_norm_sq]
  norm_num at h
  exact h

/-- The genuine `S4` square equals the actual covariance HS norm, without a
finite-dimensional restriction on either Hilbert space. -/
theorem hsCovarianceColumns_norm_eq_four_sq (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    ‖hsLeftComposition (hilbertSchmidtOperator b c).adjoint c‖ = hsSchattenNorm b c 4 ^ 2 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (sq_nonneg _)).mp
  rw [← hsSchattenNorm_four_pow]
  ring

section Finite

variable [Fintype ι]

/-- The covariance of an actual finite operator has its genuine Schatten-four
square as HS norm. All column membership is constructed from the finite basis. -/
theorem finiteOperatorColumns_adjoint_mul_self_norm (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    ‖finiteOperatorColumns b (A.adjoint * A)‖ = hsSchattenNorm b (finiteOperatorColumns b A) 4 ^ 2 := by
  have hd : finiteOperatorColumns b (A.adjoint * A) = hsLeftComposition A.adjoint (finiteOperatorColumns b A) := by
    ext j
    simp only [finiteOperatorColumns_apply, hsLeftComposition_apply, mul_apply_eq_comp]
  rw [hd]
  simpa only [hilbertSchmidtOperator_finiteOperatorColumns] using
    hsCovarianceColumns_norm_eq_four_sq b (finiteOperatorColumns b A)

/-- The actual adjoint's finite columns have the same Schatten-four value. -/
theorem finiteOperatorColumns_adjoint_four (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b A.adjoint) 4 =
      hsSchattenNorm b (finiteOperatorColumns b A) 4 := by
  apply hsSchattenNorm_adjoint_reconstruction_eq b b (finiteOperatorColumns b A)
  · rw [hilbertSchmidtOperator_finiteOperatorColumns, hilbertSchmidtOperator_finiteOperatorColumns]
  · norm_num

/-- The second covariance `A A*` has the same genuine `S4` square as HS norm. -/
theorem finiteOperatorColumns_self_mul_adjoint_norm (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    ‖finiteOperatorColumns b (A * A.adjoint)‖ = hsSchattenNorm b (finiteOperatorColumns b A) 4 ^ 2 := by
  simpa only [ContinuousLinearMap.adjoint_adjoint, finiteOperatorColumns_adjoint_four] using
    finiteOperatorColumns_adjoint_mul_self_norm b A.adjoint

/-- The finite trace of an actual HS product is its actual column inner product. -/
theorem finiteOperatorColumns_trace_inner (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) :
    basisTrace b (A.adjoint * B) = inner ℝ (finiteOperatorColumns b A) (finiteOperatorColumns b B) := by
  simpa only [hilbertSchmidtOperator_finiteOperatorColumns, ← ContinuousLinearMap.mul_def] using
    (hilbertSchmidtProduct_trace b (finiteOperatorColumns b A) (finiteOperatorColumns b B)).2

/-- Exact finite trace/HS norm identity for arbitrary actual operators. -/
theorem finiteOperatorColumns_norm_sq_trace (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    ‖finiteOperatorColumns b A‖ ^ 2 = basisTrace b (A.adjoint * A) := by
  rw [finiteOperatorColumns_trace_inner, real_inner_self_eq_norm_sq]

/-- The actual covariance is selfadjoint; no spectral assumption is needed. -/
theorem adjoint_mul_self_adjoint (A : H →L[ℝ] H) :
    (A.adjoint * A).adjoint = A.adjoint * A := by
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- The actual fourth Schatten power is the actual trace of `(A* A)^2`. -/
theorem finiteSchatten_four_pow_trace (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b A) 4 ^ 4 = basisTrace b ((A.adjoint * A) ^ 2) := by
  have h := finiteOperatorColumns_norm_sq_trace b (A.adjoint * A)
  rw [finiteOperatorColumns_adjoint_mul_self_norm, adjoint_mul_self_adjoint] at h
  calc
    _ = (hsSchattenNorm b (finiteOperatorColumns b A) 4 ^ 2) ^ 2 := by ring
    _ = _ := by simpa only [pow_two] using h

/-- The same fourth Schatten power is the actual trace of `(A A*)²`. -/
theorem finiteSchatten_four_pow_trace_self_adjoint (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b A) 4 ^ 4 = basisTrace b ((A * A.adjoint) ^ 2) := by
  simpa only [ContinuousLinearMap.adjoint_adjoint, finiteOperatorColumns_adjoint_four] using
    finiteSchatten_four_pow_trace b A.adjoint

/-- Full trace cyclicity identifies a genuine product's HS energy with the
covariance product. -/
theorem finiteOperatorColumns_mul_norm_sq_trace (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) :
    ‖finiteOperatorColumns b (A * B)‖ ^ 2 = basisTrace b ((A.adjoint * A) * (B * B.adjoint)) := by
  rw [finiteOperatorColumns_norm_sq_trace]
  have hadj : (A * B).adjoint = B.adjoint * A.adjoint := ContinuousLinearMap.adjoint_comp A B
  rw [hadj]
  calc
    _ = basisTrace b (B.adjoint * ((A.adjoint * A) * B)) := by simp only [mul_assoc]
    _ = basisTrace b (((A.adjoint * A) * B) * B.adjoint) := finiteBasisTrace_mul_comm b _ _
    _ = _ := by simp only [mul_assoc]

/-- The actual finite `S4 × S4 → S2` Hölder estimate, derived from covariance
trace cyclicity and HS Cauchy--Schwarz. No product norm bound is assumed. -/
theorem finiteOperatorColumns_mul_norm_le_four (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) :
    ‖finiteOperatorColumns b (A * B)‖ ≤
      hsSchattenNorm b (finiteOperatorColumns b A) 4 * hsSchattenNorm b (finiteOperatorColumns b B) 4 := by
  have hcs := real_inner_le_norm (finiteOperatorColumns b (A.adjoint * A))
    (finiteOperatorColumns b (B * B.adjoint))
  rw [← finiteOperatorColumns_trace_inner, adjoint_mul_self_adjoint,
    ← finiteOperatorColumns_mul_norm_sq_trace, finiteOperatorColumns_adjoint_mul_self_norm,
    finiteOperatorColumns_self_mul_adjoint_norm] at hcs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hsSchattenNorm_nonneg b _ 4) (hsSchattenNorm_nonneg b _ 4))).mp
  simpa only [mul_pow] using hcs

omit [CompleteSpace H] in
/-- Finite actual operator columns preserve addition. -/
theorem finiteOperatorColumns_add (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) :
    finiteOperatorColumns b (A + B) = finiteOperatorColumns b A + finiteOperatorColumns b B := by
  ext j
  simp only [finiteOperatorColumns_apply, add_apply, lp.coeFn_add, Pi.add_apply]

omit [CompleteSpace H] in
/-- Finite actual operator columns preserve negation. -/
theorem finiteOperatorColumns_neg (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    finiteOperatorColumns b (-A) = -finiteOperatorColumns b A := by
  ext j
  simp only [finiteOperatorColumns_apply, neg_apply, lp.coeFn_neg, Pi.neg_apply]

/-- A genuine dimension-free `S4` bound for the finite real sign multiplier.
The constant three is obtained from the actual Cotlar identity, positivity of
the block covariance trace, HS contraction, and the proved product Hölder bound.
No triangular or general HMS Schatten estimate is an input. -/
theorem triangularSchur_four_le (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b (triangularSchur b x A)) 4 ≤
      3 * hsSchattenNorm b (finiteOperatorColumns b A) 4 := by
  let Y := triangularSchur b x A
  let C := Y.adjoint * Y
  let P := A.adjoint * A
  let R := (diagonalBlockSchur b x A).adjoint * diagonalBlockSchur b x A
  let U := -(Y.adjoint * A) + A.adjoint * Y
  let a := hsSchattenNorm b (finiteOperatorColumns b A) 4
  let y := hsSchattenNorm b (finiteOperatorColumns b Y) 4
  have ha : 0 ≤ a := hsSchattenNorm_nonneg b _ 4
  have hy : 0 ≤ y := hsSchattenNorm_nonneg b _ 4
  have hcot : -C = triangularSchur b x U - P + R := by
    simpa only [C, P, R, U, Y, triangularSchur_adjoint, diagonalBlockSchur_adjoint,
      neg_mul] using triangularSchur_cotlar b x A.adjoint A
  have hgram : C = P - R - triangularSchur b x U := by
    calc
      C = -(-C) := by simp
      _ = -(triangularSchur b x U - P + R) := congrArg Neg.neg hcot
      _ = _ := by abel
  have hCpos : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self Y
  have hRpos : R.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self (diagonalBlockSchur b x A)
  have hCR : 0 ≤ basisTrace b (C * R) := finiteBasisTrace_mul_nonneg b C R hCpos hRpos
  have hCnorm : ‖finiteOperatorColumns b C‖ = y ^ 2 := finiteOperatorColumns_adjoint_mul_self_norm b Y
  have hPnorm : ‖finiteOperatorColumns b P‖ = a ^ 2 := finiteOperatorColumns_adjoint_mul_self_norm b A
  have hprod₁ := finiteOperatorColumns_mul_norm_le_four b Y.adjoint A
  rw [finiteOperatorColumns_adjoint_four] at hprod₁
  have hprod₂ := finiteOperatorColumns_mul_norm_le_four b A.adjoint Y
  rw [finiteOperatorColumns_adjoint_four] at hprod₂
  have hUnorm : ‖finiteOperatorColumns b U‖ ≤ 2 * y * a := by
    change ‖finiteOperatorColumns b (-(Y.adjoint * A) + A.adjoint * Y)‖ ≤ _
    rw [finiteOperatorColumns_add, finiteOperatorColumns_neg]
    calc
      _ ≤ ‖-finiteOperatorColumns b (Y.adjoint * A)‖ + ‖finiteOperatorColumns b (A.adjoint * Y)‖ := norm_add_le _ _
      _ = ‖finiteOperatorColumns b (Y.adjoint * A)‖ + ‖finiteOperatorColumns b (A.adjoint * Y)‖ := by rw [norm_neg]
      _ ≤ y * a + a * y := add_le_add hprod₁ hprod₂
      _ = _ := by ring
  have hHUnorm : ‖finiteOperatorColumns b (triangularSchur b x U)‖ ≤ 2 * y * a :=
    (triangularSchur_hs_norm_le b x U).trans hUnorm
  have hCP : basisTrace b (C * P) ≤ y ^ 2 * a ^ 2 := by
    have h := real_inner_le_norm (finiteOperatorColumns b C) (finiteOperatorColumns b P)
    rw [← finiteOperatorColumns_trace_inner] at h
    have hCs : C.adjoint = C := adjoint_mul_self_adjoint Y
    simpa only [hCs, hCnorm, hPnorm] using h
  have hCH : |basisTrace b (C * triangularSchur b x U)| ≤ y ^ 2 * (2 * y * a) := by
    have h := abs_real_inner_le_norm (finiteOperatorColumns b C)
      (finiteOperatorColumns b (triangularSchur b x U))
    rw [← finiteOperatorColumns_trace_inner] at h
    have hCs : C.adjoint = C := adjoint_mul_self_adjoint Y
    rw [hCs, hCnorm] at h
    exact h.trans (mul_le_mul_of_nonneg_left hHUnorm (sq_nonneg y))
  have hCC : basisTrace b (C * C) = y ^ 4 := by
    simpa only [C, pow_two] using (finiteSchatten_four_pow_trace b Y).symm
  have htrace : basisTrace b (C * C) = basisTrace b (C * P) - basisTrace b (C * R) -
      basisTrace b (C * triangularSchur b x U) := by
    have h := congrArg (fun T => basisTrace b (C * T)) hgram
    simpa only [mul_sub, ← finiteBasisTraceCLM_apply, map_sub] using h
  have hpoly : y ^ 4 ≤ y ^ 2 * a ^ 2 + y ^ 2 * (2 * y * a) := by
    rw [hCC] at htrace
    linarith [(neg_le_abs (basisTrace b (C * triangularSchur b x U))).trans hCH]
  change y ≤ 3 * a
  by_contra hnot
  have hgt : 3 * a < y := lt_of_not_ge hnot
  have hypos : 0 < y := by linarith
  have hcancel : y ^ 2 ≤ a ^ 2 + 2 * y * a := by
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hypos)).mp
    nlinarith only [hpoly]
  have hstrict : 0 < (y - 3 * a) * (y + a) := mul_pos (by linarith) (by linarith)
  nlinarith [sq_nonneg a]

/-- The same true finite `S4` sign estimate directly on arbitrary actual HS
columns, without an operator-reconstruction hypothesis. -/
theorem triangularSchurHS_four_le (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (c : HilbertSchmidtColumns ι H) :
    hsSchattenNorm b (triangularSchurHS b x c) 4 ≤ 3 * hsSchattenNorm b c 4 := by
  have h := triangularSchur_four_le b x (hilbertSchmidtOperator b c)
  rw [finiteOperatorColumns_triangularSchur, finiteOperatorColumns_hilbertSchmidtOperator] at h
  exact h

end Finite
end
end KernelSeq
