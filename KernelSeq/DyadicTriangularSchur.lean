import KernelSeq.FiniteSchattenProduct

/-!
# Actual finite triangular Schur bounds at dyadic exponents

The actual Cotlar identity retains the positive equal-label block covariance.
Positive spectral-power monotonicity then gives a norm doubling step. Combined
with the proved exact dyadic product estimate, this yields the dimension-free
constant `p - 1` at every dyadic exponent `p ≥ 2`.
No triangular multiplier, Holder, or HMS certificate is a final hypothesis.
-/

namespace KernelSeq
noncomputable section

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem finiteSchatten_add_le (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteOperatorColumns b (A + B)) p ≤
      hsSchattenNorm b (finiteOperatorColumns b A) p +
        hsSchattenNorm b (finiteOperatorColumns b B) p := by
  rw [finiteOperatorColumns_add]
  exact hsSchattenNorm_add_le b _ _ hp

private theorem finiteSchatten_neg_eq (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteOperatorColumns b (-A)) p =
      hsSchattenNorm b (finiteOperatorColumns b A) p := by
  rw [finiteOperatorColumns_neg]
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
    hsSchattenNorm_smul b (finiteOperatorColumns b A) (-1) hp

private theorem triangularSchur_doubling_of_bounds
    (b : HilbertBasis ι ℝ H) (x : ι → ℝ) {p T : ℝ} (hp : 2 ≤ p) (hT : 0 ≤ T)
    (hbound : ∀ A : H →L[ℝ] H,
      hsSchattenNorm b (finiteOperatorColumns b (triangularSchur b x A)) p ≤
        T * hsSchattenNorm b (finiteOperatorColumns b A) p)
    (hproduct : ∀ A B : H →L[ℝ] H,
      hsSchattenNorm b (finiteOperatorColumns b (A * B)) p ≤
        hsSchattenNorm b (finiteOperatorColumns b A) (2 * p) *
          hsSchattenNorm b (finiteOperatorColumns b B) (2 * p))
    (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b (triangularSchur b x A)) (2 * p) ≤
      (2 * T + 1) * hsSchattenNorm b (finiteOperatorColumns b A) (2 * p) := by
  letI : FiniteDimensional ℝ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  let Y := triangularSchur b x A
  let C := Y.adjoint * Y
  let P := A.adjoint * A
  let R := (diagonalBlockSchur b x A).adjoint * diagonalBlockSchur b x A
  let U := -(Y.adjoint * A) + A.adjoint * Y
  let Q := P - triangularSchur b x U
  let r := hsSchattenNorm b (finiteOperatorColumns b Y) (2 * p)
  let s := hsSchattenNorm b (finiteOperatorColumns b A) (2 * p)
  have hr : 0 ≤ r := hsSchattenNorm_nonneg b _ _
  have hs : 0 ≤ s := hsSchattenNorm_nonneg b _ _
  have hp0 : 0 < p := by linarith
  have hp2 : 2 ≤ 2 * p := by linarith
  have hcot : -C = triangularSchur b x U - P + R := by
    simpa only [C, P, R, U, Y, triangularSchur_adjoint, diagonalBlockSchur_adjoint,
      neg_mul] using triangularSchur_cotlar b x A.adjoint A
  have hgram : C = P - R - triangularSchur b x U := by
    calc
      C = -(-C) := by simp
      _ = -(triangularSchur b x U - P + R) := congrArg Neg.neg hcot
      _ = _ := by abel
  have hQeq : Q = C + R := by dsimp only [Q]; rw [hgram]; abel
  have hC : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self Y
  have hP : P.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hR : R.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self (diagonalBlockSchur b x A)
  have hQ : Q.IsPositive := by rw [hQeq]; exact hC.add hR
  have hCQ : C ≤ Q := by
    apply (ContinuousLinearMap.le_def _ _).mpr
    have heq : Q - C = R := by rw [hQeq]; abel
    rw [heq]
    exact hR
  have hCnorm : hsSchattenNorm b (finiteOperatorColumns b C) p = r ^ 2 :=
    finiteSchatten_covariance_eq b Y hp0
  have hPnorm : hsSchattenNorm b (finiteOperatorColumns b P) p = s ^ 2 :=
    finiteSchatten_covariance_eq b A hp0
  have hprod₁ := hproduct Y.adjoint A
  rw [finiteSchatten_adjoint_eq b Y hp2] at hprod₁
  have hprod₂ := hproduct A.adjoint Y
  rw [finiteSchatten_adjoint_eq b A hp2] at hprod₂
  have hUnorm : hsSchattenNorm b (finiteOperatorColumns b U) p ≤ 2 * r * s := by
    calc
      _ ≤ hsSchattenNorm b (finiteOperatorColumns b (-(Y.adjoint * A))) p +
          hsSchattenNorm b (finiteOperatorColumns b (A.adjoint * Y)) p :=
        finiteSchatten_add_le b _ _ hp
      _ = hsSchattenNorm b (finiteOperatorColumns b (Y.adjoint * A)) p +
          hsSchattenNorm b (finiteOperatorColumns b (A.adjoint * Y)) p := by
        rw [finiteSchatten_neg_eq b _ hp]
      _ ≤ r * s + s * r := add_le_add hprod₁ hprod₂
      _ = _ := by ring
  have hHU : hsSchattenNorm b (finiteOperatorColumns b (triangularSchur b x U)) p ≤
      T * (2 * r * s) := (hbound U).trans (mul_le_mul_of_nonneg_left hUnorm hT)
  have hQnorm : hsSchattenNorm b (finiteOperatorColumns b Q) p ≤
      hsSchattenNorm b (finiteOperatorColumns b P) p +
        hsSchattenNorm b (finiteOperatorColumns b (triangularSchur b x U)) p := by
    change hsSchattenNorm b (finiteOperatorColumns b (P - triangularSchur b x U)) p ≤ _
    rw [sub_eq_add_neg]
    exact (finiteSchatten_add_le b _ _ hp).trans_eq (by rw [finiteSchatten_neg_eq b _ hp])
  have hmono := finiteSchatten_positive_mono b C Q hC hQ hCQ (by linarith : 1 ≤ p)
  have hpoly : r ^ 2 ≤ s ^ 2 + 2 * T * r * s := by
    have hbase := hmono.trans hQnorm
    rw [hCnorm, hPnorm] at hbase
    nlinarith
  change r ≤ (2 * T + 1) * s
  by_contra hnot
  have hgt : (2 * T + 1) * s < r := lt_of_not_ge hnot
  have hr0 : 0 < r := by nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * T + 1) hs]
  have hstrict : 0 < (r - (2 * T + 1) * s) * (r + s) :=
    mul_pos (sub_pos.mpr hgt) (by linarith)
  nlinarith [mul_nonneg hT (sq_nonneg s)]

/-- The actual finite sign Schur multiplier satisfies the dimension-free
bound `p - 1` for every dyadic exponent `p = 2^(m+1)`. Scalar labels may repeat,
and the basis index may be empty. All product bounds are proved upstream. -/
theorem triangularSchur_dyadic_le (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (m : ℕ) (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b (triangularSchur b x A)) ((2 : ℝ) ^ (m + 1)) ≤
      ((2 : ℝ) ^ (m + 1) - 1) * hsSchattenNorm b (finiteOperatorColumns b A) ((2 : ℝ) ^ (m + 1)) := by
  letI : FiniteDimensional ℝ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  induction m generalizing A with
  | zero =>
    simpa only [Nat.zero_add, pow_one, hsSchattenNorm_two,
      show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using triangularSchur_hs_norm_le b x A
  | succ m ih =>
    let p : ℝ := (2 : ℝ) ^ (m + 1)
    have hp : 2 ≤ p := by
      dsimp only [p]
      simpa only [pow_one] using
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 1)
    have hbound : ∀ B : H →L[ℝ] H,
        hsSchattenNorm b (finiteOperatorColumns b (triangularSchur b x B)) p ≤
          (p - 1) * hsSchattenNorm b (finiteOperatorColumns b B) p := fun B => ih B
    have hproduct : ∀ B C : H →L[ℝ] H,
        hsSchattenNorm b (finiteOperatorColumns b (B * C)) p ≤
          hsSchattenNorm b (finiteOperatorColumns b B) (2 * p) *
            hsSchattenNorm b (finiteOperatorColumns b C) (2 * p) :=
      fun B C => finiteSchatten_mul_le_dyadic b B C m
    have hd := triangularSchur_doubling_of_bounds b x hp (by linarith) hbound hproduct A
    have heq : (2 : ℝ) ^ (m + 1 + 1) = 2 * p := by dsimp only [p]; rw [pow_succ']
    change hsSchattenNorm b (finiteOperatorColumns b (triangularSchur b x A)) ((2 : ℝ) ^ (m + 1 + 1)) ≤
      ((2 : ℝ) ^ (m + 1 + 1) - 1) * hsSchattenNorm b (finiteOperatorColumns b A) ((2 : ℝ) ^ (m + 1 + 1))
    rw [heq]
    convert hd using 1; ring

/-- The same dyadic estimate on arbitrary actual finite HS columns. No
operator-reconstruction premise or multiplier certificate is needed. -/
theorem triangularSchurHS_dyadic_le (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (m : ℕ) (c : HilbertSchmidtColumns ι H) :
    hsSchattenNorm b (triangularSchurHS b x c) ((2 : ℝ) ^ (m + 1)) ≤
      ((2 : ℝ) ^ (m + 1) - 1) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  have h := triangularSchur_dyadic_le b x m (hilbertSchmidtOperator b c)
  rw [finiteOperatorColumns_triangularSchur, finiteOperatorColumns_hilbertSchmidtOperator] at h
  exact h

end
end KernelSeq
