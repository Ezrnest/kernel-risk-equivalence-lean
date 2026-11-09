import KernelSeq.SchattenFour
import KernelSeq.MatrixBernsteinExp

/-!
# Actual finite trace-product bounds toward Golden--Thompson

The trace Cauchy--Schwarz inequality below concerns actual arbitrary finite
operators and actual HS columns. For selfadjoint `A,B`, the difference between
`trace(A² B²)` and `trace((A B)²)` is identified exactly with half the genuine
HS commutator energy. Two actual dyadic trace comparisons, and their half/quarter-scale
exponential specializations, are proved. No general Golden--Thompson theorem
or recursive inequality at arbitrary dyadic depths is asserted.
-/

namespace KernelSeq

noncomputable section

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Actual finite HS norm is invariant under the actual adjoint. -/
theorem finiteOperatorColumns_adjoint_norm (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    ‖finiteOperatorColumns b A.adjoint‖ = ‖finiteOperatorColumns b A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [finiteOperatorColumns_norm_sq_trace, finiteOperatorColumns_norm_sq_trace,
    ContinuousLinearMap.adjoint_adjoint, finiteBasisTrace_mul_comm b A A.adjoint]

/-- Genuine trace Cauchy--Schwarz for any two actual finite operators. -/
theorem finiteBasisTrace_mul_abs_le_hs (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) :
    |basisTrace b (A * B)| ≤ ‖finiteOperatorColumns b A‖ * ‖finiteOperatorColumns b B‖ := by
  have h := abs_real_inner_le_norm (finiteOperatorColumns b A.adjoint) (finiteOperatorColumns b B)
  rw [← finiteOperatorColumns_trace_inner, ContinuousLinearMap.adjoint_adjoint,
    finiteOperatorColumns_adjoint_norm] at h
  exact h

/-- A genuine four-factor trace estimate, with products represented by their
actual finite HS columns. -/
theorem finiteBasisTrace_four_abs_le_hs (b : HilbertBasis ι ℝ H) (A B C D : H →L[ℝ] H) :
    |basisTrace b (A * B * C * D)| ≤
      ‖finiteOperatorColumns b (A * B)‖ * ‖finiteOperatorColumns b (C * D)‖ := by
  simpa only [mul_assoc] using finiteBasisTrace_mul_abs_le_hs b (A * B) (C * D)

/-- The corresponding actual four-factor Schatten-four Hölder inequality. -/
theorem finiteBasisTrace_four_abs_le_four (b : HilbertBasis ι ℝ H) (A B C D : H →L[ℝ] H) :
    |basisTrace b (A * B * C * D)| ≤
      (hsSchattenNorm b (finiteOperatorColumns b A) 4 * hsSchattenNorm b (finiteOperatorColumns b B) 4) *
        (hsSchattenNorm b (finiteOperatorColumns b C) 4 * hsSchattenNorm b (finiteOperatorColumns b D) 4) := by
  exact (finiteBasisTrace_four_abs_le_hs b A B C D).trans
    (mul_le_mul (finiteOperatorColumns_mul_norm_le_four b A B)
      (finiteOperatorColumns_mul_norm_le_four b C D) (norm_nonneg _)
      (mul_nonneg (hsSchattenNorm_nonneg b _ 4) (hsSchattenNorm_nonneg b _ 4)))

omit [CompleteSpace H] in
/-- Exact cyclic rotation of four actual finite operator factors. -/
theorem finiteBasisTrace_four_cycle (b : HilbertBasis ι ℝ H) (A B C D : H →L[ℝ] H) :
    basisTrace b (A * B * C * D) = basisTrace b (B * C * D * A) := by
  simpa only [mul_assoc] using finiteBasisTrace_mul_comm b A (B * C * D)

/-- The exact actual commutator HS energy identity. In particular the
comparison is valid without any positivity or commutativity assumption. -/
theorem finiteBasisTrace_commutator_energy (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    2 * (basisTrace b (A ^ 2 * B ^ 2) - basisTrace b ((A * B) ^ 2)) =
      ‖finiteOperatorColumns b (A * B - B * A)‖ ^ 2 := by
  have hadj : (A * B - B * A).adjoint = B * A - A * B := by
    simp only [map_sub, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      hA.adjoint_eq, hB.adjoint_eq]
  have hexp : (B * A - A * B) * (A * B - B * A) =
      (B * A * A * B + A * B * B * A) - B * A * B * A - A * B * A * B := by
    noncomm_ring
  have h₁ : basisTrace b (B * A * A * B) = basisTrace b (A ^ 2 * B ^ 2) := by
    simpa only [pow_two, mul_assoc] using finiteBasisTrace_four_cycle b B A A B
  have h₂ : basisTrace b (A * B * B * A) = basisTrace b (A ^ 2 * B ^ 2) := by
    simpa only [pow_two, mul_assoc] using (finiteBasisTrace_mul_comm b (A * B * B) A)
  have h₃ : basisTrace b (B * A * B * A) = basisTrace b ((A * B) ^ 2) := by
    simpa only [pow_two, mul_assoc] using finiteBasisTrace_four_cycle b B A B A
  have h₄ : basisTrace b (A * B * A * B) = basisTrace b ((A * B) ^ 2) := by
    simp only [pow_two, mul_assoc]
  have h := finiteOperatorColumns_norm_sq_trace b (A * B - B * A)
  rw [hadj, hexp] at h
  simp only [← finiteBasisTraceCLM_apply, map_sub, map_add] at h
  simp only [finiteBasisTraceCLM_apply, h₁, h₂, h₃, h₄] at h
  linarith

/-- The first actual dyadic trace comparison, derived from genuine
commutator energy nonnegativity. -/
theorem finiteBasisTrace_square_product_le (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    basisTrace b ((A * B) ^ 2) ≤ basisTrace b (A ^ 2 * B ^ 2) := by
  have h := finiteBasisTrace_commutator_energy b A B hA hB
  nlinarith [sq_nonneg ‖finiteOperatorColumns b (A * B - B * A)‖]

/-- The same first comparison with absolute trace, from genuine trace CS. -/
theorem finiteBasisTrace_square_product_abs_le (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    |basisTrace b ((A * B) ^ 2)| ≤ basisTrace b (A ^ 2 * B ^ 2) := by
  have h := finiteBasisTrace_mul_abs_le_hs b (A * B) (A * B)
  rw [← pow_two, ← pow_two, finiteOperatorColumns_mul_norm_sq_trace,
    hA.adjoint_eq, hB.adjoint_eq] at h
  simpa only [pow_two] using h

/-- An exponential's true half-scale square is its full-scale exponential.
Only an operator's commutation with itself is used. -/
theorem operator_exp_half_sq (X : H →L[ℝ] H) :
    NormedSpace.exp ((1 / 2 : ℝ) • X) ^ 2 = NormedSpace.exp X := by
  letI : NormedAlgebra ℚ (H →L[ℝ] H) := .restrictScalars ℚ ℝ _
  rw [← NormedSpace.exp_nsmul]
  congr 1
  simp only [two_smul, ← add_smul]
  norm_num

/-- The first dyadic Golden--Thompson comparison for actual selfadjoint
operators. This does not assume commutation between `X` and `Y`. -/
theorem finiteBasisTrace_exp_half_product_sq_le (b : HilbertBasis ι ℝ H) (X Y : H →L[ℝ] H)
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) :
    basisTrace b ((NormedSpace.exp ((1 / 2 : ℝ) • X) * NormedSpace.exp ((1 / 2 : ℝ) • Y)) ^ 2) ≤
      basisTrace b (NormedSpace.exp X * NormedSpace.exp Y) := by
  have h := finiteBasisTrace_square_product_le b
    (NormedSpace.exp ((1 / 2 : ℝ) • X)) (NormedSpace.exp ((1 / 2 : ℝ) • Y))
    (((IsSelfAdjoint.all (1 / 2 : ℝ)).smul hX).exp)
    (((IsSelfAdjoint.all (1 / 2 : ℝ)).smul hY).exp)
  simpa only [operator_exp_half_sq] using h

/-- A genuine trace square is bounded by the actual adjoint-square trace,
even for a nonselfadjoint finite operator. -/
theorem finiteBasisTrace_square_le_adjoint_square (b : HilbertBasis ι ℝ H) (W : H →L[ℝ] H) :
    basisTrace b (W ^ 2) ≤ basisTrace b (W.adjoint * W) := by
  have h := finiteBasisTrace_mul_abs_le_hs b W W
  rw [← pow_two, ← pow_two, finiteOperatorColumns_norm_sq_trace] at h
  exact (le_abs_self _).trans h

/-- The second actual dyadic trace comparison. Two genuine trace-CS steps
suffice for fourth powers; a general recursive bound is not assumed here. -/
theorem finiteBasisTrace_fourth_product_le (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    basisTrace b ((A * B) ^ 4) ≤ basisTrace b ((A ^ 2 * B ^ 2) ^ 2) := by
  let W := (A * B) ^ 2
  let P := B * A ^ 2 * B
  let Q := A * B ^ 2 * A
  let T := basisTrace b ((A ^ 2 * B ^ 2) ^ 2)
  have hWs : W.adjoint = (B * A) ^ 2 := by
    simp only [W, pow_two, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      hA.adjoint_eq, hB.adjoint_eq]
  have hW : basisTrace b ((A * B) ^ 4) ≤ basisTrace b (W.adjoint * W) := by
    simpa only [W, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using
      finiteBasisTrace_square_le_adjoint_square b W
  have hWPQ : basisTrace b (W.adjoint * W) = basisTrace b (P * Q) := by
    rw [hWs]
    calc
      _ = basisTrace b ((B * A * B) * (A ^ 2 * (B * A * B))) := by
        apply congrArg (basisTrace b)
        dsimp only [W]
        noncomm_ring
      _ = basisTrace b ((A ^ 2 * (B * A * B)) * (B * A * B)) := finiteBasisTrace_mul_comm b _ _
      _ = basisTrace b ((A ^ 2 * B * A * B ^ 2 * A) * B) := by
        apply congrArg (basisTrace b)
        noncomm_ring
      _ = basisTrace b (B * (A ^ 2 * B * A * B ^ 2 * A)) := finiteBasisTrace_mul_comm b _ B
      _ = _ := by
        apply congrArg (basisTrace b)
        dsimp only [P, Q]
        noncomm_ring
  have hPs : P.adjoint = P := by
    simp only [P, pow_two, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      hA.adjoint_eq, hB.adjoint_eq, ContinuousLinearMap.comp_assoc]
  have hQs : Q.adjoint = Q := by
    simp only [Q, pow_two, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      hA.adjoint_eq, hB.adjoint_eq, ContinuousLinearMap.comp_assoc]
  have hPnorm : ‖finiteOperatorColumns b P‖ ^ 2 = T := by
    rw [finiteOperatorColumns_norm_sq_trace, hPs]
    calc
      _ = basisTrace b (B * (A ^ 2 * B ^ 2 * A ^ 2 * B)) := by
        apply congrArg (basisTrace b)
        dsimp only [P]
        noncomm_ring
      _ = basisTrace b ((A ^ 2 * B ^ 2 * A ^ 2 * B) * B) := finiteBasisTrace_mul_comm b _ _
      _ = T := by
        dsimp only [T]
        apply congrArg (basisTrace b)
        noncomm_ring
  have hQnorm : ‖finiteOperatorColumns b Q‖ ^ 2 = T := by
    rw [finiteOperatorColumns_norm_sq_trace, hQs]
    calc
      _ = basisTrace b ((A * B ^ 2 * A ^ 2 * B ^ 2) * A) := by
        apply congrArg (basisTrace b)
        dsimp only [Q]
        noncomm_ring
      _ = basisTrace b (A * (A * B ^ 2 * A ^ 2 * B ^ 2)) := finiteBasisTrace_mul_comm b _ _
      _ = T := by
        dsimp only [T]
        apply congrArg (basisTrace b)
        noncomm_ring
  have hPQ := (le_abs_self (basisTrace b (P * Q))).trans (finiteBasisTrace_mul_abs_le_hs b P Q)
  have hPQ' : basisTrace b (P * Q) ≤ T := by
    nlinarith [sq_nonneg (‖finiteOperatorColumns b P‖ - ‖finiteOperatorColumns b Q‖)]
  exact hW.trans (hWPQ.trans_le hPQ')

/-- The actual quarter-scale exponential square is its half-scale exponential. -/
theorem operator_exp_quarter_sq (X : H →L[ℝ] H) :
    NormedSpace.exp ((1 / 4 : ℝ) • X) ^ 2 = NormedSpace.exp ((1 / 2 : ℝ) • X) := by
  have h := operator_exp_half_sq ((1 / 2 : ℝ) • X)
  norm_num only [smul_smul] at h
  exact h

/-- The second dyadic exponential comparison, with every exponential and
operator product actual. No full recursive Golden--Thompson assertion is used. -/
theorem finiteBasisTrace_exp_quarter_product_four_le (b : HilbertBasis ι ℝ H)
    (X Y : H →L[ℝ] H) (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) :
    basisTrace b ((NormedSpace.exp ((1 / 4 : ℝ) • X) * NormedSpace.exp ((1 / 4 : ℝ) • Y)) ^ 4) ≤
      basisTrace b ((NormedSpace.exp ((1 / 2 : ℝ) • X) * NormedSpace.exp ((1 / 2 : ℝ) • Y)) ^ 2) := by
  have h := finiteBasisTrace_fourth_product_le b
    (NormedSpace.exp ((1 / 4 : ℝ) • X)) (NormedSpace.exp ((1 / 4 : ℝ) • Y))
    (((IsSelfAdjoint.all (1 / 4 : ℝ)).smul hX).exp)
    (((IsSelfAdjoint.all (1 / 4 : ℝ)).smul hY).exp)
  simpa only [operator_exp_quarter_sq] using h

/-- The first two actually proved dyadic steps combine into a finite
fourth-power exponential bound. This remains weaker than full GT. -/
theorem finiteBasisTrace_exp_quarter_product_four_le_exp_product (b : HilbertBasis ι ℝ H)
    (X Y : H →L[ℝ] H) (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) :
    basisTrace b ((NormedSpace.exp ((1 / 4 : ℝ) • X) * NormedSpace.exp ((1 / 4 : ℝ) • Y)) ^ 4) ≤
      basisTrace b (NormedSpace.exp X * NormedSpace.exp Y) :=
  (finiteBasisTrace_exp_quarter_product_four_le b X Y hX hY).trans
    (finiteBasisTrace_exp_half_product_sq_le b X Y hX hY)

end
end KernelSeq
