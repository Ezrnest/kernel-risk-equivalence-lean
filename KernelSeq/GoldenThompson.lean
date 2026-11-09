import KernelSeq.TraceProductBounds
import KernelSeq.LieProductFormula

/-!
# The finite real Golden--Thompson inequality

The dyadic comparison is proved by Golden's strong-induction argument: cyclic
trace identities, actual trace Cauchy--Schwarz, and previously proved lower
dyadic comparisons. No trace-power, Holder, or Golden--Thompson certificate is
assumed. The final limit uses the actual Banach-algebra Lie product formula.

Reference: S. Golden, *Lower Bounds for the Helmholtz Function*, Physical Review
137 (1965), B1127--B1128, doi:10.1103/PhysRev.137.B1127.
-/

namespace KernelSeq

noncomputable section

open Filter Topology

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem trace_product_pow_cycle (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (n : ℕ) :
    basisTrace b ((A * B) ^ n) = basisTrace b ((B * A) ^ n) := by
  cases n with
  | zero => rfl
  | succ n =>
    calc
      _ = basisTrace b (((A * B) ^ n * A) * B) := by rw [pow_succ, mul_assoc]
      _ = basisTrace b (B * ((A * B) ^ n * A)) := finiteBasisTrace_mul_comm b _ _
      _ = _ := by congr 1; rw [mul_pow_mul]; simp only [pow_succ', mul_assoc]

omit [CompleteSpace H] in
private theorem trace_four_square_pow (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (n : ℕ) :
    basisTrace b ((A ^ 2 * B ^ 2) ^ n) =
      basisTrace b (((A * B) * (B * A)) ^ n) := by
  simpa only [pow_two, mul_assoc] using
    trace_product_pow_cycle b A (A * B * B) n

private theorem trace_selfadj_product_le_of_equal_square_trace
    (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (heq : basisTrace b (A ^ 2) = basisTrace b (B ^ 2)) :
    basisTrace b (A * B) ≤ basisTrace b (A ^ 2) := by
  have h := (le_abs_self (basisTrace b (A * B))).trans
    (finiteBasisTrace_mul_abs_le_hs b A B)
  have hAn := finiteOperatorColumns_norm_sq_trace b A
  have hBn := finiteOperatorColumns_norm_sq_trace b B
  rw [hA.adjoint_eq, ← pow_two] at hAn
  rw [hB.adjoint_eq, ← pow_two, ← heq] at hBn
  nlinarith [sq_nonneg (‖finiteOperatorColumns b A‖ - ‖finiteOperatorColumns b B‖)]

omit [Fintype ι] in
private theorem trace_dyadic_iterate (b : HilbertBasis ι ℝ H) (m : ℕ)
    (h : ∀ k < m, ∀ A B : H →L[ℝ] H,
      IsSelfAdjoint A → IsSelfAdjoint B →
      basisTrace b ((A * B) ^ (2 ^ (k + 1))) ≤
        basisTrace b ((A ^ 2 * B ^ 2) ^ (2 ^ k)))
    (n : ℕ) (hn : n ≤ m) (A B : H →L[ℝ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    basisTrace b ((A * B) ^ (2 ^ n)) ≤
      basisTrace b (A ^ (2 ^ n) * B ^ (2 ^ n)) := by
  induction n generalizing A B with
  | zero => simp
  | succ n ih =>
    have hn' : n < m := by omega
    calc
      _ ≤ basisTrace b ((A ^ 2 * B ^ 2) ^ (2 ^ n)) := h n hn' A B hA hB
      _ ≤ basisTrace b ((A ^ 2) ^ (2 ^ n) * (B ^ 2) ^ (2 ^ n)) :=
        ih (by omega) (A ^ 2) (B ^ 2) (hA.pow _) (hB.pow _)
      _ = _ := by
        have hp (C : H →L[ℝ] H) : (C ^ 2) ^ (2 ^ n) = C ^ (2 ^ (n + 1)) := by
          rw [← pow_mul, ← pow_succ' 2 n]
        rw [hp, hp]

private theorem trace_dyadic_equal_moments (b : HilbertBasis ι ℝ H) (m : ℕ)
    (h : ∀ k < m, ∀ A B : H →L[ℝ] H,
      IsSelfAdjoint A → IsSelfAdjoint B →
      basisTrace b ((A * B) ^ (2 ^ (k + 1))) ≤
        basisTrace b ((A ^ 2 * B ^ 2) ^ (2 ^ k)))
    (n : ℕ) (hn : n ≤ m) (A B : H →L[ℝ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (heq : ∀ N : ℕ, basisTrace b (A ^ N) = basisTrace b (B ^ N)) :
    basisTrace b ((A * B) ^ (2 ^ n)) ≤
      basisTrace b (A ^ (2 ^ (n + 1))) := by
  refine (trace_dyadic_iterate b m h n hn A B hA hB).trans ?_
  have heq' : basisTrace b ((A ^ (2 ^ n)) ^ 2) =
      basisTrace b ((B ^ (2 ^ n)) ^ 2) := by
    simpa only [← pow_mul] using heq (2 ^ n * 2)
  have hs := trace_selfadj_product_le_of_equal_square_trace b
    (A ^ (2 ^ n)) (B ^ (2 ^ n)) (hA.pow _) (hB.pow _) heq'
  have hp : (A ^ (2 ^ n)) ^ 2 = A ^ (2 ^ (n + 1)) := by
    rw [← pow_mul, ← pow_succ 2 n]
  rwa [hp] at hs

private def goldenAlpha (X : H →L[ℝ] H) (r : ℕ) : H →L[ℝ] H :=
  X ^ (2 ^ r) * X.adjoint ^ (2 ^ r)

private def goldenBeta (X : H →L[ℝ] H) (r : ℕ) : H →L[ℝ] H :=
  X.adjoint ^ (2 ^ r) * X ^ (2 ^ r)

private theorem goldenAlpha_selfadj (X : H →L[ℝ] H) (r : ℕ) :
    IsSelfAdjoint (goldenAlpha X r) := by
  change star (goldenAlpha X r) = goldenAlpha X r
  simp only [goldenAlpha, star_mul, star_pow, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint]

private theorem goldenBeta_selfadj (X : H →L[ℝ] H) (r : ℕ) :
    IsSelfAdjoint (goldenBeta X r) := by
  change star (goldenBeta X r) = goldenBeta X r
  simp only [goldenBeta, star_mul, star_pow, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint]

private theorem goldenAlphaBeta_moments (b : HilbertBasis ι ℝ H)
    (X : H →L[ℝ] H) (r N : ℕ) :
    basisTrace b ((goldenAlpha X r) ^ N) = basisTrace b ((goldenBeta X r) ^ N) :=
  trace_product_pow_cycle b _ _ N

private theorem goldenAlpha_succ_trace (b : HilbertBasis ι ℝ H)
    (X : H →L[ℝ] H) (r N : ℕ) :
    basisTrace b ((goldenAlpha X (r + 1)) ^ N) =
      basisTrace b ((goldenAlpha X r * goldenBeta X r) ^ N) := by
  dsimp only [goldenAlpha, goldenBeta]
  rw [pow_succ, pow_mul, pow_mul]
  exact trace_four_square_pow b _ _ N

private theorem goldenAlpha_descent (b : HilbertBasis ι ℝ H) (m : ℕ)
    (h : ∀ k < m, ∀ A B : H →L[ℝ] H,
      IsSelfAdjoint A → IsSelfAdjoint B →
      basisTrace b ((A * B) ^ (2 ^ (k + 1))) ≤
        basisTrace b ((A ^ 2 * B ^ 2) ^ (2 ^ k)))
    (X : H →L[ℝ] H) (r s : ℕ) (hrs : r + s ≤ m) :
    basisTrace b ((goldenAlpha X r) ^ (2 ^ s)) ≤
      basisTrace b ((goldenAlpha X 0) ^ (2 ^ (r + s))) := by
  induction r generalizing s with
  | zero => simp
  | succ r ih =>
    rw [goldenAlpha_succ_trace]
    have hs : s ≤ m := by omega
    have ht := trace_dyadic_equal_moments b m h s hs
      (goldenAlpha X r) (goldenBeta X r)
      (goldenAlpha_selfadj X r) (goldenBeta_selfadj X r)
      (goldenAlphaBeta_moments b X r)
    have hi := ih (s + 1) (by omega)
    exact ht.trans (by simpa only [Nat.succ_add, Nat.add_succ] using hi)

/-- Golden's actual trace comparison at every dyadic depth. The strong
induction uses only trace cyclicity and genuine finite trace Cauchy--Schwarz.
The inputs need only be selfadjoint, and need not commute or be positive. -/
theorem finiteBasisTrace_dyadic_product_le (b : HilbertBasis ι ℝ H) (m : ℕ)
    (A B : H →L[ℝ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    basisTrace b ((A * B) ^ (2 ^ (m + 1))) ≤
      basisTrace b ((A ^ 2 * B ^ 2) ^ (2 ^ m)) := by
  induction m using Nat.strong_induction_on generalizing A B with
  | h m ih =>
    let X := A * B
    have hs := finiteBasisTrace_square_le_adjoint_square b (X ^ (2 ^ m))
    have hpow : (X ^ (2 ^ m)) ^ 2 = X ^ (2 ^ (m + 1)) := by
      rw [← pow_mul, ← pow_succ 2 m]
    have hadj : (X ^ (2 ^ m)).adjoint = X.adjoint ^ (2 ^ m) := by
      change star (X ^ (2 ^ m)) = star X ^ (2 ^ m)
      exact star_pow _ _
    rw [hpow, hadj] at hs
    have hstart : basisTrace b (X ^ (2 ^ (m + 1))) ≤ basisTrace b (goldenAlpha X m) := by
      exact hs.trans_eq (trace_product_pow_cycle b _ _ 1 |>.symm.trans (by simp [goldenAlpha]))
    have hd := goldenAlpha_descent b m ih X m 0 (by omega)
    have hend : basisTrace b ((goldenAlpha X 0) ^ (2 ^ m)) =
        basisTrace b ((A ^ 2 * B ^ 2) ^ (2 ^ m)) := by
      have hX : X.adjoint = B * A := by
        change star (A * B) = B * A
        rw [star_mul, hA.star_eq, hB.star_eq]
      simp only [goldenAlpha, pow_zero, pow_one, hX]
      change basisTrace b (((A * B) * (B * A)) ^ (2 ^ m)) = _
      exact (trace_four_square_pow b A B (2 ^ m)).symm
    have hd' : basisTrace b (goldenAlpha X m) ≤
        basisTrace b ((goldenAlpha X 0) ^ (2 ^ m)) := by
      simpa only [pow_zero, pow_one, Nat.add_zero] using hd
    exact hstart.trans (hd'.trans_eq hend)

/-- Iterating the proved dyadic comparison gives the full finite product
bound at each power of two. -/
theorem finiteBasisTrace_dyadic_product_le_powers (b : HilbertBasis ι ℝ H) (n : ℕ)
    (A B : H →L[ℝ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    basisTrace b ((A * B) ^ (2 ^ n)) ≤
      basisTrace b (A ^ (2 ^ n) * B ^ (2 ^ n)) := by
  exact trace_dyadic_iterate b n
    (fun k _ C D hC hD => finiteBasisTrace_dyadic_product_le b k C D hC hD)
    n le_rfl A B hA hB

/-- The actual exponential normalization at any positive integer scale. -/
theorem operator_exp_inv_nsmul_pow (X : H →L[ℝ] H) (n : ℕ) (hn : 0 < n) :
    NormedSpace.exp ((n : ℝ)⁻¹ • X) ^ n = NormedSpace.exp X := by
  simpa only [lieExactStep, add_zero] using lieExactStep_pow X 0 hn

/-- The entire dyadic exponential approximation is bounded by the actual
product of full exponentials. This is proved at every finite depth. -/
theorem finiteBasisTrace_exp_dyadic_product_le (b : HilbertBasis ι ℝ H) (n : ℕ)
    (A B : H →L[ℝ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    basisTrace b ((NormedSpace.exp (((2 ^ n : ℕ) : ℝ)⁻¹ • A) *
      NormedSpace.exp (((2 ^ n : ℕ) : ℝ)⁻¹ • B)) ^ (2 ^ n)) ≤
      basisTrace b (NormedSpace.exp A * NormedSpace.exp B) := by
  have h := finiteBasisTrace_dyadic_product_le_powers b n
    (NormedSpace.exp (((2 ^ n : ℕ) : ℝ)⁻¹ • A))
    (NormedSpace.exp (((2 ^ n : ℕ) : ℝ)⁻¹ • B))
    (((IsSelfAdjoint.all _).smul hA).exp) (((IsSelfAdjoint.all _).smul hB).exp)
  rw [operator_exp_inv_nsmul_pow A _ (pow_pos (by norm_num) _),
    operator_exp_inv_nsmul_pow B _ (pow_pos (by norm_num) _)] at h
  exact h

/-- The genuine finite real Hilbert-space Golden--Thompson inequality.
No positivity, commutation, trace-power, or concentration assumption is made:
only actual selfadjointness is required. -/
theorem finiteBasisTrace_exp_add_le (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    basisTrace b (NormedSpace.exp (A + B)) ≤
      basisTrace b (NormedSpace.exp A * NormedSpace.exp B) := by
  have hp : Tendsto (fun n : ℕ => 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have ht := (lie_trotter_product_formula A B).comp hp
  have htr := ((finiteBasisTraceCLM b).continuous.tendsto
    (NormedSpace.exp (A + B))).comp ht
  have hb : ∀ n : ℕ,
      finiteBasisTraceCLM b
        ((NormedSpace.exp (((2 ^ n : ℕ) : ℝ)⁻¹ • A) *
          NormedSpace.exp (((2 ^ n : ℕ) : ℝ)⁻¹ • B)) ^ (2 ^ n)) ≤
        basisTrace b (NormedSpace.exp A * NormedSpace.exp B) := by
    intro n
    rw [finiteBasisTraceCLM_apply]
    exact finiteBasisTrace_exp_dyadic_product_le b n A B hA hB
  simpa only [finiteBasisTraceCLM_apply] using
    le_of_tendsto htr (Eventually.of_forall hb)

end
end KernelSeq
