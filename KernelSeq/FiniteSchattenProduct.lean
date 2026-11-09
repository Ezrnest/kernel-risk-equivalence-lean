import KernelSeq.FiniteSingularApproximation
import KernelSeq.GoldenThompson
import KernelSeq.TraceProductBounds
import Mathlib.Analysis.Real.Sqrt

/-!
# Actual finite Schatten product bounds

The actual product singular-value bound, parity splitting of the actual sorted
singular series and scalar Cauchy--Schwarz prove a weak Schatten Hölder bound
with factor `2^(1/p)`. No Schatten product inequality is an assumption. The
actual covariance/Schatten identity is also proved from positive power traces.
The locally proved dyadic trace inequality further gives exact constant-one
product Hölder at every dyadic exponent at least two.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H] [Fintype ι]

/-- The actual finite Schatten power as a natural-index finite range sum. -/
theorem finiteSchatten_rpow_eq_sum_range_singularValues (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b A) p ^ p =
      ∑ n ∈ Finset.range (Module.finrank ℝ H), A.toLinearMap.singularValues n ^ p := by
  rw [finiteSchatten_rpow_eq_sum_singularValues b A hp]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => A.toLinearMap.singularValues n ^ p) (Module.finrank ℝ H)

omit [CompleteSpace H] in
/-- The scalar product power series has its actual finite support. -/
theorem finiteSingularPower_mul_summable (A B : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    Summable (fun n : ℕ => A.toLinearMap.singularValues n ^ p * B.toLinearMap.singularValues n ^ p) := by
  apply summable_of_ne_finset_zero (s := Finset.range (Module.finrank ℝ H))
  intro n hn
  rw [A.toLinearMap.singularValues_of_finrank_le (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)),
    Real.zero_rpow hp.ne', zero_mul]

/-- Scalar Cauchy--Schwarz applied to the actual sorted singular-value powers. -/
theorem finiteSingularPower_mul_tsum_le (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    (∑' n : ℕ, A.toLinearMap.singularValues n ^ p * B.toLinearMap.singularValues n ^ p) ≤
      hsSchattenNorm b (finiteOperatorColumns b A) (2 * p) ^ p *
        hsSchattenNorm b (finiteOperatorColumns b B) (2 * p) ^ p := by
  have hsum : (∑' n : ℕ, A.toLinearMap.singularValues n ^ p * B.toLinearMap.singularValues n ^ p) =
      ∑ n ∈ Finset.range (Module.finrank ℝ H), A.toLinearMap.singularValues n ^ p * B.toLinearMap.singularValues n ^ p := by
    apply tsum_eq_sum
    intro n hn
    rw [A.toLinearMap.singularValues_of_finrank_le (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)),
      Real.zero_rpow hp.ne', zero_mul]
  have hsq (T : H →L[ℝ] H) :
      (∑ n ∈ Finset.range (Module.finrank ℝ H), (T.toLinearMap.singularValues n ^ p) ^ 2) =
        hsSchattenNorm b (finiteOperatorColumns b T) (2 * p) ^ (2 * p) := by
    rw [finiteSchatten_rpow_eq_sum_range_singularValues b T (by positivity)]
    apply Finset.sum_congr rfl
    intro n _
    rw [show 2 * p = p * 2 by ring, Real.rpow_mul (T.toLinearMap.singularValues_nonneg n), Real.rpow_two]
  rw [hsum]
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range (Module.finrank ℝ H))
    (fun n => A.toLinearMap.singularValues n ^ p) (fun n => B.toLinearMap.singularValues n ^ p)
  have hsqrt (T : H →L[ℝ] H) :
      Real.sqrt (hsSchattenNorm b (finiteOperatorColumns b T) (2 * p) ^ (2 * p)) =
        hsSchattenNorm b (finiteOperatorColumns b T) (2 * p) ^ p := by
    have heq : hsSchattenNorm b (finiteOperatorColumns b T) (2 * p) ^ (2 * p) =
        (hsSchattenNorm b (finiteOperatorColumns b T) (2 * p) ^ p) ^ 2 := by
      rw [show 2 * p = p * 2 by ring, Real.rpow_mul (hsSchattenNorm_nonneg b _ _), Real.rpow_two]
    rw [heq, Real.sqrt_sq (Real.rpow_nonneg (hsSchattenNorm_nonneg b _ _) p)]
  rw [hsq A, hsq B, hsqrt A, hsqrt B] at h
  exact h

set_option maxHeartbeats 800000 in
/-- Actual parity splitting and the proved product singular-value bound give
the weak Hölder comparison at the level of genuine Schatten power sums. -/
theorem finiteSchatten_mul_rpow_le (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b (A * B)) p ^ p ≤
      2 * (hsSchattenNorm b (finiteOperatorColumns b A) (2 * p) ^ p *
        hsSchattenNorm b (finiteOperatorColumns b B) (2 * p) ^ p) := by
  have hbase := finiteSingularPower_summable (A * B) hp
  have he : Summable (fun n : ℕ => (A * B).toLinearMap.singularValues (2 * n) ^ p) := by
    simpa only [Function.comp_def] using hbase.comp_injective (by intro i j h; change 2 * i = 2 * j at h; omega : Function.Injective (fun n : ℕ => 2 * n))
  have ho : Summable (fun n : ℕ => (A * B).toLinearMap.singularValues (2 * n + 1) ^ p) := by
    simpa only [Function.comp_def] using hbase.comp_injective (by intro i j h; change 2 * i + 1 = 2 * j + 1 at h; omega : Function.Injective (fun n : ℕ => 2 * n + 1))
  have hEven (n : ℕ) : (A * B).toLinearMap.singularValues (2 * n) ^ p ≤
      A.toLinearMap.singularValues n ^ p * B.toLinearMap.singularValues n ^ p := by
    have hw : (A * B).toLinearMap.singularValues (2 * n) ≤
        A.toLinearMap.singularValues n * B.toLinearMap.singularValues n := by
      simpa only [two_mul] using finiteSingularValue_mul_le A B n n
    exact (Real.rpow_le_rpow ((A * B).toLinearMap.singularValues_nonneg _) hw hp.le).trans_eq
      (Real.mul_rpow (A.toLinearMap.singularValues_nonneg n) (B.toLinearMap.singularValues_nonneg n))
  have hOdd (n : ℕ) : (A * B).toLinearMap.singularValues (2 * n + 1) ^ p ≤
      A.toLinearMap.singularValues n ^ p * B.toLinearMap.singularValues n ^ p :=
    (Real.rpow_le_rpow ((A * B).toLinearMap.singularValues_nonneg _)
      ((A * B).toLinearMap.singularValues_antitone (by omega : 2 * n ≤ 2 * n + 1)) hp.le).trans (hEven n)
  rw [finiteSchatten_rpow_eq_tsum_singularValues b (A * B) hp, ← tsum_even_add_odd he ho,
    ← he.tsum_add ho]
  calc
    _ ≤ ∑' n : ℕ, 2 * (A.toLinearMap.singularValues n ^ p * B.toLinearMap.singularValues n ^ p) :=
      Summable.tsum_le_tsum (fun n => by linarith [hEven n, hOdd n]) (he.add ho)
        ((finiteSingularPower_mul_summable A B hp).mul_left 2)
    _ = 2 * ∑' n : ℕ, A.toLinearMap.singularValues n ^ p * B.toLinearMap.singularValues n ^ p := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (finiteSingularPower_mul_tsum_le b A B hp) (by norm_num)

/-- The genuine weak finite Schatten Hölder bound, valid for every positive
real exponent. The factor comes solely from the proved index doubling. -/
theorem finiteSchatten_mul_le (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b (A * B)) p ≤
      (2 : ℝ) ^ (1 / p) * hsSchattenNorm b (finiteOperatorColumns b A) (2 * p) *
        hsSchattenNorm b (finiteOperatorColumns b B) (2 * p) := by
  apply (Real.rpow_le_rpow_iff (hsSchattenNorm_nonneg b _ p)
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hsSchattenNorm_nonneg b _ _))
      (hsSchattenNorm_nonneg b _ _)) hp).mp
  have h := finiteSchatten_mul_rpow_le b A B hp
  refine h.trans_eq ?_
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hsSchattenNorm_nonneg b _ _))
    (hsSchattenNorm_nonneg b _ _),
    Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (hsSchattenNorm_nonneg b _ _),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hp.ne', Real.rpow_one]
  ring

/-- The actual covariance/Schatten identity for every positive real exponent. -/
theorem finiteSchatten_covariance_eq (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b (A.adjoint * A)) p =
      hsSchattenNorm b (finiteOperatorColumns b A) (2 * p) ^ 2 := by
  let C := A.adjoint * A
  have hC : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hcov : hsSingularCovariance b (finiteOperatorColumns b A) = C := by
    simp only [hsSingularCovariance, hilbertSchmidtOperator_finiteOperatorColumns, C, ContinuousLinearMap.mul_def]
  have hpow : hsSchattenNorm b (finiteOperatorColumns b C) p ^ p =
      hsSchattenNorm b (finiteOperatorColumns b A) (2 * p) ^ (2 * p) := by
    rw [finiteSchatten_rpow_eq_positivePowerTrace b C hC hp, finitePositivePower_trace]
    have h := hsSchattenNorm_rpow b (finiteOperatorColumns b A) (by positivity : 0 < 2 * p)
    change _ = compactPositivePowerSum (hsSingularCovariance b (finiteOperatorColumns b A)) ((2 * p) / 2) at h
    rw [hcov, show (2 * p) / 2 = p by ring] at h
    exact h.symm
  apply (Real.rpow_left_inj (hsSchattenNorm_nonneg b _ p) (sq_nonneg _) hp.ne').mp
  exact hpow.trans (by rw [Real.rpow_mul (hsSchattenNorm_nonneg b _ (2 * p)), Real.rpow_two])

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- Full cyclicity of actual powers of two arbitrary finite factors. -/
theorem finiteBasisTrace_product_pow_cycle (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (n : ℕ) :
    basisTrace b ((A * B) ^ n) = basisTrace b ((B * A) ^ n) := by
  cases n with
  | zero => rfl
  | succ n =>
    calc
      _ = basisTrace b (((A * B) ^ n * A) * B) := by rw [pow_succ, mul_assoc]
      _ = basisTrace b (B * ((A * B) ^ n * A)) := finiteBasisTrace_mul_comm b _ _
      _ = _ := by congr 1; rw [mul_pow_mul]; simp only [pow_succ', mul_assoc]

/-- Every even natural Schatten power is the actual covariance power trace. -/
theorem finiteSchatten_even_nat_pow_trace (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) (n : ℕ) (hn : 0 < n) :
    hsSchattenNorm b (finiteOperatorColumns b A) ((2 * n : ℕ) : ℝ) ^ (2 * n) =
      basisTrace b ((A.adjoint * A) ^ n) := by
  let C := A.adjoint * A
  have hC : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hcov : hsSingularCovariance b (finiteOperatorColumns b A) = C := by
    simp only [hsSingularCovariance, hilbertSchmidtOperator_finiteOperatorColumns, C, ContinuousLinearMap.mul_def]
  have h := hsSchattenNorm_rpow b (finiteOperatorColumns b A)
    (by exact_mod_cast (by omega : 0 < 2 * n) : 0 < ((2 * n : ℕ) : ℝ))
  change _ = compactPositivePowerSum (hsSingularCovariance b (finiteOperatorColumns b A)) (((2 * n : ℕ) : ℝ) / 2) at h
  rw [hcov, show ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) by push_cast; ring] at h
  have htrace := finitePositivePower_trace b C hC (n : ℝ) (Nat.cast_nonneg n)
  rw [finitePositivePower_natCast_eq_pow] at htrace
  have h' : hsSchattenNorm b (finiteOperatorColumns b A) ((2 * n : ℕ) : ℝ) ^ (2 * n) =
      compactPositivePowerSum C (n : ℝ) := by simpa only [Real.rpow_natCast] using h
  exact h'.trans htrace.symm

/-- The actual covariance power has the exact finite HS norm associated with
its even Schatten moment. -/
theorem finiteSchatten_covariance_pow_hs_norm (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) (n : ℕ) (hn : 0 < n) :
    ‖finiteOperatorColumns b ((A.adjoint * A) ^ n)‖ =
      hsSchattenNorm b (finiteOperatorColumns b A) ((4 * n : ℕ) : ℝ) ^ (2 * n) := by
  have hself : IsSelfAdjoint (A.adjoint * A) := (ContinuousLinearMap.isPositive_adjoint_comp_self A).isSelfAdjoint
  have hnorm := finiteOperatorColumns_norm_sq_trace b ((A.adjoint * A) ^ n)
  rw [(hself.pow n).adjoint_eq, ← pow_add, show n + n = 2 * n by omega] at hnorm
  have htrace := finiteSchatten_even_nat_pow_trace b A (2 * n) (by omega)
  rw [show 2 * (2 * n) = 4 * n by omega] at htrace
  apply (sq_eq_sq₀ (norm_nonneg _) (pow_nonneg (hsSchattenNorm_nonneg b _ _) _)).mp
  rw [hnorm, ← htrace, ← pow_mul, show (2 * n) * 2 = 4 * n by omega]

omit [FiniteDimensional ℝ H] in
/-- Adjoint invariance for arbitrary actual finite reconstructions. -/
theorem finiteSchatten_adjoint_eq (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteOperatorColumns b A.adjoint) p = hsSchattenNorm b (finiteOperatorColumns b A) p := by
  apply hsSchattenNorm_adjoint_reconstruction_eq b b (finiteOperatorColumns b A)
  · rw [hilbertSchmidtOperator_finiteOperatorColumns, hilbertSchmidtOperator_finiteOperatorColumns]
  · exact hp

omit [FiniteDimensional ℝ H] in
/-- The true product covariance power trace equals the power trace of the
ordered two covariance factors; this is actual cyclicity, not a certificate. -/
theorem finiteBasisTrace_product_covariance_pow (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (n : ℕ) :
    basisTrace b (((A * B).adjoint * (A * B)) ^ n) =
      basisTrace b (((A.adjoint * A) * (B * B.adjoint)) ^ n) := by
  have hadj : (A * B).adjoint = B.adjoint * A.adjoint := ContinuousLinearMap.adjoint_comp A B
  rw [hadj]
  calc
    _ = basisTrace b ((B.adjoint * ((A.adjoint * A) * B)) ^ n) := by simp only [mul_assoc]
    _ = basisTrace b ((((A.adjoint * A) * B) * B.adjoint) ^ n) := finiteBasisTrace_product_pow_cycle b _ _ n
    _ = _ := by simp only [mul_assoc]

/-- Exact constant-one product Hölder at every actual dyadic exponent
`2 * 2^m`. The proof uses the locally proved dyadic trace comparison and
actual finite trace Cauchy--Schwarz, with no Hölder input. -/
theorem finiteSchatten_mul_le_dyadic_nat (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (m : ℕ) :
    hsSchattenNorm b (finiteOperatorColumns b (A * B)) ((2 * 2 ^ m : ℕ) : ℝ) ≤
      hsSchattenNorm b (finiteOperatorColumns b A) ((4 * 2 ^ m : ℕ) : ℝ) *
        hsSchattenNorm b (finiteOperatorColumns b B) ((4 * 2 ^ m : ℕ) : ℝ) := by
  let n := 2 ^ m
  have hn : 0 < n := pow_pos (by norm_num) _
  let P := A.adjoint * A
  let Q := B * B.adjoint
  have hP : IsSelfAdjoint P := (ContinuousLinearMap.isPositive_adjoint_comp_self A).isSelfAdjoint
  have hQ : IsSelfAdjoint Q := by
    have h := (ContinuousLinearMap.isPositive_adjoint_comp_self B.adjoint).isSelfAdjoint
    simpa only [Q, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.mul_def] using h
  have hQnorm : ‖finiteOperatorColumns b (Q ^ n)‖ =
      hsSchattenNorm b (finiteOperatorColumns b B) ((4 * n : ℕ) : ℝ) ^ (2 * n) := by
    have h := finiteSchatten_covariance_pow_hs_norm b B.adjoint n hn
    rw [ContinuousLinearMap.adjoint_adjoint,
      finiteSchatten_adjoint_eq b B (by exact_mod_cast (by omega : 2 ≤ 4 * n) : 2 ≤ ((4 * n : ℕ) : ℝ))] at h
    exact h
  have hpow : hsSchattenNorm b (finiteOperatorColumns b (A * B)) ((2 * n : ℕ) : ℝ) ^ (2 * n) ≤
      (hsSchattenNorm b (finiteOperatorColumns b A) ((4 * n : ℕ) : ℝ) *
        hsSchattenNorm b (finiteOperatorColumns b B) ((4 * n : ℕ) : ℝ)) ^ (2 * n) := by
    calc
      _ = basisTrace b (((A * B).adjoint * (A * B)) ^ n) := finiteSchatten_even_nat_pow_trace b _ n hn
      _ = basisTrace b ((P * Q) ^ n) := finiteBasisTrace_product_covariance_pow b A B n
      _ ≤ basisTrace b (P ^ n * Q ^ n) := finiteBasisTrace_dyadic_product_le_powers b m P Q hP hQ
      _ ≤ ‖finiteOperatorColumns b (P ^ n)‖ * ‖finiteOperatorColumns b (Q ^ n)‖ :=
        (le_abs_self _).trans (finiteBasisTrace_mul_abs_le_hs b _ _)
      _ = _ := by rw [finiteSchatten_covariance_pow_hs_norm b A n hn, hQnorm, mul_pow]
  apply (Real.rpow_le_rpow_iff (hsSchattenNorm_nonneg b _ _)
    (mul_nonneg (hsSchattenNorm_nonneg b _ _) (hsSchattenNorm_nonneg b _ _))
    (by exact_mod_cast (by omega : 0 < 2 * n) : 0 < ((2 * n : ℕ) : ℝ))).mp
  simpa only [Real.rpow_natCast] using hpow

/-- Exact constant-one actual dyadic Schatten Hölder, in the real-exponent
normalization used by the Cotlar doubling argument. -/
theorem finiteSchatten_mul_le_dyadic (b : HilbertBasis ι ℝ H)
    (A B : H →L[ℝ] H) (m : ℕ) :
    hsSchattenNorm b (finiteOperatorColumns b (A * B)) ((2 : ℝ) ^ (m + 1)) ≤
      hsSchattenNorm b (finiteOperatorColumns b A) (2 * (2 : ℝ) ^ (m + 1)) *
        hsSchattenNorm b (finiteOperatorColumns b B) (2 * (2 : ℝ) ^ (m + 1)) := by
  have h := finiteSchatten_mul_le_dyadic_nat b A B m
  have h₂ : ((2 * 2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ (m + 1) := by push_cast; rw [pow_succ]; ring
  have h₄ : ((4 * 2 ^ m : ℕ) : ℝ) = 2 * (2 : ℝ) ^ (m + 1) := by push_cast; rw [pow_succ]; ring
  rw [h₂, h₄] at h
  exact h

end
end KernelSeq
