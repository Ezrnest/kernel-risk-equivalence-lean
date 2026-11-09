import KernelSeq.MixedEndpointLower
import KernelSeq.SchattenTriangle
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Dyadic exponents suffice for the actual optimized Schatten endpoint

Proves genuine exponent monotonicity of the actual HS Schatten quantities.
Rounding any p≥2 up to a power of two costs at most a factor two in p Sp.
Consequently proving analytic multiplier bounds only at dyadic exponents is
sufficient for the original logarithmic endpoint, without strengthening the
manuscript's asymptotic assumptions.
-/

namespace KernelSeq
noncomputable section

variable {ι H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hsSchattenNorm_antitone_exponent (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p q : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    hsSchattenNorm b c q ≤ hsSchattenNorm b c p := by
  have hp0 : 0 < p := by linarith
  have hq : 2 ≤ q := hp.trans hpq
  have hq0 : 0 < q := by linarith
  let S := hsSchattenNorm b c p
  have hS : 0 ≤ S := hsSchattenNorm_nonneg b c p
  have hdiff : 0 ≤ q - p := sub_nonneg.mpr hpq
  have hterm (i : HSSingularIndex b c) : i.1 ^ (q / 2) ≤ S ^ (q - p) * i.1 ^ (p / 2) := by
    have hi : 0 ≤ i.1 := hsSingularValue_nonneg b c i
    have hbound : i.1 ≤ S ^ 2 := (hsSingularValue_le_opNorm_sq b c i).trans
      (pow_le_pow_left₀ (norm_nonneg _) (opNorm_le_hsSchattenNorm b c hp) 2)
    have hpw := Real.rpow_le_rpow hi hbound (div_nonneg hdiff (by norm_num : (0 : ℝ) ≤ 2))
    have hscale : (S ^ 2) ^ ((q - p) / 2) = S ^ (q - p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS]
      congr 1
      ring
    rw [hscale] at hpw
    have heq : i.1 ^ (q / 2) = i.1 ^ ((q - p) / 2) * i.1 ^ (p / 2) := by
      rw [← Real.rpow_add_of_nonneg hi (by positivity) (by positivity)]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hpw (Real.rpow_nonneg hi _)
  have hsum : (∑' i : HSSingularIndex b c, i.1 ^ (q / 2)) ≤ S ^ q := by
    calc
      _ ≤ ∑' i : HSSingularIndex b c, S ^ (q - p) * i.1 ^ (p / 2) :=
        (summable_hsSingularPower b c hq).tsum_le_tsum hterm
          ((summable_hsSingularPower b c hp).mul_left _)
      _ = S ^ (q - p) * S ^ p := by rw [tsum_mul_left, ← hsSchattenNorm_rpow b c hp0]
      _ = S ^ q := by
        rw [← Real.rpow_add_of_nonneg hS hdiff hp0.le]
        congr 1
        ring
  have hr := Real.rpow_le_rpow
    (tsum_nonneg (fun i => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _))
    hsum (one_div_nonneg.mpr hq0.le)
  change hsSchattenNorm b c q ≤ (S ^ q) ^ (1 / q) at hr
  rw [← Real.rpow_mul hS, mul_one_div_cancel hq0.ne', Real.rpow_one] at hr
  exact hr

def dyadicSchattenExponent (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 1)

theorem dyadicSchattenExponent_ge_two (n : ℕ) : 2 ≤ dyadicSchattenExponent n := by
  unfold dyadicSchattenExponent
  rw [pow_succ]
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith

theorem exists_dyadicSchattenExponent_between {p : ℝ} (hp : 2 ≤ p) :
    ∃ n : ℕ, p ≤ dyadicSchattenExponent n ∧ dyadicSchattenExponent n ≤ 2 * p := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ p) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, hn'.le, ?_⟩
  unfold dyadicSchattenExponent
  rw [pow_succ]
  nlinarith

theorem dyadicSchatten_candidate_le (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E)
    {p : ℝ} (hp : 2 ≤ p) :
    ∃ n : ℕ, dyadicSchattenExponent n * hsSchattenNorm b c (dyadicSchattenExponent n) ≤
      2 * (p * hsSchattenNorm b c p) := by
  obtain ⟨n, hpn, hnp⟩ := exists_dyadicSchattenExponent_between hp
  refine ⟨n, ?_⟩
  calc
    _ ≤ dyadicSchattenExponent n * hsSchattenNorm b c p :=
      mul_le_mul_of_nonneg_left (hsSchattenNorm_antitone_exponent b c hp hpn)
        (le_trans (by norm_num) (dyadicSchattenExponent_ge_two n))
    _ ≤ (2 * p) * hsSchattenNorm b c p :=
      mul_le_mul_of_nonneg_right hnp (hsSchattenNorm_nonneg b c p)
    _ = _ := by ring

def hsDyadicSchattenEndpoint (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E) : ℝ :=
  sInf (Set.range (fun n : ℕ => dyadicSchattenExponent n * hsSchattenNorm b c (dyadicSchattenExponent n)))

theorem hsDyadicSchattenEndpoint_nonneg (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E) :
    0 ≤ hsDyadicSchattenEndpoint b c := by
  apply le_csInf
  · exact ⟨_, Set.mem_range_self 0⟩
  · rintro _ ⟨n, rfl⟩
    exact mul_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans (dyadicSchattenExponent_ge_two n))
      (hsSchattenNorm_nonneg b c _)

theorem hsDyadicSchattenEndpoint_le_candidate (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (n : ℕ) :
    hsDyadicSchattenEndpoint b c ≤ dyadicSchattenExponent n * hsSchattenNorm b c (dyadicSchattenExponent n) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact mul_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans (dyadicSchattenExponent_ge_two k))
      (hsSchattenNorm_nonneg b c _)
  · exact Set.mem_range_self n

theorem hsSchattenEndpoint_le_dyadic (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E) :
    hsSchattenEndpoint b c ≤ hsDyadicSchattenEndpoint b c := by
  apply le_csInf
  · exact ⟨_, Set.mem_range_self 0⟩
  · rintro _ ⟨n, rfl⟩
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨p, rfl⟩
      exact mul_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans p.2) (hsSchattenNorm_nonneg b c _)
    · exact Set.mem_range_self (⟨dyadicSchattenExponent n, dyadicSchattenExponent_ge_two n⟩ : {p : ℝ // 2 ≤ p})

/-- The dyadic optimization has exactly the same original logarithmic scale,
up to the fixed factor two, for actual arbitrary HS operators. -/
theorem hsDyadicSchattenEndpoint_le_two (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E) :
    hsDyadicSchattenEndpoint b c ≤ 2 * hsSchattenEndpoint b c := by
  have hhalf : hsDyadicSchattenEndpoint b c / 2 ≤ hsSchattenEndpoint b c := by
    apply le_csInf
    · exact ⟨_, Set.mem_range_self (⟨2, le_rfl⟩ : {p : ℝ // 2 ≤ p})⟩
    · rintro _ ⟨p, rfl⟩
      obtain ⟨n, hn⟩ := dyadicSchatten_candidate_le b c p.2
      have h := (hsDyadicSchattenEndpoint_le_candidate b c n).trans hn
      linarith
  linarith

/-- Genuine dyadic multiplier bounds suffice for the original all-p endpoint.
This changes only a fixed constant, not any scale condition in the manuscript. -/
theorem le_mul_hsSchattenEndpoint_of_dyadic (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {N C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, N ≤ C * (dyadicSchattenExponent n * hsSchattenNorm b c (dyadicSchattenExponent n))) :
    N ≤ (2 * C) * hsSchattenEndpoint b c := by
  by_cases hC0 : C = 0
  · simpa only [hC0, mul_zero, zero_mul] using h 0
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  have hdiv : N / C ≤ hsDyadicSchattenEndpoint b c := by
    apply le_csInf
    · exact ⟨_, Set.mem_range_self 0⟩
    · rintro _ ⟨n, rfl⟩
      exact (div_le_iff₀ hCp).mpr (by simpa only [mul_comm C] using h n)
  have hn : N ≤ C * hsDyadicSchattenEndpoint b c := by
    exact (div_le_iff₀ hCp).mp hdiv |>.trans_eq (mul_comm _ _)
  exact hn.trans ((mul_le_mul_of_nonneg_left (hsDyadicSchattenEndpoint_le_two b c) hC).trans_eq (by ring))

end
end KernelSeq
