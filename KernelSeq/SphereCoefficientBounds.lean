import KernelSeq.SpherePolynomialMoments

/-!
# Genuine bounds on the spherical polynomial coefficients

The first omitted radial moment supplies a full extra factor d⁻¹. These
bounds concern the coefficients already identified with actual integrals;
they are proved from their finite products, not assumed eigenvalue bounds.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem spherePowerBaseCoefficient_nonneg (N : ℕ) : 0 ≤ spherePowerBaseCoefficient ι N := by
  unfold spherePowerBaseCoefficient
  split_ifs
  · exact Finset.prod_nonneg fun _ _ => div_nonneg (by positivity) (by positivity)
  · exact le_rfl

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereMixedPowerCoefficient_le_base (N k : ℕ) :
    sphereMixedPowerCoefficient ι N k ≤ spherePowerBaseCoefficient ι N := by
  rw [sphereMixedPowerCoefficient_eq_product]
  apply mul_le_of_le_one_right (spherePowerBaseCoefficient_nonneg N)
  apply Finset.prod_le_one
  · intro j _
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  · intro j _
    by_cases hden : N-j=0
    · have hnum : N/2-j=0 := by omega
      simp only [hden, hnum, Nat.cast_zero, mul_zero, div_zero, zero_le_one]
    · have hdp : (0 : ℝ) < ((N-j : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hden)
      apply (div_le_one hdp).mpr
      have hh : 2*(N/2-j) ≤ N-j := by omega
      exact_mod_cast hh

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereMixedPowerCoefficient_zero_of_half_lt {N k : ℕ} (hNk : N/2 < k) :
    sphereMixedPowerCoefficient ι N k = 0 := by
  rw [sphereMixedPowerCoefficient_eq_product]
  have hp : (∏ a ∈ Finset.range k,
      (2*((N/2-a : ℕ) : ℝ)) / ((N-a : ℕ) : ℝ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hNk)
    simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_div]
  rw [hp, mul_zero]

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereMixedPowerCoefficient_zero_of_not_even {N : ℕ} (hN : ¬Even N) (k : ℕ) :
    sphereMixedPowerCoefficient ι N k = 0 := by
  rw [sphereMixedPowerCoefficient_eq_product, spherePowerBaseCoefficient, if_neg hN, zero_mul]

omit [DecidableEq ι] in
/-- Every radial coefficient is bounded by any available initial moment
prefix; all later factors lie in [0,1] under the genuine dimension d≥1. -/
theorem spherePowerBaseCoefficient_le_dimension_power (N k : ℕ) (hk : k ≤ N/2) :
    spherePowerBaseCoefficient ι N ≤ (N : ℝ)^k / (Fintype.card ι : ℝ)^k := by
  have hd : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hd1 : 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold spherePowerBaseCoefficient
  split_ifs with hEven
  · calc
      _ ≤ ∏ a ∈ Finset.range k, (2*(a : ℝ)+1) / ((Fintype.card ι : ℝ)+2*(a : ℝ)) := by
        apply Finset.prod_le_prod_of_subset_of_le_one (Finset.range_mono hk)
        · intro a _
          exact div_nonneg (by positivity) (by positivity)
        · intro a _ _
          apply (div_le_one (by positivity : 0 < (Fintype.card ι : ℝ)+2*(a : ℝ))).mpr
          linarith
      _ ≤ ∏ _a ∈ Finset.range k, (N : ℝ)/(Fintype.card ι : ℝ) := by
        apply Finset.prod_le_prod
        · intro a _
          exact div_nonneg (by positivity) (by positivity)
        · intro a ha
          have ha' : 2*a+1 ≤ N := by have := Finset.mem_range.mp ha; omega
          calc
            _ ≤ (2*(a : ℝ)+1)/(Fintype.card ι : ℝ) :=
              div_le_div_of_nonneg_left (by positivity) hd (by nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ (a : ℝ))])
            _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast ha') hd.le
      _ = _ := by simp only [Finset.prod_const, Finset.card_range, div_pow]
  · positivity

omit [DecidableEq ι] in
/-- Off the leading degree j=m, every actual coefficient gains d^(-m-1).
Small j and the wrong parity vanish by the actual differentiated formula. -/
theorem sphereMixedPowerCoefficient_off_diagonal_le (m j : ℕ) (hjm : j ≠ m) :
    sphereMixedPowerCoefficient ι (j+m) m ≤
      ((j+m : ℕ) : ℝ)^(m+1) / (Fintype.card ι : ℝ)^(m+1) := by
  by_cases hk : m+1 ≤ (j+m)/2
  · exact (sphereMixedPowerCoefficient_le_base _ _).trans
      (spherePowerBaseCoefficient_le_dimension_power (j+m) (m+1) hk)
  · by_cases hs : (j+m)/2 < m
    · rw [sphereMixedPowerCoefficient_zero_of_half_lt hs]
      positivity
    · have hN : j+m=2*m+1 := by omega
      have hnot : ¬Even (j+m) := by rw [hN]; rintro ⟨r, hr⟩; omega
      rw [sphereMixedPowerCoefficient_zero_of_not_even hnot]
      positivity

omit [DecidableEq ι] in
theorem sphereMixedPowerCoefficient_off_diagonal_le_fixed_power (m j : ℕ) (hjm : j ≠ m) :
    sphereMixedPowerCoefficient ι (j+m) m ≤
      ((m : ℝ)+1)^(m+1) * (j+1 : ℝ)^(m+1) / (Fintype.card ι : ℝ)^(m+1) := by
  apply (sphereMixedPowerCoefficient_off_diagonal_le m j hjm).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hjm : ((j+m : ℕ) : ℝ) ≤ ((m : ℝ)+1)*(j+1 : ℝ) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((j+m : ℕ) : ℝ)) hjm (m+1)

omit [DecidableEq ι] in
/-- Uniform in the harmonic degree ell: every degree at least p has the
same d⁻p bound, with a coefficient weight depending only on the kernel power. -/
theorem sphereMixedPowerCoefficient_uniform_degree_le (ell p j : ℕ) (hp : p ≤ ell) :
    sphereMixedPowerCoefficient ι (j+ell) ell ≤
      (2 : ℝ)^p * (j+1 : ℝ)^p / (Fintype.card ι : ℝ)^p := by
  by_cases hj : j < ell
  · rw [sphereMixedPowerCoefficient_zero_of_half_lt (by omega : (j+ell)/2 < ell)]
    positivity
  · have hpre : p ≤ (j+ell)/2 := by omega
    have hh := (sphereMixedPowerCoefficient_le_base (ι := ι) (j+ell) ell).trans
      (spherePowerBaseCoefficient_le_dimension_power (ι := ι) (j+ell) p hpre)
    apply hh.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hnum : ((j+ell : ℕ) : ℝ) ≤ 2*(j+1 : ℝ) := by
      have hj' : ell ≤ j := le_of_not_gt hj
      have hcast : (ell : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj'
      push_cast
      linarith
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((j+ell : ℕ) : ℝ)) hnum p


end
end KernelSeq
