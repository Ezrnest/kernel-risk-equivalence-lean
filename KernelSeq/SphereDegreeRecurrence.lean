import KernelSeq.SpherePolynomialMoments

/-!
# Actual degree recurrence of the spherical power coefficients

The degree-two recurrence is proved for the constructed moment coefficients,
including parity and unresolved-degree zeros. It supplies degree monotonicity
without postulating a harmonic decomposition or completeness theorem.
-/

namespace KernelSeq

open scoped BigOperators
noncomputable section

theorem sphereMixedPowerCoefficient_eq_zero_of_half_lt
    {ι : Type*} [Fintype ι] (N k : ℕ) (hk : N/2 < k) :
    sphereMixedPowerCoefficient ι N k = 0 := by
  induction k with
  | zero => omega
  | succ k IH =>
    rw [sphereMixedPowerCoefficient]
    by_cases h : N/2 < k
    · rw [IH h, zero_mul, zero_div]
    · have he : N/2-k = 0 := by omega
      rw [he, Nat.cast_zero, mul_zero, mul_zero, zero_div]

theorem sphereMixedPowerCoefficient_eq_zero_of_not_even
    {ι : Type*} [Fintype ι] (N k : ℕ) (hN : ¬Even N) :
    sphereMixedPowerCoefficient ι N k = 0 := by
  induction k with
  | zero => simp only [sphereMixedPowerCoefficient, spherePowerBaseCoefficient, if_neg hN]
  | succ k IH => rw [sphereMixedPowerCoefficient, IH, zero_mul, zero_div]

theorem spherePowerBaseCoefficient_even_succ
    {ι : Type*} [Fintype ι] (r : ℕ) :
    spherePowerBaseCoefficient ι (2*(r+1)) =
      spherePowerBaseCoefficient ι (2*r)*(2*(r:ℝ)+1)/((Fintype.card ι : ℝ)+2*(r:ℝ)) := by
  have h0 : Even (2*r) := ⟨r, by omega⟩
  have h1 : Even (2*(r+1)) := ⟨r+1, by omega⟩
  rw [spherePowerBaseCoefficient, if_pos h1, spherePowerBaseCoefficient, if_pos h0,
    show (2*(r+1))/2=r+1 by omega, show (2*r)/2=r by omega, Finset.prod_range_succ]
  ring

theorem sphereMixedPowerCoefficient_even_degree_succ
    {ι : Type*} [Fintype ι] [Nonempty ι] (r k : ℕ) (hk : k ≤ r) :
    sphereMixedPowerCoefficient ι (2*(r+1)) (k+2) =
      sphereMixedPowerCoefficient ι (2*r) k*(2*((r-k : ℕ):ℝ))/
        ((Fintype.card ι : ℝ)+2*(r:ℝ)) := by
  have hd : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  induction k with
  | zero =>
    simp only [sphereMixedPowerCoefficient, Nat.sub_zero]
    rw [spherePowerBaseCoefficient_even_succ]
    rw [show (2*(r+1))/2=r+1 by omega, show r+1-1=r by omega,
      show 2*(r+1)-1=2*r+1 by omega]
    push_cast
    field_simp
  | succ k IH =>
    have hkr : k ≤ r := by omega
    rw [sphereMixedPowerCoefficient, IH hkr, sphereMixedPowerCoefficient]
    rw [show (2*(r+1))/2=r+1 by omega, show (2*r)/2=r by omega,
      show r+1-(k+2)=r-(k+1) by omega, show 2*(r+1)-(k+2)=2*r-k by omega]
    ring

/-- For fixed kernel power `j`, increasing the actual degree by two has
the exact classical ratio. The numerator vanishes when `j < k`. -/
theorem sphereMixedPowerCoefficient_degree_two_recurrence
    {ι : Type*} [Fintype ι] [Nonempty ι] (j k : ℕ) :
    sphereMixedPowerCoefficient ι (j+(k+2)) (k+2) =
      sphereMixedPowerCoefficient ι (j+k) k*((j-k : ℕ):ℝ)/
        ((Fintype.card ι : ℝ)+(j:ℝ)+(k:ℝ)) := by
  by_cases hEven : Even (j+k)
  · obtain ⟨r, hr⟩ := hEven
    have hn : j+k=2*r := by omega
    have hn' : j+(k+2)=2*(r+1) := by omega
    by_cases hkr : k ≤ r
    · have hnum : 2*(r-k)=j-k := by omega
      have hh := sphereMixedPowerCoefficient_even_degree_succ (ι := ι) r k hkr
      rw [← hn, ← hn'] at hh
      have hnumR : 2*((r-k : ℕ):ℝ) = ((j-k : ℕ):ℝ) := by exact_mod_cast hnum
      have hden : (Fintype.card ι : ℝ)+2*(r:ℝ) = (Fintype.card ι : ℝ)+(j:ℝ)+(k:ℝ) := by
        have hnR : (j:ℝ)+(k:ℝ)=2*(r:ℝ) := by exact_mod_cast hn
        linarith
      simpa only [hnumR, hden] using hh
    · rw [sphereMixedPowerCoefficient_eq_zero_of_half_lt _ _ (by omega : (j+(k+2))/2 < k+2),
        sphereMixedPowerCoefficient_eq_zero_of_half_lt _ _ (by omega : (j+k)/2 < k),
        zero_mul, zero_div]
  · have hEven' : ¬Even (j+(k+2)) := by
      rintro ⟨r, hr⟩
      apply hEven
      exact ⟨r-1, by omega⟩
    rw [sphereMixedPowerCoefficient_eq_zero_of_not_even _ _ hEven',
      sphereMixedPowerCoefficient_eq_zero_of_not_even _ _ hEven, zero_mul, zero_div]

theorem sphereMixedPowerCoefficient_degree_two_le
    {ι : Type*} [Fintype ι] [Nonempty ι] (j k : ℕ) :
    sphereMixedPowerCoefficient ι (j+(k+2)) (k+2) ≤ sphereMixedPowerCoefficient ι (j+k) k := by
  rw [sphereMixedPowerCoefficient_degree_two_recurrence]
  have hd : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ (by positivity : 0 < (Fintype.card ι : ℝ)+(j:ℝ)+(k:ℝ))).mpr
  apply mul_le_mul_of_nonneg_left _ (sphereMixedPowerCoefficient_nonneg _ _)
  have hj : ((j-k : ℕ):ℝ) ≤ j := by exact_mod_cast Nat.sub_le j k
  linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

end
end KernelSeq
