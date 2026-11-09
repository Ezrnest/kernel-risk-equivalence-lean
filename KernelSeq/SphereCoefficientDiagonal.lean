import KernelSeq.SpherePolynomialMoments
import KernelSeq.SphereMonomialBlock
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The exact diagonal coefficient of a spherical monomial block

The finite scalar products reduce to `m!`; consequently the actual mixed
spherical moment coefficient is `m!` times the genuine degree moment.
Neither a harmonic-block constant nor its normalization is an assumption.
-/

namespace KernelSeq

open scoped BigOperators
noncomputable section

theorem odd_product_mul_two_pow_factorial (m : ℕ) :
    (∏ a ∈ Finset.range m, (2*a+1))*2^m*m.factorial = (2*m).factorial := by
  induction m with
  | zero => simp
  | succ m IH =>
    rw [Finset.prod_range_succ, pow_succ, Nat.factorial_succ]
    calc
      _ = (2*m+2)*(2*m+1)*((∏ a ∈ Finset.range m, (2*a+1))*2^m*m.factorial) := by ring
      _ = _ := by
        rw [IH, show 2*(m+1) = (2*m+1)+1 by ring, Nat.factorial_succ,
          Nat.factorial_succ]
        ring

theorem spherical_diagonal_product_eq_factorial (m : ℕ) :
    (∏ a ∈ Finset.range m, (2*(a:ℝ)+1))*
      (∏ k ∈ Finset.range m, (2*((m-k : ℕ):ℝ))/((2*m-k : ℕ):ℝ)) = (m.factorial : ℝ) := by
  have hn : (∏ k ∈ Finset.range m, ((m-k : ℕ):ℝ)) = (m.factorial : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  have hd : (∏ k ∈ Finset.range m, ((2*m-k : ℕ):ℝ)) = ((2*m).descFactorial m : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range]
  have hodd : (∏ a ∈ Finset.range m, (2*(a:ℝ)+1))*(2:ℝ)^m*(m.factorial : ℝ) =
      ((2*m).factorial : ℝ) := by exact_mod_cast odd_product_mul_two_pow_factorial m
  have hfactor : (m.factorial : ℝ)*((2*m).descFactorial m : ℝ) = ((2*m).factorial : ℝ) := by
    exact_mod_cast (by simpa only [show 2*m-m=m by omega] using
      Nat.factorial_mul_descFactorial (show m ≤ 2*m by omega))
  have hdpos : (0 : ℝ) < (2*m).descFactorial m :=
    Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr (by omega))
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range]
  rw [hn, hd]
  rw [← mul_div_assoc]
  apply (div_eq_iff hdpos.ne').mpr
  nlinarith only [hodd, hfactor]

theorem sphereMixedPowerCoefficient_diagonal
    {ι : Type*} [Fintype ι] (m : ℕ) :
    sphereMixedPowerCoefficient ι (2*m) m = (m.factorial : ℝ)*degreeSphereMoment ι m := by
  have heven : Even (2*m) := ⟨m, by omega⟩
  have hdiv : (2*m)/2 = m := by omega
  rw [sphereMixedPowerCoefficient_eq_product, spherePowerBaseCoefficient, if_pos heven, hdiv,
    Finset.prod_div_distrib]
  calc
    _ = (∏ k ∈ Finset.range m, ((Fintype.card ι : ℝ)+2*(k:ℝ)))⁻¹*
        ((∏ a ∈ Finset.range m, (2*(a:ℝ)+1))*
          (∏ k ∈ Finset.range m, (2*((m-k : ℕ):ℝ))/((2*m-k : ℕ):ℝ))) := by ring
    _ = _ := by rw [spherical_diagonal_product_eq_factorial]; unfold degreeSphereMoment; ring

end
end KernelSeq
