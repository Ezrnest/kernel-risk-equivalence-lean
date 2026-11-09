import KernelSeq.SphereInnerPower
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Choose.Cast

/-!
# Genuine all-order even coordinate moments

The actual radial line-polynomial identity supplies the second-coordinate
coefficient. Summing it with the sphere equation gives the exact recurrence
for every even degree, without a Gaussian representation or harmonic-spectrum
assumption.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def sphereBasisPole (i : ι) : KernelSphere (EuclideanSpace ℝ ι) :=
  ⟨EuclideanSpace.basisFun ι ℝ i, mem_sphere_zero_iff_norm.mpr
    ((EuclideanSpace.basisFun ι ℝ).orthonormal.norm_eq_one i)⟩

def sphereCoordinateEvenMoment (r : ℕ) (i : ι) : ℝ :=
  ∫ y : KernelSphere (EuclideanSpace ℝ ι), (y : EuclideanSpace ℝ ι) i^(2*r) ∂uniformSphere

omit [DecidableEq ι] [Nonempty ι] in
theorem sphereInnerPowerMoment_basis (n : ℕ) (i : ι) :
    sphereInnerPowerMoment n (EuclideanSpace.basisFun ι ℝ i) =
      ∫ y : KernelSphere (EuclideanSpace ℝ ι), (y : EuclideanSpace ℝ ι) i^n ∂uniformSphere := by
  simp only [sphereInnerPowerMoment, EuclideanSpace.basisFun_inner]

private theorem coeff_one_add_X_sq_pow (r : ℕ) :
    (((1 : Polynomial ℝ) + Polynomial.X^2)^(r+1)).coeff 2 = (r+1 : ℝ) := by
  have he : ((1 : Polynomial ℝ) + Polynomial.X^2)^(r+1) =
      Polynomial.expand ℝ 2 ((1 + Polynomial.X)^(r+1)) := by simp
  rw [he, Polynomial.coeff_expand (by norm_num : 0 < 2)]
  simp [Polynomial.coeff_one_add_X_pow]

/-- The actual second translation coefficient, including repeated labels. -/
theorem sphere_even_mixed_coefficient (r : ℕ) (i j : ι) :
    ((2*(r+1)).choose 2 : ℝ) *
      (∫ y : KernelSphere (EuclideanSpace ℝ ι),
        (y : EuclideanSpace ℝ ι) i^(2*r) * (y : EuclideanSpace ℝ ι) j^2 ∂uniformSphere) =
      sphereCoordinateEvenMoment (r+1) i *
        (if i=j then ((2*(r+1)).choose 2 : ℝ) else (r+1 : ℝ)) := by
  let b := EuclideanSpace.basisFun ι ℝ
  have he := sphereLineMomentPolynomial_even (r+1) (b i) (b j) (sphereBasisPole i)
  have hh := congrArg (fun P : Polynomial ℝ => P.coeff 2) he
  rw [sphereLineMomentPolynomial_coeff (by omega : 2 ≤ 2*(r+1))] at hh
  have hsub : 2*(r+1)-2 = 2*r := by omega
  simp only [hsub, sphereMixedPowerMoment, b, EuclideanSpace.basisFun_inner] at hh
  have hnorm (k : ι) : ‖b k‖ = 1 := (EuclideanSpace.basisFun ι ℝ).orthonormal.norm_eq_one k
  have hinner : (b j) i = if i=j then 1 else 0 := by
    simpa only [b, EuclideanSpace.basisFun_inner] using
      (orthonormal_iff_ite.mp (EuclideanSpace.basisFun ι ℝ).orthonormal) i j
  have hpole : sphereInnerPowerMoment (2*(r+1)) (sphereBasisPole i : EuclideanSpace ℝ ι) =
      sphereCoordinateEvenMoment (r+1) i := by
    change sphereInnerPowerMoment (2*(r+1)) (EuclideanSpace.basisFun ι ℝ i) = _
    rw [sphereInnerPowerMoment_basis]
    rfl
  rw [hpole] at hh
  change _ = (Polynomial.C (sphereCoordinateEvenMoment (r+1) i) *
    (Polynomial.C (‖b i‖^2) + Polynomial.C (2*(b j) i)*Polynomial.X +
      Polynomial.C (‖b j‖^2)*Polynomial.X^2)^(r+1)).coeff 2 at hh
  rw [hnorm, hnorm, hinner] at hh
  simp only [one_pow, Polynomial.C_1, Polynomial.coeff_C_mul] at hh
  by_cases hij : i=j
  · rw [if_pos hij]
    rw [if_pos hij] at hh
    have hp : ((1 : Polynomial ℝ) + Polynomial.C (2*1)*Polynomial.X + Polynomial.X^2) =
        (Polynomial.X+1)^2 := by simp only [mul_one, Polynomial.C_ofNat]; ring
    simp only [one_mul] at hh
    rw [hp, ← pow_mul, Polynomial.coeff_X_add_one_pow] at hh
    exact hh
  · rw [if_neg hij]
    rw [if_neg hij] at hh
    simp only [mul_zero, Polynomial.C_0, zero_mul, add_zero, one_mul] at hh
    rw [coeff_one_add_X_sq_pow] at hh
    exact hh

/-- The Laplacian recurrence is derived by summing the actual second
translation coefficients and using the pointwise sphere equation. -/
theorem sphereCoordinateEvenMoment_recurrence (r : ℕ) (i : ι) :
    ((Fintype.card ι : ℝ) + 2*(r : ℝ)) * sphereCoordinateEvenMoment (r+1) i =
      (2*(r : ℝ)+1) * sphereCoordinateEvenMoment r i := by
  have hchoose : ((2*(r+1)).choose 2 : ℝ) = ((r : ℝ)+1) * (2*(r : ℝ)+1) := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hsumSphere (y : KernelSphere (EuclideanSpace ℝ ι)) :
      (∑ j : ι, (y : EuclideanSpace ℝ ι) j^2) = 1 := by
    have hi := real_inner_self_eq_norm_sq (y : EuclideanSpace ℝ ι)
    have hy : ‖(y : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
    simpa only [PiLp.inner_apply, Real.inner_apply, ← pow_two, hy, one_pow] using hi
  have hsum : (∑ j : ι, ∫ y : KernelSphere (EuclideanSpace ℝ ι),
      (y : EuclideanSpace ℝ ι) i^(2*r) * (y : EuclideanSpace ℝ ι) j^2 ∂uniformSphere) =
      sphereCoordinateEvenMoment r i := by
    rw [← integral_finsetSum _ (fun j _ => integrable_continuous_uniformSphere (by fun_prop))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [← Finset.mul_sum, hsumSphere, mul_one]
  have hcoef : (∑ j : ι, if i=j then ((2*(r+1)).choose 2 : ℝ) else (r+1 : ℝ)) =
      ((r : ℝ)+1) * ((Fintype.card ι : ℝ) + 2*(r : ℝ)) := by
    have hterm (j : ι) : (if i=j then ((2*(r+1)).choose 2 : ℝ) else (r+1 : ℝ)) =
        (r+1 : ℝ) + if i=j then ((2*(r+1)).choose 2 : ℝ) - (r+1 : ℝ) else 0 := by
      split_ifs <;> ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hchoose]
    ring
  have hh : ((2*(r+1)).choose 2 : ℝ) * sphereCoordinateEvenMoment r i =
      sphereCoordinateEvenMoment (r+1) i *
        (((r : ℝ)+1) * ((Fintype.card ι : ℝ) + 2*(r : ℝ))) := by
    rw [← hsum, Finset.mul_sum]
    simp_rw [sphere_even_mixed_coefficient]
    rw [← Finset.mul_sum, hcoef]
  have hr : (0 : ℝ) < (r : ℝ)+1 := by positivity
  apply mul_left_cancel₀ hr.ne'
  calc
    _ = sphereCoordinateEvenMoment (r+1) i *
        (((r : ℝ)+1) * ((Fintype.card ι : ℝ) + 2*(r : ℝ))) := by ring
    _ = _ := hh.symm
    _ = _ := by rw [hchoose]; ring

/-- Exact every-order coordinate even moments under the genuine sphere law. -/
theorem sphereCoordinateEvenMoment_eq_product (r : ℕ) (i : ι) :
    sphereCoordinateEvenMoment r i =
      ∏ k ∈ Finset.range r, (2*(k : ℝ)+1) / ((Fintype.card ι : ℝ)+2*(k : ℝ)) := by
  induction r with
  | zero => simp [sphereCoordinateEvenMoment]
  | succ r ih =>
    have hd : (0 : ℝ) < (Fintype.card ι : ℝ) + 2*(r : ℝ) := by
      have hd0 : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
      positivity
    rw [Finset.prod_range_succ]
    calc
      _ = ((2*(r : ℝ)+1) * sphereCoordinateEvenMoment r i) /
          ((Fintype.card ι : ℝ)+2*(r : ℝ)) := by
        apply (eq_div_iff hd.ne').mpr
        simpa only [mul_comm] using sphereCoordinateEvenMoment_recurrence r i
      _ = _ := by rw [ih]; ring


/-- The radial even moment has its actual closed coefficient for every x. -/
theorem sphereInnerPowerMoment_even_eq_product (r : ℕ) (x : EuclideanSpace ℝ ι) (i : ι) :
    sphereInnerPowerMoment (2*r) x = ‖x‖^(2*r) *
      (∏ k ∈ Finset.range r, (2*(k : ℝ)+1) / ((Fintype.card ι : ℝ)+2*(k : ℝ))) := by
  rw [sphereInnerPowerMoment_radial (pole := sphereBasisPole i)]
  have hp : sphereInnerPowerMoment (2*r) (sphereBasisPole i : EuclideanSpace ℝ ι) =
      sphereCoordinateEvenMoment r i := by
    change sphereInnerPowerMoment (2*r) (EuclideanSpace.basisFun ι ℝ i) = _
    rw [sphereInnerPowerMoment_basis]
    rfl
  rw [hp, sphereCoordinateEvenMoment_eq_product]

theorem sphereCoordinateEvenMoment_pos (r : ℕ) (i : ι) : 0 < sphereCoordinateEvenMoment r i := by
  rw [sphereCoordinateEvenMoment_eq_product]
  apply Finset.prod_pos
  intro k _
  have hd : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  positivity

end
end KernelSeq
