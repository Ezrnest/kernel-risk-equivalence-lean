import KernelSeq.SpherePolynomialMoments
import Mathlib.Data.Multiset.Count

/-!
# Actual coordinate jets of radial monomial functions

Repeated coordinate indices are retained in multisets. The radial spaces
are actual spans of ambient functions, so their derivatives can be taken
before restricting to the unit sphere. Integer degree caps make the spaces
below degree zero genuinely zero.
-/

namespace KernelSeq

open MeasureTheory Submodule Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ambientMultisetMonomial (a : Multiset ι) (x : EuclideanSpace ℝ ι) : ℝ :=
  (a.map (fun i => x i)).prod

omit [Fintype ι] [DecidableEq ι] in
theorem ambientMultisetMonomial_cons (a : Multiset ι) (i : ι) (x : EuclideanSpace ℝ ι) :
    ambientMultisetMonomial (i ::ₘ a) x = x i*ambientMultisetMonomial a x := by
  simp only [ambientMultisetMonomial, Multiset.map_cons, Multiset.prod_cons]

omit [Fintype ι] [DecidableEq ι] in
theorem ambientMultisetMonomial_continuous (a : Multiset ι) : Continuous (ambientMultisetMonomial a) := by
  induction a using Multiset.induction_on with
  | empty => exact continuous_const
  | @cons i a IH =>
    have he : ambientMultisetMonomial (i ::ₘ a) =
        fun x => x i*ambientMultisetMonomial a x := funext (ambientMultisetMonomial_cons a i)
    rw [he]
    exact (show Continuous (fun x : EuclideanSpace ℝ ι => x i) by fun_prop).mul IH

omit [Fintype ι] in
theorem ambientMultisetMonomial_erase (a : Multiset ι) (i : ι) (hi : i ∈ a)
    (x : EuclideanSpace ℝ ι) :
    x i*ambientMultisetMonomial (a.erase i) x = ambientMultisetMonomial a x := by
  rw [← ambientMultisetMonomial_cons, Multiset.cons_erase hi]

theorem hasDerivAt_ambientMultisetMonomial_add_basis
    (a : Multiset ι) (i : ι) (x : EuclideanSpace ℝ ι) :
    HasDerivAt (fun c : ℝ => ambientMultisetMonomial a (x+c • EuclideanSpace.basisFun ι ℝ i))
      ((a.count i : ℝ)*ambientMultisetMonomial (a.erase i) x) 0 := by
  induction a using Multiset.induction_on with
  | empty => simpa [ambientMultisetMonomial] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | @cons j a IH =>
    have hc : HasDerivAt (fun c : ℝ => (x+c • EuclideanSpace.basisFun ι ℝ i) j)
        (if j=i then (1 : ℝ) else 0) 0 := by
      simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, euclidean_basis_coordinate,
        mul_one, mul_zero, add_zero, id_eq, one_mul] using
        ((hasDerivAt_id (0 : ℝ)).mul_const (if j=i then (1 : ℝ) else 0)).const_add (x j)
    have hh := hc.fun_mul IH
    simp only [zero_smul, add_zero] at hh
    have hfun : (fun c : ℝ => (x+c • EuclideanSpace.basisFun ι ℝ i) j*
        ambientMultisetMonomial a (x+c • EuclideanSpace.basisFun ι ℝ i)) =
        (fun c : ℝ => ambientMultisetMonomial (j ::ₘ a) (x+c • EuclideanSpace.basisFun ι ℝ i)) := by
      funext c
      exact (ambientMultisetMonomial_cons a j _).symm
    rw [hfun] at hh
    apply hh.congr_deriv
    by_cases hji : j=i
    · subst j
      rw [if_pos rfl, Multiset.count_cons_self, Multiset.erase_cons_head]
      by_cases hi : i ∈ a
      · rw [Nat.cast_add, Nat.cast_one]
        have he := ambientMultisetMonomial_erase a i hi x
        nlinarith only [congrArg ((a.count i : ℝ)*·) he]
      · simp only [Multiset.count_eq_zero.mpr hi, Nat.cast_zero, zero_mul, mul_zero, add_zero, one_mul,
          zero_add, Nat.cast_one]
    · rw [if_neg hji, Multiset.count_cons_of_ne (Ne.symm hji), Multiset.erase_cons_tail a hji]
      rw [ambientMultisetMonomial_cons]
      ring

def radialWordMonomial (a : Multiset ι) (l : ℕ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ambientMultisetMonomial a x*(‖x‖^2)^l

def radialPolynomialSpace (ι : Type*) [Fintype ι] (p : ℤ) :
    Submodule ℝ (EuclideanSpace ℝ ι → ℝ) :=
  span ℝ {f | ∃ (a : Multiset ι) (l : ℕ), (a.card : ℤ) ≤ p ∧ f = radialWordMonomial a l}

omit [DecidableEq ι] in
theorem radialWordMonomial_mem {a : Multiset ι} (l : ℕ) {p : ℤ} (ha : (a.card : ℤ) ≤ p) :
    radialWordMonomial a l ∈ radialPolynomialSpace ι p :=
  Submodule.subset_span ⟨a,l,ha,rfl⟩

omit [DecidableEq ι] in
theorem radialPolynomialSpace_mono {p q : ℤ} (hpq : p ≤ q) :
    radialPolynomialSpace ι p ≤ radialPolynomialSpace ι q := by
  apply Submodule.span_le.mpr
  rintro f ⟨a,l,ha,rfl⟩
  exact radialWordMonomial_mem l (ha.trans hpq)

omit [DecidableEq ι] in
theorem radialPolynomialSpace_eq_bot {p : ℤ} (hp : p < 0) :
    radialPolynomialSpace ι p = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro f ⟨a,l,ha,hf⟩
  have hn : (0 : ℤ) ≤ a.card := Nat.cast_nonneg _
  omega

omit [DecidableEq ι] in
theorem radialPolynomialSpace_continuous {p : ℤ} {f : EuclideanSpace ℝ ι → ℝ}
    (hf : f ∈ radialPolynomialSpace ι p) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a,l,_,rfl⟩ := hf
    exact (ambientMultisetMonomial_continuous a).mul ((continuous_norm.pow 2).pow l)
  | zero => exact continuous_const
  | add f g hf hg IHf IHg => exact IHf.add IHg
  | smul c f hf IH => exact (continuous_const (y := c)).mul IH

def radialWordDerivative (a : Multiset ι) (i : ι) (l : ℕ) : EuclideanSpace ℝ ι → ℝ :=
  (a.count i : ℝ) • radialWordMonomial (a.erase i) l

theorem radialWordDerivative_mem (a : Multiset ι) (i : ι) (l : ℕ) :
    radialWordDerivative a i l ∈ radialPolynomialSpace ι ((a.card : ℤ)-1) := by
  by_cases hi : i ∈ a
  · apply Submodule.smul_mem
    apply radialWordMonomial_mem
    have he := Multiset.card_erase_add_one hi
    omega
  · simp only [radialWordDerivative, Multiset.count_eq_zero.mpr hi, Nat.cast_zero, zero_smul]
    exact Submodule.zero_mem _

/-- Differentiation in a coordinate direction raises the nonradial degree
cap by at most one. Radial powers remain explicit ambient functions. -/
theorem radialPolynomialSpace_line_derivative {p : ℤ} {f : EuclideanSpace ℝ ι → ℝ}
    (hf : f ∈ radialPolynomialSpace ι p) (i : ι) :
    ∃ g ∈ radialPolynomialSpace ι (p+1), ∀ x : EuclideanSpace ℝ ι,
      HasDerivAt (fun c : ℝ => f (x+c • EuclideanSpace.basisFun ι ℝ i)) (g x) 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a,l,ha,rfl⟩ := hf
    let g := radialWordDerivative a i l + (2*(l:ℝ)) • radialWordMonomial (i ::ₘ a) (l-1)
    have hg1 : radialWordDerivative a i l ∈ radialPolynomialSpace ι (p+1) :=
      radialPolynomialSpace_mono (by omega) (radialWordDerivative_mem a i l)
    have hg2 : (2*(l:ℝ)) • radialWordMonomial (i ::ₘ a) (l-1) ∈ radialPolynomialSpace ι (p+1) := by
      apply Submodule.smul_mem
      apply radialWordMonomial_mem
      simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      omega
    refine ⟨g, Submodule.add_mem _ hg1 hg2, fun x => ?_⟩
    have hn := hasDerivAt_norm_sq_add_smul x (EuclideanSpace.basisFun ι ℝ i)
    rw [real_inner_comm, EuclideanSpace.basisFun_inner] at hn
    have hh := (hasDerivAt_ambientMultisetMonomial_add_basis a i x).fun_mul (hn.fun_pow l)
    simp only [zero_smul, add_zero] at hh
    apply hh.congr_deriv
    dsimp [g, radialWordDerivative, radialWordMonomial]
    rw [ambientMultisetMonomial_cons]
    ring
  | zero => exact ⟨0, Submodule.zero_mem _, fun x => hasDerivAt_const 0 0⟩
  | add f g hf hg IHf IHg =>
    obtain ⟨df,hdf,hf'⟩ := IHf
    obtain ⟨dg,hdg,hg'⟩ := IHg
    exact ⟨df+dg,Submodule.add_mem _ hdf hdg,fun x => (hf' x).add (hg' x)⟩
  | smul c f hf IH =>
    obtain ⟨df,hdf,hf'⟩ := IH
    exact ⟨c • df,Submodule.smul_mem _ c hdf,fun x => (hf' x).const_mul c⟩

section ActualSphereMoments
variable [Nonempty ι]

/-- The full ambient moment of any repeated-coordinate word has its actual
degree coefficient as leading term. All pair contractions are contained in
the radial span with nonradial degree at most two less than the word.
The statement is proved before restricting to the unit sphere. -/
theorem weightedSpherePowerMoment_multiset_mod_radial
    (N : ℕ) (a : Multiset ι) (hA : a.card ≤ N) :
    ∃ R ∈ radialPolynomialSpace ι ((a.card : ℤ)-2), ∀ x : EuclideanSpace ℝ ι,
      weightedSpherePowerMoment
        (fun y : KernelSphere (EuclideanSpace ℝ ι) => ambientMultisetMonomial a y)
        (N-a.card) x = sphereMixedPowerCoefficient ι N a.card*ambientMultisetMonomial a x*
          (‖x‖^2)^(N/2-a.card)+R x := by
  have hmain : ∀ a : Multiset ι, a.card ≤ N →
      ∃ R ∈ radialPolynomialSpace ι ((a.card : ℤ)-2), ∀ x : EuclideanSpace ℝ ι,
        weightedSpherePowerMoment
          (fun y : KernelSphere (EuclideanSpace ℝ ι) => ambientMultisetMonomial a y)
          (N-a.card) x = sphereMixedPowerCoefficient ι N a.card*ambientMultisetMonomial a x*
            (‖x‖^2)^(N/2-a.card)+R x := by
    intro a
    induction a using Multiset.induction_on with
    | empty =>
      intro _
      refine ⟨0, Submodule.zero_mem _, fun x => ?_⟩
      simpa only [Multiset.card_zero, Nat.sub_zero, ambientMultisetMonomial,
        Multiset.map_zero, Multiset.prod_zero, mul_one, sphereMixedPowerCoefficient,
        Pi.zero_apply, add_zero, weightedSpherePowerMoment, one_mul, sphereInnerPowerMoment] using
        sphereInnerPowerMoment_eq_baseCoefficient (ι := ι) N x
    | @cons i a IH =>
      intro hA
      have hkN : a.card < N := by simp only [Multiset.card_cons] at hA; omega
      obtain ⟨R,hR,hid⟩ := IH (by omega)
      obtain ⟨g,hg,hgderiv⟩ := radialPolynomialSpace_line_derivative hR i
      rw [show (a.card : ℤ)-2+1=(a.card : ℤ)-1 by ring] at hg
      let C := sphereMixedPowerCoefficient ι N a.card
      let q := N/2-a.card
      let d : ℝ := ((N-a.card : ℕ) : ℝ)
      let Rnew := d⁻¹ • (C • radialWordDerivative a i q+g)
      have hRnew : Rnew ∈ radialPolynomialSpace ι ((a.card : ℤ)-1) :=
        Submodule.smul_mem _ _ (Submodule.add_mem _
          (Submodule.smul_mem _ _ (radialWordDerivative_mem a i q)) hg)
      refine ⟨Rnew, ?_, fun x => ?_⟩
      · have hcap : (((i ::ₘ a).card : ℤ)-2)=(a.card : ℤ)-1 := by
          simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one]
          ring
        rw [hcap]
        exact hRnew
      · have hN : N-a.card-1+1=N-a.card := by omega
        have hncast : ((N-a.card-1 : ℕ):ℝ)+1=d := by dsimp [d]; exact_mod_cast hN
        have hnexp : N-a.card-1=N-(a.card+1) := by omega
        have hweight : (fun y : KernelSphere (EuclideanSpace ℝ ι) =>
            ambientMultisetMonomial a y*inner ℝ (EuclideanSpace.basisFun ι ℝ i) (y : EuclideanSpace ℝ ι)) =
            (fun y : KernelSphere (EuclideanSpace ℝ ι) => ambientMultisetMonomial (i ::ₘ a) y) := by
          funext y
          rw [EuclideanSpace.basisFun_inner, ambientMultisetMonomial_cons]
          ring
        have hleft := hasDerivAt_weightedSpherePower_add_smul
          (fun y : KernelSphere (EuclideanSpace ℝ ι) => ambientMultisetMonomial a y)
          ((ambientMultisetMonomial_continuous a).comp continuous_subtype_val)
          (N-a.card-1) x (EuclideanSpace.basisFun ι ℝ i)
        rw [hN, hncast, hweight, hnexp] at hleft
        have hn := hasDerivAt_norm_sq_add_smul x (EuclideanSpace.basisFun ι ℝ i)
        rw [real_inner_comm, EuclideanSpace.basisFun_inner] at hn
        have hright := (((hasDerivAt_ambientMultisetMonomial_add_basis a i x).fun_mul
          (hn.fun_pow q)).const_mul C).add (hgderiv x)
        simp only [zero_smul, add_zero] at hright
        have hEq (c : ℝ) : weightedSpherePowerMoment
            (fun y : KernelSphere (EuclideanSpace ℝ ι) => ambientMultisetMonomial a y)
            (N-a.card) (x+c • EuclideanSpace.basisFun ι ℝ i) =
            C*(ambientMultisetMonomial a (x+c • EuclideanSpace.basisFun ι ℝ i)*
              (‖x+c • EuclideanSpace.basisFun ι ℝ i‖^2)^q)+
              R (x+c • EuclideanSpace.basisFun ι ℝ i) := by
          rw [hid]
          dsimp only [C,q]
          ring
        have hright' := hright.congr_of_eventuallyEq (Filter.Eventually.of_forall hEq)
        have he := hleft.unique hright'
        have hd : 0 < d := Nat.cast_pos.mpr (by dsimp [d] at *; omega)
        have hd' : ((N-a.card : ℕ):ℝ) ≠ 0 := hd.ne'
        have hpExp : N/2-a.card-1=N/2-(a.card+1) := by omega
        rw [Multiset.card_cons]
        apply mul_left_cancel₀ hd.ne'
        calc
          _ = C*((a.count i : ℝ)*ambientMultisetMonomial (a.erase i) x*(‖x‖^2)^q+
              ambientMultisetMonomial a x*((q:ℝ)*(‖x‖^2)^(q-1)*(2*x i)))+g x := he
          _ = _ := by
            rw [sphereMixedPowerCoefficient, ambientMultisetMonomial_cons]
            dsimp [Rnew, C, q, d, radialWordDerivative, radialWordMonomial]
            rw [← hpExp]
            field_simp [hd']
            ring
  exact hmain a hA

end ActualSphereMoments

end
end KernelSeq
