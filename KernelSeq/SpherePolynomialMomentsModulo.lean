import KernelSeq.RadialPolynomialJets
import KernelSeq.SpherePolynomialFiltration
import KernelSeq.FeatureEmbedding
import KernelSeq.CompactCovariance

/-!
# Actual spherical polynomial moments modulo lower-degree polynomials

Ambient radial remainders are restricted only after the genuine derivative
calculation. Their L2 classes lie in the actual polynomial filtration. Thus
every repeated-word monomial kernel has its constructed degree coefficient
as scalar principal part, with a proved lower-degree remainder.
-/

namespace KernelSeq

open MeasureTheory Submodule Set
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem radialPolynomialSpace_restrict_exists
    {p : ℤ} {n : ℕ} (hpn : p ≤ (n : ℤ)) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : f ∈ radialPolynomialSpace ι p) :
    ∃ v ∈ spherePolynomialSpace ι n,
      v =ᵐ[uniformSphere (E := EuclideanSpace ℝ ι)] (fun x => f x) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a,l,ha,rfl⟩ := hf
    let s : Sym ι a.card := ⟨a,rfl⟩
    have hcard : a.card ≤ n := by exact_mod_cast ha.trans hpn
    have hv : sphereSymLp s ∈ spherePolynomialSpace ι n :=
      homogeneousSpherePolynomialSpace_le_filtration hcard
        (Submodule.subset_span (Set.mem_range_self s))
    refine ⟨sphereSymLp s,hv,?_⟩
    filter_upwards [(sphereMultisetMonomial_memLp a).coeFn_toLp] with x hx
    change (sphereSymLp s) x = sphereMultisetMonomial a x at hx
    rw [hx]
    have hnorm : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    simp only [radialWordMonomial, hnorm, one_pow, mul_one]
    rfl
  | zero =>
    refine ⟨0,Submodule.zero_mem _,?_⟩
    exact Lp.coeFn_zero _ _ _
  | add f g hf hg IHf IHg =>
    obtain ⟨v,hv,hveq⟩ := IHf
    obtain ⟨w,hw,hweq⟩ := IHg
    refine ⟨v+w,Submodule.add_mem _ hv hw,?_⟩
    filter_upwards [Lp.coeFn_add v w,hveq,hweq] with x hx hvx hwx
    rw [hx]
    change v x+w x = f x+g x
    rw [hvx,hwx]
  | smul c f hf IH =>
    obtain ⟨v,hv,hveq⟩ := IH
    refine ⟨c • v,Submodule.smul_mem _ c hv,?_⟩
    filter_upwards [Lp.coeFn_smul c v,hveq] with x hx hvx
    rw [hx]
    change c*v x = c*f x
    rw [hvx]

section Feature
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual bounded prediction covariance of a monomial Gram kernel
acts on every repeated-coordinate degree-m monomial by the true scalar
coefficient modulo an actual lower polynomial space. -/
theorem predictionCovariance_sphereSymLp_mod_polynomial
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (j : ℕ) (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      inner ℝ (k x) (k y) = inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)^j)
    {m : ℕ} (a : Sym ι m) :
    predictionCovariance (featureEmbedding uniformSphere k hk) (sphereSymLp a)-
      sphereMixedPowerCoefficient ι (j+m) m • sphereSymLp a ∈ spherePolynomialSpace ι (m-2) := by
  let S := featureEmbedding uniformSphere k hk
  let v := sphereSymLp a
  let C := sphereMixedPowerCoefficient ι (j+m) m
  obtain ⟨R,hR,hpoint⟩ := weightedSpherePowerMoment_multiset_mod_radial (ι := ι)
    (j+m) a.val (by rw [a.property]; omega)
  rw [a.property] at hR
  obtain ⟨vR,hvR,hvReq⟩ := radialPolynomialSpace_restrict_exists (by omega :
    (m:ℤ)-2 ≤ ((m-2 : ℕ):ℤ)) hR
  have hact (x : KernelSphere (EuclideanSpace ℝ ι)) :
      inner ℝ (k x) (S.adjoint v) = C*ambientMultisetMonomial a.val x+R x := by
    rw [featureEmbedding_adjoint_pairing]
    calc
      _ = weightedSpherePowerMoment
          (fun y : KernelSphere (EuclideanSpace ℝ ι) => ambientMultisetMonomial a.val y) j x := by
        unfold weightedSpherePowerMoment
        apply integral_congr_ae
        filter_upwards [(sphereMultisetMonomial_memLp a.val).coeFn_toLp] with y hy
        change v y = sphereMultisetMonomial a.val y at hy
        rw [hy,hkernel]
        rw [real_inner_comm (y : EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι)]
        dsimp only [sphereMultisetMonomial,ambientMultisetMonomial]
        ring
      _ = _ := by
        have hh := hpoint (x : EuclideanSpace ℝ ι)
        have hnorm : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
        simpa only [a.property,Nat.add_sub_cancel,hnorm,one_pow,mul_one] using hh
  have heq : predictionCovariance S v = C • v+vR := by
    change S (S.adjoint v) = _
    apply Lp.ext
    filter_upwards [featureEmbedding_ae uniformSphere k hk (S.adjoint v),
      Lp.coeFn_add (C • v) vR,Lp.coeFn_smul C v,
      (sphereMultisetMonomial_memLp a.val).coeFn_toLp,hvReq] with x hx hadd hsmul hva hvr
    change v x = sphereMultisetMonomial a.val x at hva
    rw [hx,hact,hadd]
    change C*ambientMultisetMonomial a.val x+R x = (C • v) x+vR x
    rw [hsmul]
    change C*ambientMultisetMonomial a.val x+R x = C*v x+vR x
    rw [hva,hvr]
    rfl
  change predictionCovariance S v-C • v ∈ _
  rw [heq,add_sub_cancel_left]
  exact hvR

end Feature
end
end KernelSeq
