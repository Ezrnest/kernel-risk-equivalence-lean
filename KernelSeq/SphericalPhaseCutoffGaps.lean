import KernelSeq.SphericalPhaseCutoffModel
import KernelSeq.HighDimensionalPhaseLimits

/-!
# Separation of the actual spherical degrees at the cutoff

Finite fixed-degree comparisons and a uniform upper bound on all higher
degrees together yield the actual eventual spectral plateaus.
-/

namespace KernelSeq
open Filter Set
open scoped Topology ContDiff
noncomputable section

variable {J : Type*} {l : Filter J}
  (ι : J → Type*) [∀ i, Fintype (ι i)] [∀ i, Nonempty (ι i)]
  (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
  (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j * t^j) (Φ t))
  (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
  (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)

include ha hseries hΦ hd in
theorem zonalSphereDegreeValue_eventually_mul_le
    {j k : ℕ} (hjk : j < k) (C : ℝ) :
    ∀ᶠ i in l, C*zonalSphereDegreeValue (ι := ι i) a k ≤
      zonalSphereDegreeValue (ι := ι i) a j := by
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let μ := fun (m : ℕ) i => zonalSphereDegreeValue (ι := ι i) a m
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hd0 (i : J) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hscaled (m : ℕ) :
      Tendsto (fun i => d i^(m : ℝ)*μ m i) l (𝓝 (a m*(m.factorial : ℝ))) := by
    simpa only [Real.rpow_natCast, mul_comm] using
      zonalSphereDegreeValue_scaled_tendsto ι a (fun m => (ha m).le) Φ hseries hΦ m hd
  have hsmall := dimensionPower_rescale_tendsto_zero hdR hd0
    (show (j : ℝ) < (k : ℝ) by exact_mod_cast hjk) (hscaled k)
  have h0 : 0 < a j*(j.factorial : ℝ) := mul_pos (ha j) (by positivity)
  have hcmp := (hsmall.const_mul C).eventually_lt (hscaled j)
    (by simpa only [mul_zero] using h0)
  filter_upwards [hcmp] with i hi
  have hh : d i^(j : ℝ)*(C*μ k i) < d i^(j : ℝ)*μ j i := by
    simpa only [mul_left_comm] using hi
  exact (lt_of_mul_lt_mul_left hh (Real.rpow_nonneg (hd0 i).le _)).le

include ha hseries hΦ hd in
theorem zonalSphereDegreeValue_eventually_tail_le_succ (p : ℕ) :
    ∀ᶠ i in l, ∀ j > p, zonalSphereDegreeValue (ι := ι i) a j ≤
      zonalSphereDegreeValue (ι := ι i) a (p+1) := by
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let C := zonalDegreeMomentConstant a (p+2)
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hd0 (i : J) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hsmall : Tendsto (fun i => C / d i) l (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hdR).const_mul C
  have hlim := zonalSphereDegreeValue_scaled_tendsto ι a (fun j => (ha j).le)
    Φ hseries hΦ (p+1) hd
  have hpos : 0 < a (p+1)*((p+1).factorial : ℝ) := mul_pos (ha _) (by positivity)
  filter_upwards [hsmall.eventually_lt hlim hpos] with i hi j hj
  by_cases he : j=p+1
  · subst j; exact le_rfl
  have htop := zonalSphereDegreeValue_uniform_upper (ι := ι i) a
    (fun j => (ha j).le) Φ hseries hΦ j (p+2) (by omega)
  have hh : C/(d i)^(p+2) ≤ zonalSphereDegreeValue (ι := ι i) a (p+1) := by
    rw [pow_succ _ (p+1), mul_comm, ← div_div]
    apply (div_le_iff₀ (pow_pos (hd0 i) _)).mpr
    exact hi.le
  exact htop.trans hh

include ha hseries hΦ hd in
/-- Both eventual plateaus, and the maximum omitted degree value, for the
actual degree sequence; no finite-rank approximation or gap certificate. -/
theorem spherical_phaseCutoff_gaps (p : ℕ) :
    ∀ᶠ i in l,
      (∀ j < p, 2*zonalSphereDegreeValue (ι := ι i) a p ≤
        zonalSphereDegreeValue (ι := ι i) a j) ∧
      2*zonalSphereDegreeValue (ι := ι i) a (p+1) ≤
        zonalSphereDegreeValue (ι := ι i) a p ∧
      (∀ j > p, zonalSphereDegreeValue (ι := ι i) a j ≤
        zonalSphereDegreeValue (ι := ι i) a (p+1)) := by
  have hlow : ∀ᶠ i in l, ∀ j : Fin p, 2*zonalSphereDegreeValue (ι := ι i) a p ≤
      zonalSphereDegreeValue (ι := ι i) a j :=
    eventually_all.mpr fun j => zonalSphereDegreeValue_eventually_mul_le
      ι a ha Φ hseries hΦ hd j.isLt 2
  filter_upwards [hlow, zonalSphereDegreeValue_eventually_mul_le ι a ha Φ hseries hΦ hd
    (Nat.lt_succ_self p) 2, zonalSphereDegreeValue_eventually_tail_le_succ ι a ha Φ hseries hΦ hd p]
    with i hi hj hk
  exact ⟨fun j hjp => hi ⟨j,hjp⟩,hj,hk⟩

end
end KernelSeq
