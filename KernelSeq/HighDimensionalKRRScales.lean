import KernelSeq.HighDimensionalPhaseLimits
import KernelSeq.SphericalRetainedScaleVerification
import KernelSeq.SphereZonalAsymptotics

/-!
# The original comparison scales for high-dimensional ridge

The degree-p block supplies the variance-dimension lower bound. The
ordinary trace bound suffices for N and the true spherical leverage.
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology ContDiff
noncomputable section

def highDimensionalRidgeExponent (s γ : ℝ) : ℝ :=
  (highDimensionalDegree s γ : ℝ) + min (highDimensionalRemainder s γ) s / 2

theorem dimensionPower_isBigO {J : Type*} {l : Filter J} {d : J → ℝ} {a b : ℝ}
    (hd : Tendsto d l atTop) (hab : a ≤ b) :
    (fun i => d i^a) =O[l] (fun i => d i^b) := by
  apply IsBigO.of_bound 1
  filter_upwards [hd.eventually (eventually_ge_atTop (1 : ℝ))] with i hi
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) _),
    one_mul] using Real.rpow_le_rpow_of_exponent_le hi hab

theorem dimensionSample_isTheta {J : Type*} {l : Filter J} {d n : J → ℝ} {γ η : ℝ}
    (hη : 0 < η) (h : Tendsto (fun i => n i / d i^γ) l (𝓝 η)) :
    n =Θ[l] (fun i => d i^γ) :=
  (isTheta_of_div_tendsto_nhds_ne_zero h hη.ne').symm

theorem dimensionPower_isTheta_samplePower {J : Type*} {l : Filter J} {d n : J → ℝ}
    {γ : ℝ} (hγ : 0 < γ) (hd : ∀ i, 0 < d i) (hn : ∀ i, 0 ≤ n i)
    (h : n =Θ[l] (fun i => d i^γ)) (r : ℝ) :
    (fun i => d i^r) =Θ[l] (fun i => n i^(r/γ)) := by
  have hh := IsTheta.rpow (r := r/γ) (Eventually.of_forall hn)
    (Eventually.of_forall fun i => Real.rpow_nonneg (hd i).le γ) h
  have heq (i : J) : (d i^γ)^(r/γ) = d i^r := by
    rw [← Real.rpow_mul (hd i).le]
    congr 1
    field_simp
  simpa only [heq] using hh.symm

theorem ridge_retains_degree_of_dimension_schedule {J : Type*} {l : Filter J}
    (ι : J → Type*) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (Φ : ℝ → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (p : ℕ) (hp : 0 < a p) {b : ℝ} (hb : (p : ℝ) ≤ b)
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hreg : lam =O[l] (fun i => (Fintype.card (ι i) : ℝ)^(-b))) :
    ∃ q0 > 0, ∀ᶠ i in l, q0 ≤ ResidualFilter.shrinkage (ResidualFilter.ridge (lam i))
      (zonalSphereDegreeValue (ι := ι i) a p) := by
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let μ := fun i => zonalSphereDegreeValue (ι := ι i) a p
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hμ := zonalSphereDegreeValue_ratio_tendsto ι a ha Φ hseries hΦ p hp hd
  have hμθ : μ =Θ[l] (fun i => d i^(-(p : ℝ))) := by
    have hpos : 0 < a p * (p.factorial : ℝ) := mul_pos hp (by positivity)
    exact (isTheta_of_div_tendsto_nhds_ne_zero hμ one_ne_zero).symm.trans
      ((isTheta_const_mul_left hpos.ne').mpr (isTheta_refl _ _))
  have hlμ := (hreg.trans (dimensionPower_isBigO hdR (by linarith : -b ≤ -(p : ℝ)))).trans hμθ.symm.isBigO
  obtain ⟨C, hC0, hC⟩ := hlμ.exists_pos
  have hμpos : ∀ᶠ i in l, 0 < μ i := by
    filter_upwards [hd.eventually (eventually_ge_atTop p)] with i hi
    exact zonalSphereDegreeValue_pos a ha Φ hseries p hi hp
  refine ⟨1/(1+C), by positivity, ?_⟩
  filter_upwards [hC.bound, hμpos] with i hi hpi
  have hh : lam i ≤ C*μ i := by
    change ‖lam i‖ ≤ C * ‖μ i‖ at hi
    simpa only [Real.norm_eq_abs, abs_of_pos (hlam i), abs_of_pos hpi] using hi
  unfold ResidualFilter.shrinkage ResidualFilter.ridge
  change 1/(1+C) ≤ μ i * (1/(μ i+lam i))
  rw [mul_one_div]
  exact (div_le_div_iff₀ (by positivity) (add_pos hpi (hlam i))).mpr (by linarith)

universe uJ uI uH
variable {J : Type uJ} {l : Filter J}
    (ι : J → Type uI) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (H : J → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]

theorem spherical_highDimensionalRidge_original_scales
    {κ s R γ η : ℝ}
    (Φ : ℝ → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R) (hγ : s+1 ≤ γ) (hη : 0 < η)
    (n : J → ℕ) (hn : ∀ i, 0 < n i)
    (f : ∀ i, Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ (ι i))))
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hnschedule : Tendsto (fun i => (n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) l (𝓝 η))
    (hreg : lam =Θ[l] (fun i => (Fintype.card (ι i) : ℝ)^(-highDimensionalRidgeExponent s γ)))
    (hsource : ∀ᶠ i in l, f i ∈ featureSourceBall (rkhsFeature (H := H i))
      (zonalSphereFeature_memLp Φ hΦ.continuousOn (hkernel i)) s hs.le R) :
    let model := fun i => sphericalScaleModel Φ hΦ.continuousOn (hkernel i) hκ hdiag
      (n i) (hn i) (f i) (lam i) (hlam i) (ResidualFilter.ridge (lam i))
      (ResidualFilter.ridge_spectralFilter (hlam i)) (ResidualFilter.ridge_contract (hlam i))
    (∀ᶠ i in l, 0 < (model i).Q) ∧
      Tendsto (fun i => (model i).compatibility) l (𝓝 0) ∧
      Tendsto (fun i => (model i).sourceBalance) l (𝓝 0) ∧
      Tendsto (fun i => (model i).expectationScale) l (𝓝 0) := by
  intro model
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let p := highDimensionalDegree s γ
  let b := highDimensionalRidgeExponent s γ
  have hp := (highDimensionalDegree_bounds hs hγ).1
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨hpb,hbγ,hcompat,hsourceExp⟩ := highDimensionalKRR_exponent_inequalities hs hs1 hγ
  change (p : ℝ) ≤ b at hpb
  change b < γ at hbγ
  change 3*b-2*(p : ℝ) < γ at hcompat
  change b*(1-s)-(p : ℝ) < 0 at hsourceExp
  have hb0 : 0 < b := hp0.trans_le hpb
  have hγ0 : 0 < γ := by linarith
  have hdP (i : J) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hnP (i : J) : 0 ≤ (n i : ℝ) := Nat.cast_nonneg _
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hnθ := dimensionSample_isTheta hη hnschedule
  have hnInf := spherical_sample_tendsto_atTop hγ0 hdR (fun i => (hdP i).le) hnP hnθ
  obtain ⟨q0,hq0,hret⟩ := ridge_retains_degree_of_dimension_schedule
    ι Φ a (fun j => (ha j).le) hseries hΦ p (ha p) hpb lam hlam hd hreg.isBigO
  have hdim : ∀ᶠ i in l, 2*p ≤ Fintype.card (ι i) :=
    hd.eventually (eventually_ge_atTop (2*p))
  have hbounds : ∀ᶠ i in l, 0 < (model i).Q ∧ ((model i).Q)⁻¹ ≤
      (2^p*(p.factorial : ℝ)/q0^2)*d i^(-(p : ℝ)) := by
    filter_upwards [hdim,hret] with i hi hr
    exact sphericalScaleModel_retained_inverse_filter_dimension_bound Φ hΦ.continuousOn
      (hkernel i) hκ hdiag (n i) (hn i) (f i) (lam i) (hlam i) _
      (ResidualFilter.ridge_spectralFilter (hlam i)) (ResidualFilter.ridge_contract (hlam i))
      a (fun j => (ha j).le) hseries p (ha p) hi hq0 hr
  have hQpos := hbounds.mono fun _ hi => hi.1
  have hQdim : (fun i => ((model i).Q)⁻¹) =O[l] (fun i => d i^(-(p : ℝ))) := by
    apply IsBigO.of_bound (2^p*(p.factorial : ℝ)/q0^2)
    filter_upwards [hbounds] with i hi
    simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hi.1),
      abs_of_nonneg (Real.rpow_nonneg (hdP i).le _)] using hi.2
  have hQpow := IsTheta.rpow (r := (p : ℝ)/b) (Eventually.of_forall fun i => (hlam i).le)
    (Eventually.of_forall fun i => Real.rpow_nonneg (hdP i).le (-b)) hreg
  have heq (i : J) : (d i^(-b))^((p : ℝ)/b) = d i^(-(p : ℝ)) := by
    rw [← Real.rpow_mul (hdP i).le]
    congr 1
    field_simp
  have hQ : (fun i => ((model i).Q)⁻¹) =O[l] (fun i => (model i).lam^((p : ℝ)/b)) := by
    change (fun i => ((model i).Q)⁻¹) =O[l] (fun i => lam i^((p : ℝ)/b))
    exact hQdim.trans (by simpa only [heq] using hQpow.symm.isBigO)
  have hN : (fun i => (model i).N) =O[l] (fun i => (model i).lam^(-(1:ℝ))) := by
    apply IsBigO.of_bound (κ^2)
    filter_upwards [] with i
    have hh := sphericalScaleModel_dimension_le_trace Φ hΦ.continuousOn (hkernel i) hκ hdiag
      (n i) (hn i) (f i) (lam i) (hlam i) _ (ResidualFilter.ridge_spectralFilter (hlam i))
      (ResidualFilter.ridge_contract (hlam i))
    change (model i).N ≤ κ^2/(model i).lam at hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg (model i).N_nonneg, Real.rpow_neg_one,
      abs_of_pos (inv_pos.mpr (model i).lambda_pos), div_eq_mul_inv] using hh
  have hL := universal_leverage_isBigO (l := l) model
  have hsource' : ∀ᶠ i in l, (model i).f ∈ (model i).SourceBall s hs.le R := hsource
  have hS := source_ball_energy_isBigO model hs.le hR.le hsource'
  have hS' : (fun i => (model i).S) =O[l] (fun i => (model i).lam^s) := by
    simpa [residualComparisonOrder, min_eq_left hs1] using hS
  have hrow : ∀ᶠ i in l, 0 < (model i).lam ∧ 0 ≤ (model i).N ∧
      0 < (model i).Q ∧ 0 ≤ (model i).L := by
    filter_upwards [hQpos] with i hi
    exact ⟨(model i).lambda_pos, (model i).N_nonneg, hi, (model i).L_nonneg⟩
  have hregTheta : (fun i => (model i).lam) =Θ[l] (fun i => (n i : ℝ)^(-(b/γ))) := by
    change lam =Θ[l] (fun i => (n i : ℝ)^(-(b/γ)))
    simpa only [neg_div] using hreg.trans (dimensionPower_isTheta_samplePower hγ0 hdP hnP hnθ (-b))
  have hc : b/γ*(2*1+1-2*((p : ℝ)/b)) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hγ0, one_mul]
    have he : b * (2*1+1-2*((p : ℝ)/b)) = 3*b-2*(p : ℝ) := by
      field_simp
      ring
    rw [he]
    exact hcompat
  have hz : 0 < s + (p : ℝ)/b - 1 := by
    have h := (lt_div_iff₀ hb0).mpr (show (1-s)*b < (p : ℝ) by nlinarith)
    linarith
  have hall := original_three_scales_of_power_bounds
    (fun i => ((model i).n : ℝ)) (fun i => (model i).lam) (fun i => (model i).N)
    (fun i => (model i).Q) (fun i => (model i).L) (fun i => (model i).S)
    hnInf (div_pos hb0 hγ0) (p := 1) (q := (p : ℝ)/b) (ellExp := 1) (by norm_num)
    hrow hregTheta hN hQ hL hS' hc hz (by simpa using (div_lt_one hγ0).mpr hbγ)
  exact ⟨hQpos, hall⟩

end
end KernelSeq
