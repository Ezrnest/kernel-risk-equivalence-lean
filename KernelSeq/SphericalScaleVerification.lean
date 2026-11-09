import KernelSeq.SphericalScaleBounds
import KernelSeq.PowerScaleVerification

/-!
# Original three scales for actual high-dimensional spherical kernels

The design spaces, RKHSs and targets may change with the index. The only
kernel data are the original common continuous zonal profile, its convergent
positive power expansion, and its literal RKHS kernel identity. The genuine
spherical block, covariance count and leverage estimates are all supplied
internally. This first result covers the small-c schedule λ=c d^(-m); the
more general condition at the exact degree-m eigenvalue is not asserted.
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology
noncomputable section

section Schedule
variable {J : Type*} {l : Filter J} {d n : J → ℝ}

theorem spherical_sample_tendsto_atTop {γ : ℝ} (hγ : 0 < γ)
    (hd : Tendsto d l atTop) (hd0 : ∀ i, 0 ≤ d i) (hn0 : ∀ i, 0 ≤ n i)
    (hschedule : n =Θ[l] (fun i => d i^γ)) : Tendsto n l atTop := by
  have hp := (tendsto_rpow_atTop hγ).comp hd
  have hpn : Tendsto (fun i => ‖d i^γ‖) l atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hd0 _) _)] using hp
  have hn := hschedule.tendsto_norm_atTop_iff.mpr hpn
  simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (hn0 _)] using hn

/-- The original sample-vs-dimension schedule gives exactly the regularization
comparison needed by the general scalar engine. -/
theorem spherical_regularization_theta {γ c : ℝ} (hγ : 0 < γ) (hc : 0 < c)
    (hd0 : ∀ i, 0 < d i) (hn0 : ∀ i, 0 ≤ n i)
    (hschedule : n =Θ[l] (fun i => d i^γ)) (m : ℕ) :
    (fun i => c * d i^(-(m : ℝ))) =Θ[l] (fun i => n i^(-((m : ℝ)/γ))) := by
  have hh := IsTheta.rpow (r := -((m : ℝ)/γ))
    (Eventually.of_forall hn0)
    (Eventually.of_forall fun i => Real.rpow_nonneg (hd0 i).le γ) hschedule
  have heq (i : J) : (d i^γ)^(-((m : ℝ)/γ)) = d i^(-(m : ℝ)) := by
    rw [← Real.rpow_mul (hd0 i).le]
    congr 1
    field_simp
  apply (isTheta_const_mul_left hc.ne').mpr
  simpa only [heq] using hh.symm

end Schedule

universe uJ uI uH
section ActualRows
variable {J : Type uJ} {l : Filter J} [NeBot l]
    (ι : J → Type uI) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (H : J → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]
    {κ ρ A : ℝ}
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (n : J → ℕ) (hn : ∀ i, 0 < n i)
    (f : ∀ i, Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ (ι i))))
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i) (φ : J → ℝ → ℝ)
    (hf : ∀ i, ResidualFilter.SpectralFilter (κ^2) (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) (κ^2) ρ A (φ i))

/-- The manuscript's actual high-dimensional small-c assertion, including
all three original scales. The same statement over a product filter is
uniform in every additional target or model parameter. -/
theorem spherical_sourceBall_original_scales
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    {γ s R c : ℝ} (m : ℕ) (hm : 0 < m) (hmγ : (m : ℝ) < γ)
    (_ham : 0 < a m) (hs : 0 < s) (hR : 0 < R)
    (hc0 : 0 < c) (hc : c ≤ sphericalSmallScaleConstant m (a m) ρ A)
    (hd : Tendsto (fun i => (Fintype.card (ι i) : ℝ)) l atTop)
    (hnschedule : (fun i => (n i : ℝ)) =Θ[l]
      (fun i => (Fintype.card (ι i) : ℝ)^γ))
    (hreg : ∀ i, lam i = c * (Fintype.card (ι i) : ℝ)^(-(m : ℝ)))
    (hsource : ∀ᶠ i in l, f i ∈ featureSourceBall (rkhsFeature (H := H i))
      (zonalSphereFeature_memLp Φ hΦ (hkernel i)) s hs.le R) :
    let model := fun i => sphericalScaleModel Φ hΦ (hkernel i) hκ hdiag
      (n i) (hn i) (f i) (lam i) (hlam i) (φ i) (hf i) (h i)
    (∀ᶠ i in l, 0 < (model i).Q) ∧
      Tendsto (fun i => (model i).compatibility) l (𝓝 0) ∧
      Tendsto (fun i => (model i).sourceBalance) l (𝓝 0) ∧
      Tendsto (fun i => (model i).expectationScale) l (𝓝 0) := by
  dsimp only
  let model := fun i => sphericalScaleModel Φ hΦ (hkernel i) hκ hdiag
    (n i) (hn i) (f i) (lam i) (hlam i) (φ i) (hf i) (h i)
  have hdP (i : J) : 0 < (Fintype.card (ι i) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hnP (i : J) : 0 ≤ (n i : ℝ) := Nat.cast_nonneg _
  have hγ : 0 < γ := (Nat.cast_pos.mpr hm).trans hmγ
  have hnInf := spherical_sample_tendsto_atTop hγ hd (fun i => (hdP i).le) hnP hnschedule
  have hregTheta : (fun i => (model i).lam) =Θ[l]
      (fun i => ((model i).n : ℝ)^(-((m : ℝ)/γ))) := by
    simpa only [model, sphericalScaleModel, hreg] using
      spherical_regularization_theta hγ hc0 hdP hnP hnschedule m
  have hdim : ∀ᶠ i in l, 2*m ≤ Fintype.card (ι i) := by
    filter_upwards [hd.eventually (eventually_ge_atTop ((2*m : ℕ) : ℝ))] with i hi
    exact_mod_cast hi
  have hbounds : ∀ᶠ i in l, 0 < (model i).Q ∧
      ((model i).Q)⁻¹ ≤ (4 * 2^m * (m.factorial : ℝ) / c) * (model i).lam := by
    filter_upwards [hdim] with i hi
    exact sphericalScaleModel_inverse_filter_dimension_bound Φ hΦ (hkernel i) hκ hdiag
      (n i) (hn i) (f i) (lam i) (hlam i) (φ i) (hf i) (h i) a ha hseries m hc0 hc (hreg i) hi
  have hQpos := hbounds.mono fun _ hi => hi.1
  have hQ : (fun i => ((model i).Q)⁻¹) =O[l] (fun i => (model i).lam^(1 : ℝ)) := by
    apply IsBigO.of_bound (4 * 2^m * (m.factorial : ℝ) / c)
    filter_upwards [hbounds] with i hi
    simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hi.1), Real.rpow_one,
      abs_of_pos (model i).lambda_pos] using hi.2
  have hN : (fun i => (model i).N) =O[l] (fun i => (model i).lam^(-(1 : ℝ))) := by
    apply IsBigO.of_bound (κ^2)
    filter_upwards [] with i
    have hh := sphericalScaleModel_dimension_le_trace Φ hΦ (hkernel i) hκ hdiag
      (n i) (hn i) (f i) (lam i) (hlam i) (φ i) (hf i) (h i)
    change (model i).N ≤ κ^2 / (model i).lam at hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg (model i).N_nonneg, Real.rpow_neg_one,
      abs_of_pos (inv_pos.mpr (model i).lambda_pos), div_eq_mul_inv] using hh
  have hL := universal_leverage_isBigO (l := l) model
  have hsource' : ∀ᶠ i in l, (model i).f ∈ (model i).SourceBall s hs.le R := hsource
  have hS := source_ball_energy_isBigO model hs.le hR.le hsource'
  obtain ⟨i0, _⟩ := hQpos.exists
  have hα := residualComparisonOrder_pos (h i0).rho_pos
  have hrow : ∀ᶠ i in l, 0 < (model i).lam ∧ 0 ≤ (model i).N ∧ 0 < (model i).Q ∧ 0 ≤ (model i).L := by
    filter_upwards [hQpos] with i hi
    exact ⟨(model i).lambda_pos, (model i).N_nonneg, hi, (model i).L_nonneg⟩
  have hθ : 0 < (m : ℝ)/γ := div_pos (Nat.cast_pos.mpr hm) hγ
  have hθ1 : (m : ℝ)/γ < 1 := (div_lt_one hγ).mpr hmγ
  have hall := original_three_scales_of_power_bounds
    (fun i => ((model i).n : ℝ)) (fun i => (model i).lam) (fun i => (model i).N)
    (fun i => (model i).Q) (fun i => (model i).L) (fun i => (model i).S)
    hnInf hθ (p := 1) (q := 1) (ellExp := 1) (by norm_num) hrow hregTheta hN hQ hL hS
    (by simpa using hθ1) (by simpa using lt_min hs hα) (by simpa using hθ1)
  refine ⟨hQpos, ?_⟩
  simpa only [SpectralScaleModel.compatibility, SpectralScaleModel.sourceBalance,
    SpectralScaleModel.expectationScale] using hall

end ActualRows
end
end KernelSeq
