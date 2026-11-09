import KernelSeq.SphericalScaleVerification
import KernelSeq.SphereZonalEigenfunctions
import KernelSeq.FiniteEigenFilterDimension

/-!
# General spherical regularization schedules retaining the degree-m block

The original retention condition is imposed only on the actual degree-m
eigenvalue and original shrinkage. Its multiplicity and the lower bound on
the actual variance dimension are proved internally from the constructed
squarefree eigenfunctions. No full harmonic basis or eigenvalue asymptotic
is an assumption. The original three scales then follow from the scalar
power engine.
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators
noncomputable section

section SingleRow
variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H (KernelSphere (EuclideanSpace ℝ ι)) ℝ]
  {κ ρ A : ℝ}
  (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
  (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
    rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
  (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
  (n : ℕ) (hn : 0 < n)
  (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))
  (lam : ℝ) (hlam : 0 < lam) (φ : ℝ → ℝ)
  (hf : ResidualFilter.SpectralFilter (κ^2) φ)
  (h : ResidualFilter.Contract lam (κ^2) ρ A φ)

theorem sphericalScaleModel_retained_filter_dimension_lower
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (m : ℕ) (ham : 0 < a m) (hd : m ≤ Fintype.card ι)
    {q0 : ℝ} (hq0 : 0 < q0)
    (hretain : q0 ≤ ResidualFilter.shrinkage φ (zonalSphereDegreeValue (ι := ι) a m)) :
    q0^2*((Fintype.card ι).choose m : ℝ) ≤
      (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).Q := by
  let k := rkhsFeature (H := H)
  let hk := zonalSphereFeature_memLp Φ hΦ hkernel
  let e := normalizedSquarefreeSphereLp (ι := ι) (m := m)
  let t := fun _ : SquarefreeSphereIndex ι m => zonalSphereDegreeValue (ι := ι) a m
  have ht (j : SquarefreeSphereIndex ι m) : 0 < t j :=
    zonalSphereDegreeValue_pos a ha Φ hseries m hd ham
  have heig (j : SquarefreeSphereIndex ι m) :
      predictionCovariance (featureEmbedding uniformSphere k hk) (e j) = t j • e j :=
    zonalSphereRKHS_normalized_squarefree_eigen Φ hΦ hkernel a ha hseries j
  have hsum := finitePredictionEigen_shrinkage_sum_le_filterDimension k hk e
    (normalizedSquarefreeSphereLp_orthonormal m) t ht heig φ hlam
    (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).population_bound hf h
  have heq : (∑ j : SquarefreeSphereIndex ι m, (ResidualFilter.shrinkage φ (t j))^2) =
      ((Fintype.card ι).choose m : ℝ)*
        (ResidualFilter.shrinkage φ (zonalSphereDegreeValue (ι := ι) a m))^2 := by
    simp only [t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_squarefreeSphereIndex]
  rw [heq] at hsum
  have hsq := pow_le_pow_left₀ hq0.le hretain 2
  exact (show q0^2*((Fintype.card ι).choose m : ℝ) ≤
      ((Fintype.card ι).choose m : ℝ)*
        (ResidualFilter.shrinkage φ (zonalSphereDegreeValue (ι := ι) a m))^2 by
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg ((Fintype.card ι).choose m))]).trans hsum

theorem sphericalScaleModel_retained_inverse_filter_dimension_bound
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (m : ℕ) (ham : 0 < a m) (hd : 2*m ≤ Fintype.card ι)
    {q0 : ℝ} (hq0 : 0 < q0)
    (hretain : q0 ≤ ResidualFilter.shrinkage φ (zonalSphereDegreeValue (ι := ι) a m)) :
    let model := sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h
    0 < model.Q ∧ model.Q⁻¹ ≤ (2^m*(m.factorial : ℝ)/q0^2)*
      (Fintype.card ι : ℝ)^(-(m : ℝ)) := by
  dsimp only
  let Q := (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).Q
  have hraw := sphericalScaleModel_retained_filter_dimension_lower Φ hΦ hkernel hκ hdiag
    n hn f lam hlam φ hf h a ha hseries m ham (by omega) hq0 hretain
  have hdim := squarefreeSphereBlock_dimension_lower (ι := ι) m hd
  rw [squarefreeSphereBlock_finrank] at hdim
  have hcoarse : q0^2*(Fintype.card ι : ℝ)^m/(2^m*(m.factorial : ℝ)) ≤ Q := by
    have hh := mul_le_mul_of_nonneg_left hdim (sq_nonneg q0)
    have heq : q0^2*(Fintype.card ι : ℝ)^m/(2^m*(m.factorial : ℝ)) =
        q0^2*((Fintype.card ι : ℝ)^m/(2^m*(m.factorial : ℝ))) := by ring
    exact (show q0^2*(Fintype.card ι : ℝ)^m/(2^m*(m.factorial : ℝ)) ≤
      q0^2*((Fintype.card ι).choose m : ℝ) by rw [heq]; exact hh).trans hraw
  have hd0 : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hfpos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr m.factorial_pos
  have hbase : 0 < q0^2*(Fintype.card ι : ℝ)^m/(2^m*(m.factorial : ℝ)) := by positivity
  have hQ := hbase.trans_le hcoarse
  refine ⟨hQ, ?_⟩
  have hh := one_div_le_one_div_of_le hbase hcoarse
  have heq : (1 : ℝ)/(q0^2*(Fintype.card ι : ℝ)^m/(2^m*(m.factorial : ℝ))) =
      (2^m*(m.factorial : ℝ)/q0^2)*(Fintype.card ι : ℝ)^(-(m : ℝ)) := by
    rw [Real.rpow_neg hd0.le, Real.rpow_natCast]
    field_simp
  simpa only [one_div, heq] using hh

end SingleRow

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

/-- The general regularization comparison in the original spherical
proposition. The positive eventual retention is precisely its liminf
condition, expressed without assuming the desired variance dimension. -/
theorem spherical_retained_sourceBall_original_scales
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    {γ s R : ℝ} (m : ℕ) (hm : 0 < m) (hmγ : (m : ℝ) < γ)
    (ham : 0 < a m) (hs : 0 < s) (hR : 0 < R)
    (hd : Tendsto (fun i => (Fintype.card (ι i) : ℝ)) l atTop)
    (hnschedule : (fun i => (n i : ℝ)) =Θ[l] (fun i => (Fintype.card (ι i) : ℝ)^γ))
    (hreg : lam =Θ[l] (fun i => (Fintype.card (ι i) : ℝ)^(-(m : ℝ))))
    (hretain : ∃ q0 > 0, ∀ᶠ i in l, q0 ≤
      ResidualFilter.shrinkage (φ i) (zonalSphereDegreeValue (ι := ι i) a m))
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
  obtain ⟨q0, hq0, hret⟩ := hretain
  have hdP (i : J) : 0 < (Fintype.card (ι i) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hnP (i : J) : 0 ≤ (n i : ℝ) := Nat.cast_nonneg _
  have hγ : 0 < γ := (Nat.cast_pos.mpr hm).trans hmγ
  have hnInf := spherical_sample_tendsto_atTop hγ hd (fun i => (hdP i).le) hnP hnschedule
  have hdTheta : (fun i => (Fintype.card (ι i) : ℝ)^(-(m : ℝ))) =Θ[l]
      (fun i => (n i : ℝ)^(-((m : ℝ)/γ))) := by
    simpa only [one_mul] using spherical_regularization_theta hγ (by norm_num : (0:ℝ)<1)
      hdP hnP hnschedule m
  have hregTheta : (fun i => (model i).lam) =Θ[l]
      (fun i => ((model i).n : ℝ)^(-((m : ℝ)/γ))) := hreg.trans hdTheta
  have hdim : ∀ᶠ i in l, 2*m ≤ Fintype.card (ι i) := by
    filter_upwards [hd.eventually (eventually_ge_atTop ((2*m : ℕ) : ℝ))] with i hi
    exact_mod_cast hi
  have hbounds : ∀ᶠ i in l, 0 < (model i).Q ∧ ((model i).Q)⁻¹ ≤
      (2^m*(m.factorial : ℝ)/q0^2)*(Fintype.card (ι i) : ℝ)^(-(m : ℝ)) := by
    filter_upwards [hdim, hret] with i hi hri
    exact sphericalScaleModel_retained_inverse_filter_dimension_bound Φ hΦ (hkernel i) hκ hdiag
      (n i) (hn i) (f i) (lam i) (hlam i) (φ i) (hf i) (h i) a ha hseries m ham hi hq0 hri
  have hQpos := hbounds.mono fun _ hi => hi.1
  have hQdim : (fun i => ((model i).Q)⁻¹) =O[l]
      (fun i => (Fintype.card (ι i) : ℝ)^(-(m : ℝ))) := by
    apply IsBigO.of_bound (2^m*(m.factorial : ℝ)/q0^2)
    filter_upwards [hbounds] with i hi
    simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hi.1),
      abs_of_nonneg (Real.rpow_nonneg (hdP i).le _)] using hi.2
  have hQ : (fun i => ((model i).Q)⁻¹) =O[l] (fun i => (model i).lam^(1:ℝ)) := by
    simp only [Real.rpow_one]
    change (fun i => ((model i).Q)⁻¹) =O[l] lam
    exact hQdim.trans hreg.symm.isBigO
  have hN : (fun i => (model i).N) =O[l] (fun i => (model i).lam^(-(1:ℝ))) := by
    apply IsBigO.of_bound (κ^2)
    filter_upwards [] with i
    have hh := sphericalScaleModel_dimension_le_trace Φ hΦ (hkernel i) hκ hdiag
      (n i) (hn i) (f i) (lam i) (hlam i) (φ i) (hf i) (h i)
    change (model i).N ≤ κ^2/(model i).lam at hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg (model i).N_nonneg, Real.rpow_neg_one,
      abs_of_pos (inv_pos.mpr (model i).lambda_pos), div_eq_mul_inv] using hh
  have hL := universal_leverage_isBigO (l := l) model
  have hsource' : ∀ᶠ i in l, (model i).f ∈ (model i).SourceBall s hs.le R := hsource
  have hS := source_ball_energy_isBigO model hs.le hR.le hsource'
  obtain ⟨i0, _⟩ := hQpos.exists
  have hα := residualComparisonOrder_pos (h i0).rho_pos
  have hrow : ∀ᶠ i in l, 0 < (model i).lam ∧ 0 ≤ (model i).N ∧
      0 < (model i).Q ∧ 0 ≤ (model i).L := by
    filter_upwards [hQpos] with i hi
    exact ⟨(model i).lambda_pos, (model i).N_nonneg, hi, (model i).L_nonneg⟩
  have hθ : 0 < (m:ℝ)/γ := div_pos (Nat.cast_pos.mpr hm) hγ
  have hθ1 : (m:ℝ)/γ < 1 := (div_lt_one hγ).mpr hmγ
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
