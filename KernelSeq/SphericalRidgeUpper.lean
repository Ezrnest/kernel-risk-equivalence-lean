import KernelSeq.SphericalRidgeSequence

/-!
# Actual worst expected risk of spherical ridge at the original rate
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped ENNReal Topology ContDiff
noncomputable section

universe uJ uI uH
variable {J : Type uJ} {l : Filter J} [NeBot l]
    (ι : J → Type uI) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (H : J → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]
    {κ s γ η R σ : ℝ}
    (Φ : ℝ → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (n : J → ℕ) (hn : ∀ i, 0 < n i)
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)

set_option maxHeartbeats 1000000 in
theorem spherical_highDimensionalRidge_expected_upper
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hs : 0 < s) (hs1 : s ≤ 1) (hγ : s+1 ≤ γ) (hη : 0 < η) (hR : 0 < R) (hσ : 0 < σ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hnschedule : Tendsto (fun i => (n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) l (𝓝 η))
    (hreg : lam =Θ[l] (fun i => (Fintype.card (ι i) : ℝ)^(-highDimensionalRidgeExponent s γ))) :
    let b := sphericalRidgeScaleModel ι H Φ hΦ hkernel hκ hdiag n hn lam hlam
    let W := fun i => canonicalGaussianSourceWorstRisk (b i) s hs.le R hσ
    let M := fun i => (gaussianSourceMinimaxRisk (b i) s hs.le R σ).toReal
    (∀ᶠ i in l, 0 ≤ W i ∧ M i ≤ W i) ∧
      W =O[l] (fun i => (Fintype.card (ι i) : ℝ)^(-highDimensionalRiskExponent s γ)) := by
  intro b W M
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let p := highDimensionalDegree s γ
  let ζ := highDimensionalRiskExponent s γ
  let Θ := fun i => GaussianSourceIndex (b i) s hs.le R
  let m := fun (z : Σ i, Θ i) => canonicalGaussianSourceRiskRow (b z.1) hσ z.2
  let V := fun i => σ^2/(n i : ℝ)*(b i).Q
  have hΘ (i : J) : Nonempty (Θ i) := gaussianSourceIndex_nonempty (b i) hs.le hR.le
  letI : NeBot (dependentFamilyFilter l Θ) := dependentFamilyFilter_neBot hΘ
  have hfst : Tendsto Sigma.fst (dependentFamilyFilter l Θ) l := tendsto_comap
  have hreg' : (fun (z : Σ i, Θ i) => lam z.1) =Θ[dependentFamilyFilter l Θ]
      (fun z => d z.1^(-highDimensionalRidgeExponent s γ)) :=
    ⟨hreg.1.comp_tendsto hfst,hreg.2.comp_tendsto hfst⟩
  have hsc := spherical_highDimensionalRidge_original_scales (l := dependentFamilyFilter l Θ)
    (fun z => ι z.1) (fun z => H z.1) Φ hΦ (fun z => hkernel z.1) hκ hdiag
    a ha hseries hs hs1 hR hγ hη (fun z => n z.1) (fun z => hn z.1)
    (fun z => z.2.val) (fun z => lam z.1) (fun z => hlam z.1)
    (hd.comp hfst) (hnschedule.comp hfst) hreg' (Eventually.of_forall fun z => z.2.property)
  have hsc' : (∀ᶠ z in dependentFamilyFilter l Θ, 0 < (m z).scaleModel.Q) ∧
      Tendsto (fun z => (m z).scaleModel.compatibility) (dependentFamilyFilter l Θ) (𝓝 0) ∧
      Tendsto (fun z => (m z).scaleModel.sourceBalance) (dependentFamilyFilter l Θ) (𝓝 0) ∧
      Tendsto (fun z => (m z).scaleModel.expectationScale) (dependentFamilyFilter l Θ) (𝓝 0) := by
    have heq (z : Σ i, Θ i) : (m z).scaleModel =
        sphericalScaleModel Φ hΦ.continuousOn (hkernel z.1) hκ hdiag
          (n z.1) (hn z.1) z.2.val (lam z.1) (hlam z.1) (ResidualFilter.ridge (lam z.1))
          (ResidualFilter.ridge_spectralFilter (hlam z.1)) (ResidualFilter.ridge_contract (hlam z.1)) := by
      change (canonicalGaussianSourceRiskRow (b z.1) hσ z.2).scaleModel = _
      rw [canonicalGaussianSourceRiskRow_scaleModel]
      rfl
    simp only [heq]
    exact hsc
  have hu := (concreteRowRiskEquivalence_of_verified_scales m hσ
    (Eventually.of_forall fun _ => le_rfl) hsc').2.1
  have hpos : ∀ᶠ i in l, ∀ f : Θ i, 0 < (m ⟨i,f⟩).benchmark :=
    eventually_dependentFamilyFilter_iff.mp
      (hsc'.1.mono fun z hz => (m z).benchmark_pos hz)
  have hdP (i : J) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hns := dimensionSample_isTheta hη hnschedule
  have hnin := (IsTheta.rpow (r := -1) (Eventually.of_forall fun i => Nat.cast_nonneg (n i))
    (Eventually.of_forall fun i => Real.rpow_nonneg (hdP i).le γ) hns).isBigO
  have hin : (fun i => (n i : ℝ)⁻¹) =O[l] (fun i => d i^(-γ)) := by
    apply hnin.congr
    · intro i
      exact Real.rpow_neg_one _
    · intro i
      rw [← Real.rpow_mul (hdP i).le,mul_neg,mul_one]
  have hQ := spherical_ridge_Q_isBigO ι H Φ hΦ hkernel hκ hdiag n hn lam hlam
    a ha hseries hs hs1 hγ hd hreg
  have hV0 : V =O[l] (fun i => d i^((p : ℝ)-γ)) := by
    apply ((hin.mul hQ).const_mul_left (σ^2)).congr
    · intro i
      simp only [V,div_eq_mul_inv]
      ring
    · intro i
      rw [← Real.rpow_add (hdP i)]
      congr 1
      ring
  have hV := hV0.trans (dimensionPower_isBigO hdR (highDimensionalRidge_rate_exponents hs hs1 hγ).2.1)
  obtain ⟨Cv,hCv,hCvB⟩ := hV.exists_pos
  obtain ⟨Cb,hCb,hCbB⟩ := spherical_ridge_bias_uniform_upper ι H Φ hΦ hkernel hκ hdiag
    n hn lam hlam a ha hseries hs hs1 hγ hd hreg hR
  let S := fun i => (Cb+Cv)*d i^(-ζ)
  have hUpper : ∀ᶠ i in l, ∀ f : Θ i, (m ⟨i,f⟩).benchmark ≤ S i := by
    filter_upwards [hCvB.bound,hCbB] with i hi hv f
    have hv0 : 0 ≤ V i := mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (b i).Q_nonneg
    change ‖V i‖ ≤ Cv*‖d i^(-ζ)‖ at hi
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hv0,
      abs_of_nonneg (Real.rpow_nonneg (hdP i).le _)] at hi
    change (canonicalGaussianSourceRiskRow (b i) hσ f).benchmark ≤ S i
    rw [canonicalGaussianSourceRiskRow_benchmark,sequenceBenchmark,← featureFilterDimension_eq_positive_sequence]
    change featureSequenceBias (b i).feature (b i).feature_memLp (b i).φ f.val + V i ≤
      (Cb+Cv)*d i^(-ζ)
    rw [add_mul]
    exact add_le_add (hv f) hi
  have hU := dependent_sup_risk_eventual_upper
    (fun i f => (m ⟨i,f⟩).expectationRisk) (fun i f => (m ⟨i,f⟩).benchmark)
    S hΘ hpos hUpper hu
  have hNonneg : ∀ᶠ i in l, 0 ≤ W i ∧ M i ≤ W i := by
    filter_upwards [hU] with i hi
    have hW := canonicalGaussianSourceWorstRisk_nonneg (b i) hs.le hσ hR.le hi.1
    refine ⟨hW,?_⟩
    have hle := gaussianSourceMinimaxRisk_le_canonicalWorstRisk (b i) hs.le hσ hi.1
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq (ENNReal.toReal_ofReal hW)
  refine ⟨hNonneg, IsBigO.of_bound (2*(Cb+Cv)) ?_⟩
  filter_upwards [hNonneg,hU] with i hi hu
  change ‖W i‖ ≤ (2*(Cb+Cv))*‖d i^(-ζ)‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hi.1,
    abs_of_nonneg (Real.rpow_nonneg (hdP i).le _),mul_assoc]
  exact hu.2

end
end KernelSeq
