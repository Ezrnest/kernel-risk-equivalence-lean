import KernelSeq.HighDimensionalRidgeRates
import KernelSeq.SphericalSpectralSums
import KernelSeq.SupportedEigenvalueBasis
import KernelSeq.CanonicalGaussianSourceFamily

/-!
# Actual spherical KRR variance and uniform sequence risk
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology ContDiff BigOperators
noncomputable section

universe uJ uI uH
variable {J : Type uJ} {l : Filter J}
    (ι : J → Type uI) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (H : J → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]
    {κ s γ : ℝ}
    (Φ : ℝ → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (n : J → ℕ) (hn : ∀ i, 0 < n i)
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)

def sphericalRidgeScaleModel (i : J) : SpectralScaleModel.{uH,uI} κ 1 2 :=
  sphericalScaleModel Φ hΦ.continuousOn (hkernel i) hκ hdiag (n i) (hn i)
    0 (lam i) (hlam i) (ResidualFilter.ridge (lam i))
    (ResidualFilter.ridge_spectralFilter (hlam i)) (ResidualFilter.ridge_contract (hlam i))

variable (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hs : 0 < s) (hs1 : s ≤ 1) (hγ : s+1 ≤ γ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hreg : lam =Θ[l] (fun i => (Fintype.card (ι i) : ℝ)^(-highDimensionalRidgeExponent s γ)))

include a ha hseries hs hs1 hγ hd hreg in
theorem spherical_ridge_Q_isBigO :
    let b := sphericalRidgeScaleModel ι H Φ hΦ hkernel hκ hdiag n hn lam hlam
    (fun i => (b i).Q) =O[l]
      (fun i => (Fintype.card (ι i) : ℝ)^(highDimensionalDegree s γ : ℝ)) := by
  intro b
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let p := highDimensionalDegree s γ
  let e := highDimensionalRidgeExponent s γ
  let D := fun i j => (Module.finrank ℝ (spherePolynomialLayer (ι i) j) : ℝ)
  let μ := fun i j => zonalSphereDegreeValue (ι := ι i) a j
  let C := zonalDegreeMomentConstant a (p+1)
  let U := fun i => C*d i^(-((p : ℝ)+1))
  let Low := fun i => ∑ j ∈ Finset.range (p+1), D i j
  have hdP (i : J) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hU (i : J) (j : ℕ) (hj : p < j) : μ i j ≤ U i := by
    have h := zonalSphereDegreeValue_uniform_upper (ι := ι i) a (fun k => (ha k).le)
      Φ hseries hΦ j (p+1) hj
    simpa only [U,C,d,μ,Real.rpow_neg (hdP i).le,← Nat.cast_succ,Real.rpow_natCast,div_eq_mul_inv]
      using h
  have hμ (i : J) (j : ℕ) : 0 ≤ μ i j :=
    zonalSphereDegreeValue_nonneg a (fun k => (ha k).le) j
  have hU0 (i : J) : 0 ≤ U i := (hμ i (p+1)).trans (hU i (p+1) (by omega))
  have hupper (i : J) : (b i).Q ≤ Low i+(U i/(lam i)^2)*κ^2 := by
    let k := (b i).feature
    let hk := (b i).feature_memLp
    have hg (x y : KernelSphere (EuclideanSpace ℝ (ι i))) :
        inner ℝ (k x) (k y) = zonalSphereKernel Φ x y := by
      change inner ℝ (rkhsFeature (H := H i) x) (rkhsFeature (H := H i) y) = _
      rw [rkhsFeature_inner,rkhsFeature_apply,hkernel]
    have ht := hasSum_zonalSphere_covarianceTrace k hk a ha
      Φ hseries hg hΦ
    have hQ := hasSum_zonalSphere_filterDimension k hk a ha
      Φ hseries hg hΦ (ResidualFilter.ridge (lam i)) (hlam i) (b i).population_bound
      (ResidualFilter.ridge_spectralFilter (hlam i)) (ResidualFilter.ridge_contract (hlam i))
    have h := ridge_degree_variance_le (D i) (μ i) p (hlam i) (fun j => Nat.cast_nonneg _)
      (hμ i) (hU i) ht.summable hQ.summable
    rw [ht.tsum_eq,hQ.tsum_eq] at h
    have htrace := featureCovarianceTrace_le_sq_bound k hk κ (Eventually.of_forall fun x =>
      pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ (b i).kappa_nonneg (b i).diagonal_bound x) 2)
    exact h.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left htrace (div_nonneg (hU0 i) (sq_nonneg _))))
  have hLow : Low =O[l] (fun i => d i^(p : ℝ)) := by
    apply IsBigO.sum
    intro j hj
    have hjp : (j : ℝ) ≤ p := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact (spherical_layerDimension_isBigO ι j hd).trans (dimensionPower_isBigO hdR hjp)
  have hUO : U =O[l] (fun i => d i^(-((p : ℝ)+1))) :=
    (isBigO_refl _ _).const_mul_left C
  have hreg2 := (IsTheta.rpow (r := -2) (Eventually.of_forall fun i => (hlam i).le)
    (Eventually.of_forall fun i => Real.rpow_nonneg (hdP i).le (-e)) hreg).isBigO
  have hInv : (fun i => ((lam i)^2)⁻¹) =O[l] (fun i => d i^(2*e)) := by
    apply hreg2.congr
    · intro i
      rw [Real.rpow_neg (hlam i).le,Real.rpow_two]
    · intro i
      rw [← Real.rpow_mul (hdP i).le]
      congr 1
      ring
  have hTail := (hUO.mul hInv).const_mul_left (κ^2)
  have hTail' : (fun i => (U i/(lam i)^2)*κ^2) =O[l] (fun i => d i^(2*e-(p : ℝ)-1)) := by
    apply hTail.congr
    · intro i
      simp only [div_eq_mul_inv]
      ring
    · intro i
      rw [← Real.rpow_add (hdP i)]
      congr 1
      ring
  have hMaj := hLow.add (hTail'.trans (dimensionPower_isBigO hdR
    (highDimensionalRidge_rate_exponents hs hs1 hγ).1))
  refine (IsBigO.of_bound 1 (g := fun i => Low i+(U i/(lam i)^2)*κ^2) ?_).trans hMaj
  filter_upwards [] with i
  have hl : 0 ≤ Low i := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (b i).Q_nonneg,
    abs_of_nonneg (add_nonneg hl (mul_nonneg (div_nonneg (hU0 i) (sq_nonneg _)) (sq_nonneg _))),one_mul]
    using hupper i

include a ha hseries hs1 hγ hd hreg in
theorem spherical_ridge_bias_uniform_upper {R : ℝ} (hR : 0 < R) :
    let b := sphericalRidgeScaleModel ι H Φ hΦ hkernel hκ hdiag n hn lam hlam
    ∃ C > 0, ∀ᶠ i in l, ∀ f : GaussianSourceIndex (b i) s hs.le R,
      featureSequenceBias (b i).feature (b i).feature_memLp (b i).φ f.val ≤
        C*(Fintype.card (ι i) : ℝ)^(-highDimensionalRiskExponent s γ) := by
  intro b
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let p := highDimensionalDegree s γ
  let U := zonalDegreeMomentConstant a (p+1)
  have hdP (i : J) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hd1 (i : J) : 1 ≤ d i := by
    change (1 : ℝ) ≤ (Fintype.card (ι i) : ℝ)
    exact_mod_cast (show 1 ≤ Fintype.card (ι i) from Fintype.card_pos)
  have hU0 : 0 ≤ U := by
    unfold U zonalDegreeMomentConstant
    exact mul_nonneg (by positivity) (tsum_nonneg fun j => mul_nonneg (ha j).le (by positivity))
  obtain ⟨c,hc,hmu⟩ := spherical_lowDegree_uniform_lower ι Φ a ha hseries hΦ p hd
  obtain ⟨C,hC,hl⟩ := hreg.isBigO.exists_pos
  let W := C^2*c^(s-2)+U^s
  have hW : 0 < W := add_pos_of_pos_of_nonneg (by positivity) (Real.rpow_nonneg hU0 _)
  refine ⟨R^2*W,by positivity,?_⟩
  filter_upwards [hl.bound,hmu] with i hli hmui f
  have hl' : lam i ≤ C*d i^(-highDimensionalRidgeExponent s γ) := by
    change ‖lam i‖ ≤ C*‖d i^(-highDimensionalRidgeExponent s γ)‖ at hli
    simpa only [Real.norm_eq_abs,abs_of_pos (hlam i),abs_of_pos (Real.rpow_pos_of_pos (hdP i) _)]
      using hli
  have hW0 : 0 ≤ W*d i^(-highDimensionalRiskExponent s γ) :=
    mul_nonneg hW.le (Real.rpow_nonneg (hdP i).le _)
  rw [mul_assoc]
  apply featureSequenceBias_le_of_spectral_weight_bound (b i).feature (b i).feature_memLp
    hs.le hR.le (b i).population_bound (b i).φ (b i).spectral_filter hW0 _ f.property
  intro j
  let S := featureEmbedding (b i).μ (b i).feature (b i).feature_memLp
  let hk := (b i).feature_memLp
  let hcmp := populationCovariance_feature_isCompact _ (b i).feature hk
  let u := predictionSingularBasis S hcmp j
  have hu0 : (u : Lp ℝ 2 (b i).μ) ≠ 0 := by
    have hnorm : ‖(u : Lp ℝ 2 (b i).μ)‖ = 1 :=
      (predictionSingularBasis S hcmp).orthonormal.norm_eq_one j
    exact norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
  have hg (x y : KernelSphere (EuclideanSpace ℝ (ι i))) :
      inner ℝ ((b i).feature x) ((b i).feature y) = zonalSphereKernel Φ x y := by
    change inner ℝ (rkhsFeature (H := H i) x) (rkhsFeature (H := H i) y) = _
    rw [rkhsFeature_inner,rkhsFeature_apply,hkernel]
  obtain ⟨m,hm⟩ := predictionEigenvalue_occurs_in_supported_basis S
    (zonalSpherePredictionBasis (b i).feature hk a ha Φ hseries hg)
    (fun z => zonalSphereDegreeValue (ι := ι i) a z.1)
    (zonalSpherePredictionBasis_eigen (b i).feature hk a ha
      Φ hseries hg hΦ) u.property hu0 (predictionSingularBasis_eigen S hcmp j)
  let t := zonalSphereDegreeValue (ι := ι i) a m.1
  change j.1.1^s*(ResidualFilter.residual (ResidualFilter.ridge (lam i)) j.1.1)^2 ≤ _
  rw [← hm]
  by_cases hm' : m.1 ≤ p
  · have h := ridge_biasWeight_low_dimension_bound (hdP i) (hlam i) hc hC hs hs1 hγ
      (hmui m.1 hm') hl'
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Real.rpow_nonneg hU0 _)) (Real.rpow_nonneg (hdP i).le _))
  · have ht : t ≤ U*d i^(-((p : ℝ)+1)) := by
      have h := zonalSphereDegreeValue_uniform_upper (ι := ι i) a (fun j => (ha j).le)
        Φ hseries hΦ m.1 (p+1) (by omega)
      simpa only [U,t,d,Real.rpow_neg (hdP i).le,← Nat.cast_succ,Real.rpow_natCast,div_eq_mul_inv] using h
    have ht0 : 0 ≤ t := zonalSphereDegreeValue_nonneg a (fun j => (ha j).le) m.1
    have h := ridge_biasWeight_high_dimension_bound (hd1 i) (hlam i) ht0 hs hs1 hγ ht
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hc.le _)))
      (Real.rpow_nonneg (hdP i).le _))

end
end KernelSeq
