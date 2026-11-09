import KernelSeq.HighDimensionalMinimaxBlockLimits
import KernelSeq.HighDimensionalMinimaxRemainder

/-!
# The original sharp spherical minimax lower bound in all four phases

The prior uses actual finite spherical eigenblocks. The squarefree blocks
already have the sharp leading dimensions, and their eigenvalues come from
the original zonal kernel. Concentration, the finite Gaussian regression
comparison, and removal of shaving are all supplied by proved lemmas.
-/

namespace KernelSeq
open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section

private theorem spherical_minimax_adjacent_degree_distinct {I : Type*} {l : Filter I}
    (ι : I → Type*) [∀ i, Fintype (ι i)] [∀ i, Nonempty (ι i)]
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (p : ℕ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    ∀ᶠ i in l, zonalSphereDegreeValue (ι := ι i) a p ≠ zonalSphereDegreeValue (ι := ι i) a (p+1) := by
  let d := fun i => (Fintype.card (ι i) : ℝ)
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hd0 (i : I) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hlim (m : ℕ) : Tendsto (fun i => d i^(m : ℝ)*zonalSphereDegreeValue (ι := ι i) a m) l
      (𝓝 (a m*(m.factorial : ℝ))) := by
    simpa only [d, Real.rpow_natCast, mul_comm] using
      zonalSphereDegreeValue_scaled_tendsto ι a (fun j => (ha j).le) Φ hseries hΦ m hd
  have hs := dimensionPower_rescale_tendsto_zero hdR hd0 (Nat.cast_lt.mpr (Nat.lt_succ_self p)) (hlim (p+1))
  have hdiff := (hlim p).sub hs
  rw [sub_zero] at hdiff
  have hp : 0 < a p*(p.factorial : ℝ) := mul_pos (ha p) (Nat.cast_pos.mpr p.factorial_pos)
  filter_upwards [hdiff.eventually (lt_mem_nhds hp)] with i hi
  intro he
  change 0 < d i^(p:ℝ)*zonalSphereDegreeValue (ι := ι i) a p -
    d i^(p:ℝ)*zonalSphereDegreeValue (ι := ι i) a (p+1) at hi
  rw [he, sub_self] at hi
  exact (lt_irrefl 0) hi

universe uI uι uH
section OriginalModel
variable {I : Type uI} {l : Filter I}
    (ι : I → Type uι) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (H : I → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]
    (Φ : ℝ → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    {s γ R σ η : ℝ} (hs : 0 < s) (hγ : s+1 ≤ γ) (hR : 0 < R) (hσ : 0 < σ) (hη : 0 < η)
    (n : I → ℕ) (hnpos : ∀ i, 0 < n i)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hn : Tendsto (fun i => (n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) l (𝓝 η))

include ha hseries hγ hR hσ hη hnpos hd hn

set_option maxHeartbeats 1000000 in
theorem rkhs_spherical_minimax_normalized_shaved_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ err > 0, ∀ᶠ i in l,
      highDimensionalPinskerConstant a s γ (Real.sqrt (1-ε)*R) σ η-err ≤
        (Fintype.card (ι i) : ℝ)^(highDimensionalRiskExponent s γ)*
          (gaussianRangeMinimaxRisk (rkhsFeature (H := H i))
            (zonalSphereFeature_memLp Φ hΦ.continuousOn (hkernel i)) σ (n i)
            (featureSourceBall (rkhsFeature (H := H i))
              (zonalSphereFeature_memLp Φ hΦ.continuousOn (hkernel i)) s hs.le R)).toReal := by
  let p := highDimensionalDegree s γ
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let R' := Real.sqrt (1-ε)*R
  let K := highDimensionalPriorWeightFactor p R
  let B := fun i => K*d i^(-(p:ℝ))
  let C := highDimensionalPinskerConstant a s γ R' σ η
  have hΦsum : HasSum a (Φ 1) := by simpa only [one_pow, mul_one] using hseries 1 (by norm_num)
  have hΦ1 : 0 ≤ Φ 1 := hΦsum.tsum_eq ▸ tsum_nonneg (fun j => (ha j).le)
  let κ := Real.sqrt (Φ 1)
  have hκ : 0 ≤ κ := Real.sqrt_nonneg _
  have hdiag : Φ 1 ≤ κ^2 := (Real.sq_sqrt hΦ1).symm.le
  let risk := fun i => highDimensionalPriorSequenceRisk (Fintype.card (ι i)) (n i)
    (zonalSphereDegreeValue (ι := ι i) a) s γ R' σ
  let rem := fun i => finiteGaussianShavingConstant κ s R*Real.exp (-priorShavingExponent ε R/(2*B i))
  let M := fun i => (gaussianRangeMinimaxRisk (rkhsFeature (H := H i))
    (zonalSphereFeature_memLp Φ hΦ.continuousOn (hkernel i)) σ (n i)
    (featureSourceBall (rkhsFeature (H := H i))
      (zonalSphereFeature_memLp Φ hΦ.continuousOn (hkernel i)) s hs.le R)).toReal
  have hpN : 0 < p := (highDimensionalDegree_bounds hs hγ).1
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hd0 (i : I) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hK : 0 < K := highDimensionalPriorWeightFactor_pos p hR
  have hB (i : I) : 0 < B i := mul_pos hK (Real.rpow_pos_of_pos (hd0 i) _)
  have hB0 : Tendsto B l (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hp).comp hdR).const_mul K
    simpa only [Function.comp_def, mul_zero, B] using h
  have hBsmall : ∀ᶠ i in l, B i ≤ 1/4 :=
    (hB0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))).mono (fun _ hi => hi.le)
  have hdim : ∀ᶠ i in l, 2*(p+1) ≤ Fintype.card (ι i) := hd.eventually (eventually_ge_atTop _)
  have hgap := spherical_minimax_adjacent_degree_distinct ι a ha Φ hseries hΦ p hd
  have hR' : 0 < R' := mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hε1)) hR
  have hRsq : R'^2 = (1-ε)*R^2 := by
    dsimp [R']
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hε1.le)]
  have hbudget : (1-ε)*R^2 ≤ R^2 := by nlinarith [mul_nonneg hε.le (sq_nonneg R)]
  have hprior : ∀ᶠ i in l, risk i ≤ M i+rem i := by
    filter_upwards [hdim, hBsmall, hgap] with i hi hiB higap
    have hw := spherical_minimax_prior_weight_bounds (ι := ι i) p hi hbudget
    have hw0 : (1-ε)*R^2/((Fintype.card (ι i)).choose p : ℝ) ≤ B i := hw.1
    have hw1 : (1-ε)*R^2/((Fintype.card (ι i)).choose (p+1) : ℝ) ≤ B i := hw.2
    by_cases hzero : highDimensionalRemainder s γ = 0
    · have hh := spherical_minimax_single_block_lower Φ hΦ.continuousOn (hkernel i)
        a ha hseries hκ hdiag hs.le hR hσ hε hε1 (hB i) hiB (n i) (hnpos i) p (by omega) hw0
      simp only [risk, highDimensionalPriorSequenceRisk, if_pos hzero, hRsq, highDimensionalBlockNoise]
      exact hh
    · have hr : highDimensionalMinimaxShare (d i) (highDimensionalRemainder s γ) ∈ Ioo (0:ℝ) 1 :=
        highDimensionalMinimaxShare_mem (Nat.one_le_cast.mpr Fintype.card_pos) (highDimensionalRemainder_mem hs hγ).1
      have hh := spherical_minimax_two_block_lower Φ hΦ.continuousOn (hkernel i)
        a ha hseries hκ hdiag hs.le hR hσ hε hε1 (hB i) hiB (n i) (hnpos i) p (by omega) higap hr hw0 hw1
      simp only [risk, highDimensionalPriorSequenceRisk, if_neg hzero, hRsq, highDimensionalBlockNoise]
      simpa only [mul_assoc] using hh
  have hseq : Tendsto (fun i => d i^(highDimensionalRiskExponent s γ)*risk i) l (𝓝 C) :=
    spherical_minimax_prior_sequence_limit ι a ha Φ hseries hΦ hs hγ hR' hσ hη n hd hn
  have hrem : Tendsto (fun i => d i^(highDimensionalRiskExponent s γ)*rem i) l (𝓝 0) :=
    dimension_exponential_shaving_remainder_tendsto_zero d hdR hd0 hp hK
      (priorShavingExponent_pos hε hε1 hR) _ _
  have hdiff := hseq.sub hrem
  rw [sub_zero] at hdiff
  intro err herr
  have hnear := hdiff.eventually (lt_mem_nhds (show C-err < C by linarith))
  filter_upwards [hprior, hnear] with i hi hn'
  have hm := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (hd0 i).le (highDimensionalRiskExponent s γ))
  change C-err < d i^(highDimensionalRiskExponent s γ)*risk i -
    d i^(highDimensionalRiskExponent s γ)*rem i at hn'
  change C-err ≤ d i^(highDimensionalRiskExponent s γ)*M i
  exact hn'.le.trans (by linarith only [hm])

/-- The sharp lower constant over the original full measurable prediction
class, at each of the manuscript's four high-dimensional phases. -/
theorem rkhs_spherical_minimax_normalized_lower :
    ∀ err > 0, ∀ᶠ i in l,
      highDimensionalPinskerConstant a s γ R σ η-err ≤
        (Fintype.card (ι i) : ℝ)^(highDimensionalRiskExponent s γ)*
          (gaussianRangeMinimaxRisk (rkhsFeature (H := H i))
            (zonalSphereFeature_memLp Φ hΦ.continuousOn (hkernel i)) σ (n i)
            (featureSourceBall (rkhsFeature (H := H i))
              (zonalSphereFeature_memLp Φ hΦ.continuousOn (hkernel i)) s hs.le R)).toReal := by
  intro err herr
  let C := highDimensionalPinskerConstant a s γ R σ η
  have hC : 0 < C := highDimensionalPinskerConstant_pos ha hR hσ hη
  let ε := min (1/2 : ℝ) (err/(2*C))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos herr (by positivity))
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have heC : ε*C ≤ err/2 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (1/2:ℝ) (err/(2*C))) hC.le
    have he : (err/(2*C))*C = err/2 := by field_simp
    exact hh.trans_eq he
  have hshave := highDimensionalPinskerConstant_shaved_lower a ha (s := s) (γ := γ) hR hσ hη hε.le hε1
  have hlow := rkhs_spherical_minimax_normalized_shaved_lower ι H Φ hΦ hkernel a ha hseries
    hs hγ hR hσ hη n hnpos hd hn hε hε1 (err/2) (by positivity)
  filter_upwards [hlow] with i hi
  refine le_trans ?_ hi
  change C-err ≤ highDimensionalPinskerConstant a s γ (Real.sqrt (1-ε)*R) σ η - err/2
  change (1-ε)*C ≤ highDimensionalPinskerConstant a s γ (Real.sqrt (1-ε)*R) σ η at hshave
  nlinarith only [hshave, heC]

end OriginalModel
end
end KernelSeq
