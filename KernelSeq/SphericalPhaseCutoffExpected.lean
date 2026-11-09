import KernelSeq.SphericalPhaseCutoffBias
import KernelSeq.SphericalPhaseCutoffVariance
import KernelSeq.SphericalPhaseCutoffScales
import KernelSeq.CanonicalGaussianSourceFamily

/-!
# Sharp expected risk of the original spherical cutoff estimator

The actual sequence supremum is attained in each sufficiently large row.
The risk comparison is applied on the dependent source family, with every
comparison scale derived from the kernel, sample schedule and source ball.
-/

namespace KernelSeq
open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section

universe uJ uI uH
variable {J : Type uJ} {l : Filter J} [NeBot l]
  (ι : J → Type uI) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
  (H : J → Type uH)
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
  [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]

set_option maxHeartbeats 1400000 in
theorem spherical_phaseCutoff_expected_limit
    {κ s R γ η σ : ℝ}
    (Φ : ℝ → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hs : 0 < s) (hR : 0 < R) (hγ : s+1 ≤ γ) (hη : 0 < η) (hσ : 0 < σ)
    (n : J → ℕ) (hn : ∀ i, 0 < n i)
    (χ : ℝ → ℝ) (hχ : ResidualFilter.PhaseCutoffProfile
      (highDimensionalPinskerWeight a s γ R σ η) χ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hnschedule : Tendsto (fun i => (n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) l (𝓝 η)) :
    let b := fun i => sphericalPhaseCutoffScaleModel Φ hΦ (hkernel i) hκ hdiag
      (n i) (hn i) 0 a ha hseries (highDimensionalDegree s γ) χ hχ
    (∀ᶠ i in l, BddAbove (Set.range (fun f : GaussianSourceIndex (b i) s hs.le R =>
      (canonicalGaussianSourceRiskRow (b i) hσ f).expectationRisk))) ∧
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^(highDimensionalRiskExponent s γ) *
      canonicalGaussianSourceWorstRisk (b i) s hs.le R hσ) l
      (𝓝 (highDimensionalPinskerConstant a s γ R σ η)) := by
  intro b
  let p := highDimensionalDegree s γ
  let w := highDimensionalPinskerWeight a s γ R σ η
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let k := fun i => rkhsFeature (H := H i)
  let hk := fun i => zonalSphereFeature_memLp Φ hΦ.continuousOn (hkernel i)
  have hgram (i : J) (x y : KernelSphere (EuclideanSpace ℝ (ι i))) :
      inner ℝ (k i x) (k i y) = zonalSphereKernel Φ x y := by
    dsimp only [k]
    rw [rkhsFeature_inner, rkhsFeature_apply, hkernel]
  let Θ := fun i => GaussianSourceIndex (b i) s hs.le R
  let L := dependentFamilyFilter l Θ
  have hΘ (i : J) : Nonempty (Θ i) := gaussianSourceIndex_nonempty (b i) hs.le hR.le
  letI : NeBot L := dependentFamilyFilter_neBot hΘ
  let row := fun z : Σ i, Θ i => canonicalGaussianSourceRiskRow (b z.1) hσ z.2
  let f : ∀ z : Σ i, Θ i, Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ (ι z.1))) :=
    fun z => z.2.val
  have hf : ∀ᶠ z in L, f z ∈ featureSourceBall (k z.1) (hk z.1) s hs.le R :=
    Eventually.of_forall fun z => z.2.property
  have hfst : Tendsto (Sigma.fst : (Σ i, Θ i) → J) L l := tendsto_comap
  have hw : 0 < w := (highDimensionalPinskerWeight_mem ha hR hσ hη).1
  let model := fun z : Σ i, Θ i => sphericalPhaseCutoffScaleModel Φ hΦ (hkernel z.1) hκ hdiag
    (n z.1) (hn z.1) (f z) a ha hseries p χ hχ
  have hmodel (z : Σ i, Θ i) : (row z).scaleModel = model z :=
    canonicalGaussianSourceRiskRow_scaleModel (b z.1) hσ z.2
  obtain ⟨hQ,hc,hz,he⟩ := spherical_phaseCutoff_original_scales
    (l := L) (fun z : Σ i, Θ i => ι z.1) (fun z => H z.1) Φ hΦ
    (fun z => hkernel z.1) hκ hdiag a ha hseries hs hR hγ hη
    (fun z => n z.1) (fun z => hn z.1) f χ hχ hw (hd.comp hfst) (hnschedule.comp hfst) hf
  change (∀ᶠ z in L, 0 < (model z).Q) at hQ
  have hQrow : ∀ᶠ z in L, 0 < (row z).Q := by
    filter_upwards [hQ] with z hz
    change 0 < (row z).scaleModel.Q
    rw [hmodel]
    exact hz
  have hcr : Tendsto (fun z => (row z).compatibility) L (𝓝 0) := by
    change Tendsto (fun z => (model z).compatibility) L (𝓝 0) at hc
    simpa only [← TriangularRiskModel.scaleModel_compatibility, hmodel] using hc
  have hzr : Tendsto (fun z => (row z).sourceBalance) L (𝓝 0) := by
    change Tendsto (fun z => (model z).sourceBalance) L (𝓝 0) at hz
    simpa only [← TriangularRiskModel.scaleModel_sourceBalance, hmodel] using hz
  have her : Tendsto (fun z => (row z).expectationScale) L (𝓝 0) := by
    change Tendsto (fun z => (model z).expectationScale) L (𝓝 0) at he
    simpa only [← TriangularRiskModel.scaleModel_expectationScale, hmodel] using he
  have hratio := (triangular_expectation_risk_equivalence (l := L) row hσ
    (Eventually.of_forall fun _ => le_rfl) hQrow hcr hzr her).1
  let risk := fun i (t : Θ i) => (row ⟨i,t⟩).expectationRisk
  let B := fun i (t : Θ i) => (row ⟨i,t⟩).benchmark
  let bias := fun i => sphericalPhaseCutoffBias (ι i) a p s R w
  let variance := fun i => σ^2/(n i : ℝ)*(b i).Q
  let W := fun i => bias i + variance i
  have hBpos : ∀ᶠ i in l, ∀ t, 0 < B i t :=
    eventually_dependentFamilyFilter_iff.mp
      (hQrow.mono fun z hQz => (row z).benchmark_pos hQz)
  have hBform (i : J) (t : Θ i) :
      B i t = featureSequenceBias (k i) (hk i) (b i).φ t.val + variance i := by
    change (canonicalGaussianSourceRiskRow (b i) hσ t).benchmark = _
    rw [canonicalGaussianSourceRiskRow_benchmark, sequenceBenchmark,
      ← featureFilterDimension_eq_positive_sequence]
    rfl
  have hgaps := spherical_phaseCutoff_gaps ι a ha Φ hseries hΦ hd p
  have hUpper : ∀ᶠ i in l, ∀ t, B i t ≤ W i := by
    filter_upwards [hgaps] with i hi t
    rw [hBform]
    exact add_le_add (sphericalPhaseCutoff_sourceBias_le (k i) (hk i) a ha Φ hseries (hgram i) hΦ
      p χ hχ hs.le hR.le (b i).population_bound hi.1 hi.2.1 hi.2.2 t.property) le_rfl
  have hAttain : ∀ᶠ i in l, ∃ t, B i t = W i := by
    filter_upwards [hgaps, hd.eventually (eventually_ge_atTop (p+1))] with i hi hdi
    obtain ⟨target,htarget,hb⟩ := sphericalPhaseCutoff_sourceBias_attained (k i) (hk i)
      a ha Φ hseries (hgram i) hΦ p χ hχ hs.le hR.le hdi hi.2.1
    let t : Θ i := ⟨target,htarget⟩
    refine ⟨t,?_⟩
    rw [hBform]
    change _ = bias i + variance i
    exact congrArg (fun x => x + variance i) hb
  obtain ⟨hbdd,hSup⟩ := dependent_sup_risk_ratio_tendsto risk B W hBpos hUpper hAttain hratio
  refine ⟨hbdd,?_⟩
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hd0 (i : J) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hv : Tendsto (fun i => d i^(γ-(p : ℝ))*variance i) l
      (𝓝 (highDimensionalNoiseConstant σ η p*w^2)) :=
    spherical_phaseCutoff_sequenceVariance_scaled_tendsto ι H k hk a ha Φ hseries hΦ hgram
      p χ hχ hd n hn hη hnschedule
  have hlimit := highDimensionalPinsker_phase_limit d bias variance hdR hd0 a ha hs hγ hR hσ hη
    (fun _ => sphericalPhaseCutoff_bias_degree_limit ι a ha Φ hseries hΦ hd p hs)
    (fun hδ => by
      have hw1 : w = 1 := if_neg hδ.ne'
      simpa only [bias, hw1, Nat.cast_add, Nat.cast_one] using
        sphericalPhaseCutoff_bias_succ_limit ι a ha Φ hseries hΦ hd p s R) hv
  have hW : ∀ᶠ i in l, 0 < W i := by
    filter_upwards [hBpos,hAttain] with i hi ⟨t,ht⟩
    exact ht ▸ hi t
  have hfinal := hlimit.mul hSup
  rw [mul_one] at hfinal
  apply hfinal.congr'
  filter_upwards [hW] with i hi
  change (d i^(highDimensionalRiskExponent s γ)*W i) *
    (canonicalGaussianSourceWorstRisk (b i) s hs.le R hσ / W i) =
    d i^(highDimensionalRiskExponent s γ)*canonicalGaussianSourceWorstRisk (b i) s hs.le R hσ
  rw [mul_assoc, mul_div_cancel₀ _ hi.ne']

end
end KernelSeq
