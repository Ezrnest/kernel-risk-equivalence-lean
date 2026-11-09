import KernelSeq.SphericalPhaseCutoffGaps
import KernelSeq.SphericalPositiveSpectrum

/-!
# Exact worst source bias of the actual smoothed cutoff

The supremum is attained in a degree-p or degree-(p+1) direction. The
upper bound uses the full supported spectrum, including every higher degree.
-/

namespace KernelSeq
open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section

def sphericalPhaseCutoffBias (ι : Type*) [Fintype ι] (a : ℕ → ℝ)
    (p : ℕ) (s R w : ℝ) : ℝ :=
  R^2 * max (zonalSphereDegreeValue (ι := ι) a p ^ s * (1-w)^2)
    (zonalSphereDegreeValue (ι := ι) a (p+1) ^ s)

section SingleRow

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
  (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
  (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
  (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)
  (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
  (p : ℕ) {s R w M : ℝ}
  (χ : ℝ → ℝ) (hχ : ResidualFilter.PhaseCutoffProfile w χ)

local notation "μ" => fun j => zonalSphereDegreeValue (ι := ι) a j
local notation "S" => featureEmbedding uniformSphere k hk
local notation "φ" => ResidualFilter.smoothedCutoff (μ p) χ
local notation "W" => max ((μ p)^s*(1-w)^2) ((μ (p+1))^s)

include ha hseries hkernel hΦ hχ in
theorem sphericalPhaseCutoff_sourceBias_le
    (hs : 0 ≤ s) (hR : 0 ≤ R) (hM : ‖populationCovariance S‖ ≤ M)
    (hlo : ∀ j < p, 2*μ p ≤ μ j)
    (hgap : 2*μ (p+1) ≤ μ p)
    (htail : ∀ j > p, μ j ≤ μ (p+1))
    {f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))}
    (hf : f ∈ featureSourceBall k hk s hs R) :
    featureSequenceBias k hk φ f ≤ sphericalPhaseCutoffBias ι a p s R w := by
  have hlam := zonalSphereDegreeValue_pos_of_smooth (ι := ι) a ha Φ hseries hΦ p
  have hμ (j : ℕ) : 0 ≤ μ j := zonalSphereDegreeValue_nonneg a (fun j => (ha j).le) j
  have hW : 0 ≤ W := (Real.rpow_nonneg (hμ (p+1)) s).trans (le_max_right _ _)
  apply featureSequenceBias_le_of_spectral_weight_bound k hk hs hR hM φ
    (ResidualFilter.phaseCutoff_spectralFilter hχ) hW _ hf
  intro i
  obtain ⟨j,hj⟩ := spherical_positiveSpectrum_degree k hk a ha Φ hseries hkernel hΦ i
  unfold featureSourceBiasWeight ResidualFilter.residual
  rw [← hj]
  rcases lt_trichotomy j p with hjp | rfl | hpj
  · rw [ResidualFilter.phaseCutoff_shrinkage_one_of_ge_twice hlam hχ (hlo j hjp)]
    simpa only [sub_self, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero] using hW
  · rw [ResidualFilter.phaseCutoff_shrinkage_at_scale hlam hχ]
    exact le_max_left _ _
  · rw [ResidualFilter.phaseCutoff_shrinkage_zero_of_le_half hlam hχ
      ((htail j hpj).trans (by linarith : μ (p+1) ≤ μ p / 2))]
    simp only [sub_zero, one_pow, mul_one]
    exact (Real.rpow_le_rpow (hμ j) (htail j hpj) hs).trans (le_max_right _ _)

include ha hseries hkernel hΦ hχ in
theorem sphericalPhaseCutoff_sourceBias_attained
    (hs : 0 ≤ s) (hR : 0 ≤ R) (hd : p+1 ≤ Fintype.card ι)
    (hgap : 2*μ (p+1) ≤ μ p) :
    ∃ f ∈ featureSourceBall k hk s hs R,
      featureSequenceBias k hk φ f = sphericalPhaseCutoffBias ι a p s R w := by
  have hlam := zonalSphereDegreeValue_pos_of_smooth (ι := ι) a ha Φ hseries hΦ p
  by_cases hcmp : (μ (p+1))^s ≤ (μ p)^s*(1-w)^2
  · obtain ⟨i,hi⟩ := spherical_positiveSpectrum_contains_degree k hk a ha Φ hseries hkernel p
      (Nat.le_of_succ_le hd)
    apply featureSequenceBias_attained_of_spectral_weight k hk hs hR φ i
    unfold featureSourceBiasWeight ResidualFilter.residual
    rw [hi, ResidualFilter.phaseCutoff_shrinkage_at_scale hlam hχ, max_eq_left hcmp]
  · obtain ⟨i,hi⟩ := spherical_positiveSpectrum_contains_degree k hk a ha Φ hseries hkernel (p+1) hd
    apply featureSequenceBias_attained_of_spectral_weight k hk hs hR φ i
    unfold featureSourceBiasWeight ResidualFilter.residual
    rw [hi, ResidualFilter.phaseCutoff_shrinkage_zero_of_le_half hlam hχ (by linarith),
      max_eq_right (le_of_not_ge hcmp)]
    simp

end SingleRow

section Limits
variable {J : Type*} {l : Filter J}
  (ι : J → Type*) [∀ i, Fintype (ι i)] [∀ i, Nonempty (ι i)]
  (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
  (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
  (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
  (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)

include ha hseries hΦ hd in
theorem spherical_fixedDegree_rpow_scaled_tendsto (p : ℕ) (s : ℝ) :
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^((p:ℝ)*s) *
      zonalSphereDegreeValue (ι := ι i) a p ^ s) l (𝓝 ((a p*(p.factorial : ℝ))^s)) := by
  have hlim := zonalSphereDegreeValue_scaled_tendsto ι a (fun j => (ha j).le)
    Φ hseries hΦ p hd
  have h0 : 0 < a p*(p.factorial : ℝ) := mul_pos (ha p) (by positivity)
  apply (hlim.rpow_const (Or.inl h0.ne') (p := s)).congr
  intro i
  rw [Real.mul_rpow (zonalSphereDegreeValue_nonneg a (fun j => (ha j).le) p) (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]

include ha hseries hΦ hd in
theorem sphericalPhaseCutoff_bias_degree_limit (p : ℕ) {s R w : ℝ} (hs : 0 < s) :
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^((p:ℝ)*s) *
      sphericalPhaseCutoffBias (ι i) a p s R w) l
      (𝓝 (highDimensionalSourceConstant a s R p * (1-w)^2)) := by
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let μ := fun (m : ℕ) i => zonalSphereDegreeValue (ι := ι i) a m
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hd0 (i : J) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hmain := (spherical_fixedDegree_rpow_scaled_tendsto ι a ha Φ hseries hΦ hd p s).mul_const ((1-w)^2)
  have hsmall := dimensionPower_rescale_tendsto_zero hdR hd0
    (show (p:ℝ)*s < ((p+1:ℕ):ℝ)*s by push_cast; nlinarith)
    (spherical_fixedDegree_rpow_scaled_tendsto ι a ha Φ hseries hΦ hd (p+1) s)
  have hmax := (hmain.max hsmall).const_mul (R^2)
  have hlim0 := mul_nonneg (Real.rpow_nonneg (mul_nonneg (ha p).le (Nat.cast_nonneg p.factorial)) s) (sq_nonneg (1-w))
  rw [max_eq_left hlim0] at hmax
  rw [highDimensionalSourceConstant, mul_assoc]
  apply hmax.congr
  intro i
  change R^2*max ((d i^((p:ℝ)*s)*μ p i^s)*(1-w)^2)
    (d i^((p:ℝ)*s)*μ (p+1) i^s) = _
  rw [mul_assoc (d i^((p:ℝ)*s)), ← mul_max_of_nonneg _ _ (Real.rpow_nonneg (hd0 i).le _)]
  unfold sphericalPhaseCutoffBias
  ring

include ha hseries hΦ hd in
theorem sphericalPhaseCutoff_bias_succ_limit (p : ℕ) (s R : ℝ) :
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^(((p+1:ℕ):ℝ)*s) *
      sphericalPhaseCutoffBias (ι i) a p s R 1) l
      (𝓝 (highDimensionalSourceConstant a s R (p+1))) := by
  apply ((spherical_fixedDegree_rpow_scaled_tendsto ι a ha Φ hseries hΦ hd (p+1) s).const_mul (R^2)).congr
  intro i
  unfold sphericalPhaseCutoffBias
  rw [sub_self, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero,
    max_eq_right (Real.rpow_nonneg (zonalSphereDegreeValue_nonneg a (fun j => (ha j).le) _) _)]
  ring

end Limits
end
end KernelSeq
