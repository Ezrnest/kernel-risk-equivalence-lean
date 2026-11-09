import KernelSeq.SchattenInterpolation
import KernelSeq.SpectralBlocks
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Intrinsic Schatten quantities and compression estimates

The quantities are the actual compact singular-value sums of the reconstructed
Hilbert--Schmidt operator. No complete Schatten Banach-space structure is
presupposed. The compression argument uses scalar spectral Jensen and Bessel,
rather than assuming an ideal property or a singular-value minmax theorem.
-/

open scoped Topology BigOperators ENNReal
open Filter

namespace KernelSeq

noncomputable section

variable {ι κ η H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The spectral sum is intrinsic to the actual covariance operator. -/
def compactPositivePowerSum (T : H →L[ℝ] H) (r : ℝ) : ℝ :=
  ∑' i : CompactSpectralIndex T, i.1 ^ r

theorem hsSchattenNorm_reconstruction_eq (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ H)
    (c : HilbertSchmidtColumns ι E) (e : HilbertSchmidtColumns κ E)
    (hA : hilbertSchmidtOperator b c = hilbertSchmidtOperator d e) (p : ℝ) :
    hsSchattenNorm b c p = hsSchattenNorm d e p := by
  change (compactPositivePowerSum (hsSingularCovariance b c) (p / 2)) ^ (1 / p) =
    (compactPositivePowerSum (hsSingularCovariance d e) (p / 2)) ^ (1 / p)
  have hT : hsSingularCovariance b c = hsSingularCovariance d e := by
    unfold hsSingularCovariance
    rw [hA]
  rw [hT]

theorem hsSchattenNorm_rebase (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ H)
    (c : HilbertSchmidtColumns ι E) (p : ℝ) :
    hsSchattenNorm d (hsRebase b d c) p = hsSchattenNorm b c p :=
  hsSchattenNorm_reconstruction_eq d b _ _ (hilbertSchmidtOperator_rebase b d c) p

section ScalarJensen

variable {I : Type*}

/-- Jensen for an arbitrary summable probability-weighted family. Finite
truncations put the missing mass at zero before taking the limit. -/
theorem rpow_tsum_probability_le (w t : I → ℝ) {r : ℝ} (hr : 1 ≤ r)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 ≤ t i)
    (hsw : Summable w) (hw1 : ∑' i, w i = 1)
    (hst : Summable (fun i => w i * t i))
    (hsr : Summable (fun i => w i * t i ^ r)) :
    (∑' i, w i * t i) ^ r ≤ ∑' i, w i * t i ^ r := by
  classical
  have hfin (s : Finset I) : (∑ i ∈ s, w i * t i) ^ r ≤ ∑ i ∈ s, w i * t i ^ r := by
    have hmass : 0 ≤ 1 - ∑ i ∈ s, w i := by
      have hsum := hsw.sum_le_tsum s (fun i _ => hw i)
      rw [hw1] at hsum
      linarith
    have h := (convexOn_rpow hr).map_add_sum_le (t := s) (w := w) (p := t)
      (v := 1 - ∑ i ∈ s, w i) (q := 0) (fun i _ => hw i) (by ring)
      (fun i _ => ht i) hmass (by simp)
    simpa only [smul_eq_mul, mul_zero, zero_add, Real.zero_rpow (by linarith : r ≠ 0)] using h
  exact le_of_tendsto_of_tendsto
    ((Real.continuous_rpow_const (by linarith : 0 ≤ r)).continuousAt.tendsto.comp hst.hasSum)
    hsr.hasSum (Filter.Eventually.of_forall hfin)

end ScalarJensen

/-- The weighted power series needed for spectral Jensen converges for every
vector; summability is inherited from the actual HS singular power sum. -/
theorem hsSingularPower_weighted_summable (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) (x : H) :
    Summable (fun i : HSSingularIndex b c =>
      i.1 ^ (p / 2) * (hsSingularBasis b c).repr x i ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun i => mul_nonneg (Real.rpow_nonneg (hsSingularValue_nonneg b c i) _) (sq_nonneg _)) _
    ((summable_hsSingularPower b c hp).mul_right (‖x‖ ^ 2))
  intro i
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hsSingularValue_nonneg b c i) _)
  have hi := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ((hsSingularBasis b c).repr x) i
  rw [(hsSingularBasis b c).repr.norm_map] at hi
  simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hi 2

/-- The actual spectral McCarthy/Jensen inequality for the covariance `A* A`.
It is valid for every `p ≥ 2`, not just the HS endpoint. -/
theorem hsSpectralJensen (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E)
    {p : ℝ} (hp : 2 ≤ p) {x : H} (hx : ‖x‖ = 1) :
    (‖hilbertSchmidtOperator b c x‖ ^ 2) ^ (p / 2) ≤
      ∑' i : HSSingularIndex b c, i.1 ^ (p / 2) * (hsSingularBasis b c).repr x i ^ 2 := by
  let w : HSSingularIndex b c → ℝ := fun i => (hsSingularBasis b c).repr x i ^ 2
  let t : HSSingularIndex b c → ℝ := fun i => i.1
  have hsw : Summable w := hilbertBasis_coefficients_sq_summable _ x
  have hw1 : ∑' i, w i = 1 := by
    rw [← hilbertBasis_norm_sq_eq_tsum (hsSingularBasis b c) x, hx]
    norm_num
  have hq := compact_quadratic_hasSum (hsSingularCovariance b c)
    (hsSingularCovariance_isCompact b c) (hsSingularCovariance_isPositive b c) x
  have hst : Summable (fun i => w i * t i) := hq.summable.congr (fun i => by dsimp [w, t, hsSingularBasis]; ring)
  have henergy : (∑' i, w i * t i) = ‖hilbertSchmidtOperator b c x‖ ^ 2 := by
    calc
      _ = inner ℝ x (hsSingularCovariance b c x) := by
        rw [← hq.tsum_eq]
        apply tsum_congr
        intro i
        dsimp only [w, t, hsSingularBasis]
        ring
      _ = _ := by
        simpa [hsSingularCovariance] using
          (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right
            (𝕜 := ℝ) (hilbertSchmidtOperator b c) x).symm
  have hsr : Summable (fun i => w i * t i ^ (p / 2)) := by
    simpa only [w, t, mul_comm] using hsSingularPower_weighted_summable b c hp x
  have hj := rpow_tsum_probability_le w t (by linarith : 1 ≤ p / 2)
    (fun i => sq_nonneg _) (hsSingularValue_nonneg b c) hsw hw1 hst hsr
  rw [henergy] at hj
  simpa only [w, t, mul_comm] using hj

/-- Any finite orthonormal family obeys the full `p`-energy bound. This is the
Jensen/Bessel step needed for genuine spectral compression, without minmax. -/
theorem hs_orthonormal_power_sum_le (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p)
    {J : Type*} (v : J → H) (hv : Orthonormal ℝ v) (s : Finset J) :
    (∑ j ∈ s, (‖hilbertSchmidtOperator b c (v j)‖ ^ 2) ^ (p / 2)) ≤
      ∑' i : HSSingularIndex b c, i.1 ^ (p / 2) := by
  classical
  let e := hsSingularBasis b c
  have hrows j : Summable (fun i : HSSingularIndex b c => i.1 ^ (p / 2) * e.repr (v j) i ^ 2) :=
    hsSingularPower_weighted_summable b c hp (v j)
  have hBessel (i : HSSingularIndex b c) : ∑ j ∈ s, e.repr (v j) i ^ 2 ≤ 1 := by
    have hh := hv.sum_inner_products_le (s := s) (x := e i)
    have heq (j : J) : ‖inner ℝ (v j) (e i)‖ ^ 2 = e.repr (v j) i ^ 2 := by
      rw [real_inner_comm (e i) (v j), ← e.repr_apply_apply]
      simp only [Real.norm_eq_abs, sq_abs]
    simp_rw [heq] at hh
    simpa only [e.orthonormal.norm_eq_one, one_pow] using hh
  calc
    _ ≤ ∑ j ∈ s, ∑' i : HSSingularIndex b c, i.1 ^ (p / 2) * e.repr (v j) i ^ 2 :=
      Finset.sum_le_sum (fun j _ => hsSpectralJensen b c hp (hv.norm_eq_one j))
    _ = ∑' i : HSSingularIndex b c, ∑ j ∈ s, i.1 ^ (p / 2) * e.repr (v j) i ^ 2 :=
      (Summable.tsum_finsetSum (fun j _ => hrows j)).symm
    _ ≤ ∑' i : HSSingularIndex b c, i.1 ^ (p / 2) := by
      apply Summable.tsum_le_tsum _ (summable_sum (fun j _ => hrows j))
        (summable_hsSingularPower b c hp)
      intro i
      rw [← Finset.mul_sum]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (hsSingularValue_nonneg b c i) _) (hBessel i)

section Compression

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- Actual columns of an isometric domain restriction followed by a bounded
output map. In particular these represent different left/right orthogonal
compressions, without a finite-dimensional ambient-space assumption. -/
def hsCompressionColumns (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ F)
    (e : HilbertBasis η ℝ E) (R : F →ₗᵢ[ℝ] H) (Q : E →L[ℝ] G)
    (c : HilbertSchmidtColumns ι E) : HilbertSchmidtColumns κ G :=
  hsLeftComposition Q (hsRightComposition b d e R.toContinuousLinearMap c)

theorem hilbertSchmidtOperator_compression (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ F)
    (e : HilbertBasis η ℝ E) (R : F →ₗᵢ[ℝ] H) (Q : E →L[ℝ] G)
    (c : HilbertSchmidtColumns ι E) :
    hilbertSchmidtOperator d (hsCompressionColumns b d e R Q c) =
      Q.comp ((hilbertSchmidtOperator b c).comp R.toContinuousLinearMap) := by
  rw [hsCompressionColumns, hilbertSchmidtOperator_leftComposition,
    hilbertSchmidtOperator_rightComposition]

/-- Compression decreases every actual finite Schatten power sum `p ≥ 2`.
This proves the ideal estimate needed here directly; it does not assume a
complete Schatten normed-space or approximation-number theory. -/
theorem hsCompression_singularPower_le (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ F)
    (e : HilbertBasis η ℝ E) (R : F →ₗᵢ[ℝ] H) (Q : E →L[ℝ] G)
    (hQ : ‖Q‖ ≤ 1) (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    (∑' j : HSSingularIndex d (hsCompressionColumns b d e R Q c), j.1 ^ (p / 2)) ≤
      ∑' i : HSSingularIndex b c, i.1 ^ (p / 2) := by
  classical
  let C := hsCompressionColumns b d e R Q c
  let v := hsSingularBasis d C
  have hv : Orthonormal ℝ (fun j => R (v j)) :=
    v.orthonormal.comp_linearIsometry R
  apply Real.tsum_le_of_sum_le (fun j => Real.rpow_nonneg (hsSingularValue_nonneg d C j) _)
  intro s
  calc
    _ ≤ ∑ j ∈ s, (‖hilbertSchmidtOperator b c (R (v j))‖ ^ 2) ^ (p / 2) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← hsSingularBasis_image_norm_sq d C j]
      apply Real.rpow_le_rpow (sq_nonneg _) _ (by linarith : 0 ≤ p / 2)
      apply pow_le_pow_left₀ (norm_nonneg _)
      have heq := hilbertSchmidtOperator_compression b d e R Q c
      change ‖hilbertSchmidtOperator d C (v j)‖ ≤ _
      rw [heq]
      simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, one_mul] using
        Q.le_of_opNorm_le hQ (hilbertSchmidtOperator b c (R (v j)))
    _ ≤ _ := hs_orthonormal_power_sum_le b c hp (fun j => R (v j)) hv s

/-- The true `p ≥ 2` Schatten quantity decreases under arbitrary isometric
restriction and output contraction. Finite orthogonal compressions are a
special case; all spaces and Hilbert bases may also be infinite. -/
theorem hsSchattenNorm_compression_le (b : HilbertBasis ι ℝ H) (d : HilbertBasis κ ℝ F)
    (e : HilbertBasis η ℝ E) (R : F →ₗᵢ[ℝ] H) (Q : E →L[ℝ] G)
    (hQ : ‖Q‖ ≤ 1) (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm d (hsCompressionColumns b d e R Q c) p ≤ hsSchattenNorm b c p := by
  apply Real.rpow_le_rpow
    (tsum_nonneg (fun j => Real.rpow_nonneg
      (hsSingularValue_nonneg d (hsCompressionColumns b d e R Q c) j) _))
    (hsCompression_singularPower_le b d e R Q hQ c hp)
    (one_div_nonneg.mpr (by linarith : 0 ≤ p))

end Compression

section OrthogonalCompression

/-- The actual rectangular compression `Q A|P` between two possibly different
closed subspaces, represented by columns in a basis of its actual domain. -/
def hsOrthogonalCompressionColumns (b : HilbertBasis ι ℝ H)
    (P : Submodule ℝ H) (Q : Submodule ℝ E) [CompleteSpace P] [CompleteSpace Q]
    (d : HilbertBasis κ ℝ P) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) : HilbertSchmidtColumns κ Q :=
  hsCompressionColumns b d e P.subtypeₗᵢ Q.orthogonalProjectionOnto c

theorem hilbertSchmidtOperator_orthogonalCompression (b : HilbertBasis ι ℝ H)
    (P : Submodule ℝ H) (Q : Submodule ℝ E) [CompleteSpace P] [CompleteSpace Q]
    (d : HilbertBasis κ ℝ P) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) :
    hilbertSchmidtOperator d (hsOrthogonalCompressionColumns b P Q d e c) =
      Q.orthogonalProjectionOnto.comp ((hilbertSchmidtOperator b c).comp P.subtypeL) := by
  exact hilbertSchmidtOperator_compression b d e P.subtypeₗᵢ Q.orthogonalProjectionOnto c

theorem hsSchattenNorm_orthogonalCompression_le (b : HilbertBasis ι ℝ H)
    (P : Submodule ℝ H) (Q : Submodule ℝ E) [CompleteSpace P] [CompleteSpace Q]
    (d : HilbertBasis κ ℝ P) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm d (hsOrthogonalCompressionColumns b P Q d e c) p ≤ hsSchattenNorm b c p :=
  hsSchattenNorm_compression_le b d e P.subtypeₗᵢ Q.orthogonalProjectionOnto
    Q.orthogonalProjectionOnto_norm_le c hp

/-- A finite actual spectral space, allowing any finite selection of the
constructed eigenvectors, including selections within multiple eigenspaces. -/
def finiteSpectralSpan (T : H →L[ℝ] H) (hc : IsCompactOperator T) (hp : T.IsPositive)
    (s : Finset (CompactSpectralIndex T)) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range (fun i : s => compactEigenbasis T hc hp.isSymmetric i))

instance finiteSpectralSpan_finiteDimensional (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hp : T.IsPositive) (s : Finset (CompactSpectralIndex T)) :
    FiniteDimensional ℝ (finiteSpectralSpan T hc hp s) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- The requested finite left/right spectral compressions are actual
instances of the proved infinite-dimensional contraction theorem. -/
theorem hsSchattenNorm_finiteSpectralCompression_le (b : HilbertBasis ι ℝ H)
    (U : H →L[ℝ] H) (V : E →L[ℝ] E)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive)
    (s : Finset (CompactSpectralIndex U)) (t : Finset (CompactSpectralIndex V))
    (d : HilbertBasis κ ℝ (finiteSpectralSpan U hcU hpU s)) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm d (hsOrthogonalCompressionColumns b
      (finiteSpectralSpan U hcU hpU s) (finiteSpectralSpan V hcV hpV t) d e c) p ≤
        hsSchattenNorm b c p :=
  hsSchattenNorm_orthogonalCompression_le b _ _ d e c hp

end OrthogonalCompression

section PointwiseLimit

/-- A Fatou bound for the actual singular power sum under pointwise operator
convergence. This is the finite-to-infinite passage needed after finite HMS
estimates, without invoking a complete Schatten Banach space. -/
theorem hsSingularPower_le_of_pointwise_tendsto (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {J : Type*} (l : Filter J) [NeBot l]
    (cs : J → HilbertSchmidtColumns ι E) {p B : ℝ} (hp : 2 ≤ p)
    (hconv : ∀ x, Tendsto (fun j => hilbertSchmidtOperator b (cs j) x) l
      (𝓝 (hilbertSchmidtOperator b c x)))
    (hbound : ∀ᶠ j in l, (∑' i : HSSingularIndex b (cs j), i.1 ^ (p / 2)) ≤ B) :
    (∑' i : HSSingularIndex b c, i.1 ^ (p / 2)) ≤ B := by
  classical
  let v := hsSingularBasis b c
  apply Real.tsum_le_of_sum_le (fun i => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _)
  intro s
  have hlim : Tendsto
      (fun j => ∑ i ∈ s, (‖hilbertSchmidtOperator b (cs j) (v i)‖ ^ 2) ^ (p / 2)) l
      (𝓝 (∑ i ∈ s, i.1 ^ (p / 2))) := by
    have ht := tendsto_finsetSum s (fun i _ =>
      (Real.continuous_rpow_const (by linarith : 0 ≤ p / 2)).continuousAt.tendsto.comp
        ((hconv (v i)).norm.pow 2))
    simpa only [v, hsSingularBasis_image_norm_sq, Function.comp_def] using ht
  apply le_of_tendsto hlim
  filter_upwards [hbound] with j hj
  exact (hs_orthonormal_power_sum_le b (cs j) hp v v.orthonormal s).trans hj

theorem hsSchattenNorm_rpow (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E)
    {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b c p ^ p = ∑' i : HSSingularIndex b c, i.1 ^ (p / 2) := by
  rw [hsSchattenNorm, ← Real.rpow_mul
    (tsum_nonneg (fun i => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _))]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- Uniform actual Schatten bounds pass to a pointwise limit of actual HS
operators. The limiting HS representation is given; neither norm convergence
nor a Schatten-completeness hypothesis is required. -/
theorem hsSchattenNorm_le_of_pointwise_tendsto (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {J : Type*} (l : Filter J) [NeBot l]
    (cs : J → HilbertSchmidtColumns ι E) {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C)
    (hconv : ∀ x, Tendsto (fun j => hilbertSchmidtOperator b (cs j) x) l
      (𝓝 (hilbertSchmidtOperator b c x)))
    (hbound : ∀ᶠ j in l, hsSchattenNorm b (cs j) p ≤ C) : hsSchattenNorm b c p ≤ C := by
  have hp0 : 0 < p := by linarith
  have hpow : (∑' i : HSSingularIndex b c, i.1 ^ (p / 2)) ≤ C ^ p := by
    apply hsSingularPower_le_of_pointwise_tendsto b c l cs hp hconv
    filter_upwards [hbound] with j hj
    rw [← hsSchattenNorm_rpow b (cs j) hp0]
    exact Real.rpow_le_rpow (Real.rpow_nonneg
      (tsum_nonneg (fun i => Real.rpow_nonneg (hsSingularValue_nonneg b (cs j) i) _)) _) hj hp0.le
  have h := Real.rpow_le_rpow
    (tsum_nonneg (fun i => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _)) hpow
    (one_div_nonneg.mpr hp0.le)
  change hsSchattenNorm b c p ≤ (C ^ p) ^ (1 / p) at h
  refine h.trans_eq ?_
  rw [← Real.rpow_mul hC, mul_one_div_cancel hp0.ne', Real.rpow_one]

end PointwiseLimit

end
end KernelSeq
