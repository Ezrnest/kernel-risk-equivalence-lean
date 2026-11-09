import KernelSeq.HSCovariance
import KernelSeq.EffectiveDimension
import Mathlib.Tactic.NoncommRing

/-!
# The actual normalized covariance fluctuation and its HS moment

Connects the real inverse square root, the empirical/population covariances,
Hilbert–Schmidt columns and the effective dimension. The Hilbert–Schmidt
covariance bound follows from independent sampling. The sharper intrinsic-dimension Bernstein operator-norm estimate is
still a separate obligation.
-/

open MeasureTheory ProbabilityTheory Topology
open scoped BigOperators ENNReal

namespace KernelSeq

variable {ι X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω}

/-- Exact empirical covariance conjugation, for an arbitrary bounded map. -/
theorem empiricalCovariance_conjugation (R : H →L[ℝ] H) {n : ℕ} (z : Fin n → H) :
    R * empiricalCovariance z * R.adjoint = empiricalCovariance (fun i => R (z i)) := by
  let C := ContinuousLinearMap.mulLeftRight ℝ (H →L[ℝ] H) R R.adjoint
  have hC (v : H) : C (InnerProductSpace.rankOne ℝ v v) =
      InnerProductSpace.rankOne ℝ (R v) (R v) := conjugate_rankOne R v
  change C (empiricalCovariance z) = _
  rw [empiricalCovariance, map_smul, map_sum]
  simp only [hC, empiricalCovariance]

/-- Exact population covariance conjugation, proved by the actual feature
integral. It does not assume any spectral calculus or covariance identity. -/
theorem populationCovariance_conjugation (R : H →L[ℝ] H)
    (k : X → H) (hk : MemLp k 2 μ) :
    R * populationCovariance (featureEmbedding μ k hk) * R.adjoint =
      populationCovariance (featureEmbedding μ (fun y => R (k y)) (R.comp_memLp' hk)) := by
  let C := ContinuousLinearMap.mulLeftRight ℝ (H →L[ℝ] H) R R.adjoint
  have hC (v : H) : C (InnerProductSpace.rankOne ℝ v v) =
      InnerProductSpace.rankOne ℝ (R v) (R v) := conjugate_rankOne R v
  change C (populationCovariance (featureEmbedding μ k hk)) = _
  rw [populationCovariance_eq_integral, ← C.integral_comp_comm (integrable_rankOne_feature k hk)]
  simp only [hC]
  exact (populationCovariance_eq_integral _ (R.comp_memLp' hk)).symm

variable [IsProbabilityMeasure μ]

/-- The normalized empirical covariance in the actual Hilbert--Schmidt space. -/
noncomputable def normalizedHSCovarianceFluctuation (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) {n : ℕ} (x : Fin n → X) :
    HilbertSchmidtColumns ι H :=
  hsCovarianceFluctuation b μ (fun y => featureRegularizedInvSqrt μ k hk lam (k y)) x

/-- The HS vector represents exactly `R (T_X - T) R`, where `R` is the real
constructed inverse square root. No factorization is an input hypothesis. -/
theorem hilbertSchmidtOperator_normalizedHSCovarianceFluctuation
    (b : HilbertBasis ι ℝ H) (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {n : ℕ} (x : Fin n → X) :
    hilbertSchmidtOperator b (normalizedHSCovarianceFluctuation b k hk lam x) =
      featureRegularizedInvSqrt μ k hk lam *
        (empiricalCovariance (fun i => k (x i)) -
          populationCovariance (featureEmbedding μ k hk)) *
            featureRegularizedInvSqrt μ k hk lam := by
  let R := featureRegularizedInvSqrt μ k hk lam
  have ha : R.adjoint = R := (featureRegularizedInvSqrt_isSelfAdjoint k hk lam).adjoint_eq
  change hilbertSchmidtOperator b (hsCovarianceFluctuation b μ (R ∘ k) x) =
    R * (empiricalCovariance (fun i => k (x i)) -
      populationCovariance (featureEmbedding μ k hk)) * R
  rw [hilbertSchmidtOperator_hsCovarianceFluctuation b (R ∘ k) (R.comp_memLp' hk) x]
  change empiricalCovariance (fun i => R (k (x i))) -
    populationCovariance (featureEmbedding μ (fun y => R (k y)) (R.comp_memLp' hk)) = _
  rw [← empiricalCovariance_conjugation R, ← populationCovariance_conjugation R k hk]
  rw [ha]
  noncomm_ring

/-- The actual operator norm perturbation is bounded by the actual HS norm. -/
theorem normalized_covariance_opNorm_le_hs (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) {n : ℕ} (x : Fin n → X) :
    ‖featureRegularizedInvSqrt μ k hk lam *
      (empiricalCovariance (fun i => k (x i)) - populationCovariance (featureEmbedding μ k hk)) *
        featureRegularizedInvSqrt μ k hk lam‖ ≤
          ‖normalizedHSCovarianceFluctuation b k hk lam x‖ := by
  rw [← hilbertSchmidtOperator_normalizedHSCovarianceFluctuation b k hk lam x]
  exact hilbertSchmidtOperator_le b _

variable [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem memLp_normalizedHSCovarianceFluctuation (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    MemLp (fun ω => normalizedHSCovarianceFluctuation b k hk lam (fun i => x i ω)) 2 P :=
  memLp_hsCovarianceFluctuation b hn x hlaw _ (memLp_normalized_feature k hk lam) hL

variable [TopologicalSpace.SeparableSpace H]

/-- The Hilbert–Schmidt covariance second-moment bound, with `N₁(λ)` equal
to integrated leverage. -/
theorem integral_normalizedHSCovarianceFluctuation_sq_le (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    (∫ ω, ‖normalizedHSCovarianceFluctuation b k hk lam (fun i => x i ω)‖ ^ 2 ∂P) ≤
      L / (n : ℝ) * featureEffectiveDimension k hk lam := by
  have h := integral_hsCovarianceFluctuation_sq_le b hn x hlaw hindep _
    (memLp_normalized_feature k hk lam) hL
  change (∫ ω, ‖normalizedHSCovarianceFluctuation b k hk lam (fun i => x i ω)‖ ^ 2 ∂P) ≤
    L / (n : ℝ) * ∫ y, normalizedLeverage k hk lam y ∂μ at h
  rwa [integral_normalizedLeverage_eq_featureEffectiveDimension k hk lam hlam] at h

/-- Explicit tail bound for the actual HS perturbation. The bound is valid
even when the effective dimension vanishes. -/
theorem measure_normalizedHSCovarianceFluctuation_ge_le (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ ‖normalizedHSCovarianceFluctuation b k hk lam (fun i => x i ω)‖} ≤
      ENNReal.ofReal (L / (n : ℝ) * featureEffectiveDimension k hk lam / t ^ 2) := by
  let z : Ω → HilbertSchmidtColumns ι H := fun ω =>
    normalizedHSCovarianceFluctuation b k hk lam (fun i => x i ω)
  have hz : MemLp z 2 P := memLp_normalizedHSCovarianceFluctuation b hn x hlaw k hk lam hL
  have hi := (memLp_two_iff_integrable_sq_norm hz.1).mp hz
  have hm := (hi.div_const (t ^ 2)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (sq_nonneg ‖z ω‖) (sq_nonneg t)))
    (s := {ω | t ≤ ‖z ω‖}) (fun ω hω => by
      rw [le_div_iff₀ (sq_pos_of_pos ht)]
      change t ≤ ‖z ω‖ at hω
      nlinarith [norm_nonneg (z ω)])
  refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (integral_normalizedHSCovarianceFluctuation_sq_le b hn x hlaw hindep k hk lam hlam hL)
    (sq_nonneg t)

end KernelSeq
