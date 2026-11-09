import KernelSeq.WalshStoppedEnergy
import KernelSeq.FiniteSingularDistribution

/-!
# Actual finite Walsh weak-type martingale transforms

The positive-input finite Walsh case of Randrianantoanina, Theorem 3.1,
https://arxiv.org/pdf/math/0111264. The genuine stopped decomposition and
energy bound come from WalshStoppedEnergy. Every original increment retains
its final-corner conjugation. No weak-type or Gundy bound is a premise.
-/

open MeasureTheory
open scoped BigOperators
namespace KernelSeq
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H]
local instance walshWeakMeasurableSpace (n : ℕ) : MeasurableSpace (WalshCube n) := ⊤

/-- Actual transform of the first N differences, retaining the initial value. -/
def finiteWalshTransform (X : ℕ → WalshCube n → H →L[ℝ] H)
    (σ : ℕ → ℝ) (N : ℕ) (ω : WalshCube n) : H →L[ℝ] H :=
  X 0 ω + ∑ k ∈ Finset.range N, σ k • (X (k + 1) ω - X k ω)

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem finiteWalshTransform_succ (X : ℕ → WalshCube n → H →L[ℝ] H)
    (σ : ℕ → ℝ) (N : ℕ) (ω : WalshCube n) :
    finiteWalshTransform X σ (N + 1) ω =
      finiteWalshTransform X σ N ω + σ N • (X (N + 1) ω - X N ω) := by
  simp only [finiteWalshTransform, Finset.sum_range_succ]
  abel

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem finiteWalshTransform_adapted (X : ℕ → WalshCube n → H →L[ℝ] H)
    (hX : ∀ k, WalshAdapted (k + 1) (X k)) (σ : ℕ → ℝ) (N : ℕ) :
    WalshAdapted (N + 1) (finiteWalshTransform X σ N) := by
  intro ω η h
  unfold finiteWalshTransform
  rw [(hX 0).mono (by omega) ω η h]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkN := Finset.mem_range.mp hk
  rw [(hX (k + 1)).mono (by omega) ω η h, (hX k).mono (by omega) ω η h]

omit [FiniteDimensional ℝ H] in
theorem finiteWalshTransform_selfAdjoint (X : ℕ → WalshCube n → H →L[ℝ] H)
    (hX : ∀ k ω, IsSelfAdjoint (X k ω)) (σ : ℕ → ℝ) (N : ℕ) (ω : WalshCube n) :
    IsSelfAdjoint (finiteWalshTransform X σ N ω) := by
  change star (finiteWalshTransform X σ N ω) = finiteWalshTransform X σ N ω
  simp only [finiteWalshTransform, star_add, star_sum, star_smul, star_sub,
    (hX _ _).star_eq, star_trivial]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem finiteBasisTrace_square_add_smul {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (s : ℝ) :
    basisTrace b ((A + s • B) * (A + s • B)) =
      basisTrace b (A * A) + 2 * s * basisTrace b (B * A) + s ^ 2 * basisTrace b (B * B) := by
  rw [finiteBasisTrace_square_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← finiteBasisTraceCLM_apply, map_smul]
  simp only [finiteBasisTraceCLM_apply, smul_eq_mul]
  ring

/-- Actual L2 trace isometry of the constructed good martingale's
deterministic sign transform. -/
theorem sum_trace_walshGood_transform_square {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) :
    (∑ ω : WalshCube n, basisTrace b
      (finiteWalshTransform (walshGoodMartingale F hF lam hlam) σ N ω *
        finiteWalshTransform (walshGoodMartingale F hF lam hlam) σ N ω)) =
      ∑ ω : WalshCube n, basisTrace b
        (walshGoodMartingale F hF lam hlam N ω * walshGoodMartingale F hF lam hlam N ω) := by
  let Y := walshGoodMartingale F hF lam hlam
  let G := walshStoppedField F hF lam hlam
  have hsign (k : ℕ) : σ k ^ 2 = 1 := by nlinarith [sq_abs (σ k), hσ k]
  induction N with
  | zero => simp only [finiteWalshTransform, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ N ih =>
    have hcross := sum_trace_walsh_centered_mul b (N + 1) (G (N + 1))
      (finiteWalshTransform Y σ N)
      (finiteWalshTransform_adapted Y (walshGoodMartingale_adapted F hF lam hlam) σ N)
    have hYrec := sum_trace_square_add_walsh_centered b (N + 1) (G (N + 1)) (Y N)
      (walshGoodMartingale_adapted F hF lam hlam N)
    have hstep (ω : WalshCube n) : finiteWalshTransform Y σ (N + 1) ω =
        finiteWalshTransform Y σ N ω + σ N •
          (G (N + 1) ω - walshPrefixAverage (N + 1) (G (N + 1)) ω) := by
      rw [finiteWalshTransform_succ]
      have hh := walshGoodMartingale_succ F hF lam hlam N ω
      change Y (N + 1) ω = Y N ω + _ at hh
      rw [hh, add_sub_cancel_left]
    have hrec : (∑ ω : WalshCube n, basisTrace b
        (finiteWalshTransform Y σ (N + 1) ω * finiteWalshTransform Y σ (N + 1) ω)) =
        (∑ ω : WalshCube n, basisTrace b
          (finiteWalshTransform Y σ N ω * finiteWalshTransform Y σ N ω)) +
        ∑ ω : WalshCube n, basisTrace b
          ((G (N + 1) ω - walshPrefixAverage (N + 1) (G (N + 1)) ω) *
            (G (N + 1) ω - walshPrefixAverage (N + 1) (G (N + 1)) ω)) := by
      simp_rw [hstep, finiteBasisTrace_square_add_smul]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hcross, hsign, mul_zero,
        add_zero, one_mul]
    have hY (ω : WalshCube n) : Y (N + 1) ω = Y N ω +
        (G (N + 1) ω - walshPrefixAverage (N + 1) (G (N + 1)) ω) :=
      walshGoodMartingale_succ F hF lam hlam N ω
    change _ = ∑ ω : WalshCube n, basisTrace b (Y (N + 1) ω * Y (N + 1) ω)
    simp_rw [hY]
    rw [hYrec, hrec]
    exact congrArg (fun x : ℝ => x + _) ih

omit [FiniteDimensional ℝ H] in
/-- Positive products make all actual cross terms of the drift sum
nonnegative, so deterministic signs cannot increase its trace square. -/
theorem finite_signed_positive_square_le {ι J : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (s : Finset J) (D : J → H →L[ℝ] H)
    (hD : ∀ j ∈ s, (D j).IsPositive) (σ : J → ℝ) (hσ : ∀ j ∈ s, |σ j| ≤ 1) :
    basisTrace b ((∑ j ∈ s, σ j • D j) * (∑ j ∈ s, σ j • D j)) ≤
      basisTrace b ((∑ j ∈ s, D j) * (∑ j ∈ s, D j)) := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← finiteBasisTraceCLM_apply, map_sum, map_smul]
  simp only [finiteBasisTraceCLM_apply, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hn := finiteBasisTrace_mul_nonneg b (D j) (D i) (hD j hj) (hD i hi)
  have hs : σ i * σ j ≤ 1 := by
    calc
      _ ≤ |σ i * σ j| := le_abs_self _
      _ = |σ i| * |σ j| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hσ i hi) (hσ j hj) (abs_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right hs hn).trans_eq (one_mul _)

omit [FiniteDimensional ℝ H] in
/-- Positive Loewner comparison genuinely increases the finite trace square. -/
theorem finiteBasisTrace_square_mono_positive {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H)
    (hA : A.IsPositive) (hB : B.IsPositive) (hAB : A ≤ B) :
    basisTrace b (A * A) ≤ basisTrace b (B * B) := by
  have hn := finiteBasisTrace_mul_nonneg b (B - A) (B + A)
    ((ContinuousLinearMap.le_def _ _).mp hAB) (hB.add hA)
  have hop : (B - A) * (B + A) = (B * B + B * A) - A * B - A * A := by noncomm_ring
  rw [hop] at hn
  simp only [← finiteBasisTraceCLM_apply, map_sub, map_add] at hn
  simp only [finiteBasisTraceCLM_apply, finiteBasisTrace_mul_comm b A B] at hn
  linarith only [hn]

theorem walshDrift_transform_square_le_good {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| ≤ 1) (N : ℕ) (ω : WalshCube n) :
    basisTrace b ((∑ k ∈ Finset.range N, σ k • walshGoodDrift F hF lam hlam k ω) *
      (∑ k ∈ Finset.range N, σ k • walshGoodDrift F hF lam hlam k ω)) ≤
      basisTrace b (walshGoodMartingale F hF lam hlam N ω * walshGoodMartingale F hF lam hlam N ω) := by
  let D := fun k => walshGoodDrift F hF lam hlam k ω
  have hD : (∑ k ∈ Finset.range N, D k).IsPositive :=
    ContinuousLinearMap.isPositive_sum _ (fun k _ => walshGoodDrift_positive F hF lam hlam k ω)
  have hle : (∑ k ∈ Finset.range N, D k) ≤ walshGoodMartingale F hF lam hlam N ω := by
    apply (ContinuousLinearMap.le_def _ _).mpr
    simpa only [walshGoodMartingale, D, add_sub_cancel_right] using walshStoppedField_positive F hF lam hlam N ω
  exact (finite_signed_positive_square_le b (Finset.range N) D
    (fun k _ => walshGoodDrift_positive F hF lam hlam k ω) σ (fun k _ => hσ k)).trans
      (finiteBasisTrace_square_mono_positive b _ _ hD (walshGoodMartingale_positive F hF lam hlam N ω) hle)

theorem walshStopped_transform_decomposition
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : ℕ → ℝ) (N : ℕ) (ω : WalshCube n) :
    finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω =
      finiteWalshTransform (walshGoodMartingale F hF lam hlam) σ N ω -
        ∑ k ∈ Finset.range N, σ k • walshGoodDrift F hF lam hlam k ω := by
  have hd (k : ℕ) : walshStoppedField F hF lam hlam (k + 1) ω - walshStoppedField F hF lam hlam k ω =
      (walshGoodMartingale F hF lam hlam (k + 1) ω - walshGoodMartingale F hF lam hlam k ω) -
        walshGoodDrift F hF lam hlam k ω := by
    rw [walshGoodMartingale_succ]
    unfold walshGoodDrift
    abel
  have hz : walshGoodMartingale F hF lam hlam 0 ω = walshStoppedField F hF lam hlam 0 ω := by
    simp only [walshGoodMartingale, Finset.range_zero, Finset.sum_empty, add_zero]
  simp only [finiteWalshTransform, hd, smul_sub, Finset.sum_sub_distrib, hz]
  abel

omit [FiniteDimensional ℝ H] in
theorem finiteBasisTrace_square_sub_le_two {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    basisTrace b ((A - B) * (A - B)) ≤ 2 * basisTrace b (A * A) + 2 * basisTrace b (B * B) := by
  have hn := finiteBasisTrace_nonneg b _ (operator_square_isPositive_of_isSelfAdjoint (A + B) (hA.add hB))
  rw [finiteBasisTrace_square_add, finiteBasisTrace_mul_comm b B A] at hn
  rw [finiteBasisTrace_square_sub]
  linarith only [hn]

/-- Genuine stopped-transform trace energy, from the actual good/bad
decomposition, actual L2 isometry, and positive drift products. -/
theorem sum_trace_walshStopped_transform_le {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) :
    (∑ ω : WalshCube n, basisTrace b
      (finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω *
        finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω)) ≤
      8 * lam * ∑ ω : WalshCube n, basisTrace b (F ω) := by
  have hpoint (ω : WalshCube n) : basisTrace b
      (finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω *
        finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω) ≤
      2 * basisTrace b (finiteWalshTransform (walshGoodMartingale F hF lam hlam) σ N ω *
        finiteWalshTransform (walshGoodMartingale F hF lam hlam) σ N ω) +
      2 * basisTrace b (walshGoodMartingale F hF lam hlam N ω * walshGoodMartingale F hF lam hlam N ω) := by
    rw [walshStopped_transform_decomposition]
    have hgood := finiteWalshTransform_selfAdjoint (walshGoodMartingale F hF lam hlam)
      (fun k η => (walshGoodMartingale_positive F hF lam hlam k η).isSelfAdjoint) σ N ω
    have hbad : IsSelfAdjoint (∑ k ∈ Finset.range N, σ k • walshGoodDrift F hF lam hlam k ω) := by
      change star _ = _
      simp only [star_sum, star_smul, star_trivial, (walshGoodDrift_positive F hF lam hlam _ ω).isSelfAdjoint.star_eq]
    exact (finiteBasisTrace_square_sub_le_two b _ _ hgood hbad).trans
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (walshDrift_transform_square_le_good b F hF lam hlam σ (fun k => (hσ k).le) N ω) (by norm_num : (0 : ℝ) ≤ 2)))
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ (Finset.univ : Finset (WalshCube n))) => hpoint ω)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_trace_walshGood_transform_square b F hF lam hlam σ hσ N] at hsum
  have henergy := sum_trace_walshGood_square_le b F hF lam hlam N
  linarith only [hsum, henergy]

theorem sum_hs_walshStopped_transform_le {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) :
    (∑ ω : WalshCube n, ‖finiteOperatorColumns b
      (finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω)‖ ^ 2) ≤
      8 * lam * ∑ ω : WalshCube n, basisTrace b (F ω) := by
  have heq (ω : WalshCube n) : ‖finiteOperatorColumns b
      (finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω)‖ ^ 2 = basisTrace b
        (finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω *
          finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω) := by
    rw [finiteOperatorColumns_norm_sq_trace,
      (finiteWalshTransform_selfAdjoint (walshStoppedField F hF lam hlam)
        (fun k η => (walshStoppedField_positive F hF lam hlam k η).isSelfAdjoint) σ N ω).adjoint_eq]
  simp_rw [heq]
  exact sum_trace_walshStopped_transform_le b F hF lam hlam σ hσ N

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem finiteWalshTransform_corner (X : ℕ → WalshCube n → H →L[ℝ] H)
    (σ : ℕ → ℝ) (N : ℕ) (ω : WalshCube n) (Q : H →L[ℝ] H) :
    finiteWalshTransform (fun k η => Q * X k η * Q) σ N ω = Q * finiteWalshTransform X σ N ω * Q := by
  simp only [finiteWalshTransform, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]

theorem walshTransform_final_corner
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : ℕ → ℝ) (N : ℕ) (ω : WalshCube n) :
    let Q := cuculescuWalshProjection F hF lam hlam (N + 1) ω
    Q * finiteWalshTransform (fun k => walshPrefixAverage (k + 1) F) σ N ω * Q =
      Q * finiteWalshTransform (walshStoppedField F hF lam hlam) σ N ω * Q := by
  dsimp only
  rw [← finiteWalshTransform_corner, ← finiteWalshTransform_corner]
  unfold finiteWalshTransform
  dsimp only
  rw [walshStoppedField_final_corner F hF lam hlam (Nat.zero_le N) ω]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkN := Finset.mem_range.mp hk
  rw [walshStoppedField_final_corner F hF lam hlam (by omega : k + 1 ≤ N) ω,
    walshStoppedField_final_corner F hF lam hlam (by omega : k ≤ N) ω]

omit [CompleteSpace H] in
/-- The actual trace of a finite idempotent equals its actual range rank. -/
theorem finiteProjection_trace_eq_rank {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (P : H →L[ℝ] H) (hP : IsIdempotentElem P) :
    basisTrace b P = (Module.finrank ℝ P.range : ℝ) := by
  rw [finiteBasisTrace_eq_linearTrace]
  exact (LinearMap.IsIdempotentElem.isProj_range P.toLinearMap
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).trace

omit [FiniteDimensional ℝ H] in
/-- Actual Hilbert--Schmidt contraction by an orthogonal projection on
both sides, derived from the already proved real Schatten ideal bound. -/
theorem finiteProjection_hs_corner_le {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A Q : H →L[ℝ] H)
    (hQ : IsSelfAdjoint Q) (hQ2 : IsIdempotentElem Q) :
    ‖finiteOperatorColumns b (Q * A * Q)‖ ≤ ‖finiteOperatorColumns b A‖ := by
  let c := finiteOperatorColumns b A
  let d := hsLeftComposition Q (hsRightComposition b b b Q c)
  have hrec : hilbertSchmidtOperator b d = Q * A * Q := by
    simp only [d, hilbertSchmidtOperator_leftComposition, hilbertSchmidtOperator_rightComposition,
      c, hilbertSchmidtOperator_finiteOperatorColumns]
    ext x
    rfl
  have heq := hsSchattenNorm_reconstruction_eq b b (finiteOperatorColumns b (Q * A * Q)) d
    ((hilbertSchmidtOperator_finiteOperatorColumns b _).trans hrec.symm) 2
  have hn := hsSchattenNorm_twoSidedComposition_le b b b Q Q c (by norm_num : (2 : ℝ) ≤ 2)
  simp only [hsSchattenNorm_two] at heq hn
  have hnorm : ‖Q‖ ≤ 1 := IsStarProjection.norm_le Q ⟨hQ2, hQ⟩
  rw [heq]
  calc
    _ ≤ ‖Q‖ * ‖c‖ * ‖Q‖ := hn
    _ ≤ 1 * ‖c‖ * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) hnorm
      (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg _))
    _ = _ := by simp only [one_mul, mul_one, c]

/-- The actual count of singular values of a finite-rank operator never
exceeds that operator's actual rank. -/
theorem finiteSingularCount_le_rank (A : H →L[ℝ] H) {t : ℝ} (ht : 0 ≤ t) :
    finiteSingularCount A t ≤ Module.finrank ℝ A.range := by
  apply (finiteSingularCount_le_iff A ht _).mpr
  have h := finiteSingularValue_le_rank_approximation A A (Module.finrank ℝ A.range) le_rfl
  have hz : A.toLinearMap.singularValues (Module.finrank ℝ A.range) ≤ 0 := by
    simpa only [sub_self, norm_zero] using h
  exact hz.trans ht

omit [CompleteSpace H] in
/-- The two actual off-corner terms have combined rank at most twice the
discarded projection rank; no support-rank certificate is assumed. -/
theorem finiteProjection_offCorner_rank_le (A Q : H →L[ℝ] H) :
    Module.finrank ℝ (A - Q * A * Q).range ≤ 2 * Module.finrank ℝ (1 - Q).range := by
  have heq : A - Q * A * Q = (1 - Q) * A * Q + A * (1 - Q) := by noncomm_ring
  rw [heq]
  exact (finiteOperator_rank_add_le _ _).trans (by
    have hl := (finiteOperator_rank_mul_le_left ((1 - Q) * A) Q).trans
      (finiteOperator_rank_mul_le_left (1 - Q) A)
    have hr := finiteOperator_rank_mul_le_right A (1 - Q)
    omega)

/-- Actual singular-count splitting into a compressed part and two
finite-rank off-corner terms. -/
theorem finiteProjection_count_split (A Q : H →L[ℝ] H) {t : ℝ} (ht : 0 ≤ t) :
    finiteSingularCount A t ≤ finiteSingularCount (Q * A * Q) (t / 2) +
      2 * Module.finrank ℝ (1 - Q).range := by
  have hs := finiteSingularCount_add_le (Q * A * Q) (A - Q * A * Q)
    (show 0 ≤ t / 2 by positivity) (show 0 ≤ t / 2 by positivity)
  have heq : Q * A * Q + (A - Q * A * Q) = A := by abel
  rw [heq, show t / 2 + t / 2 = t by ring] at hs
  exact hs.trans (Nat.add_le_add_left ((finiteSingularCount_le_rank _ (by positivity)).trans
    (finiteProjection_offCorner_rank_le A Q)) _)

/-- Genuine pointwise count/HS/trace splitting for an actual orthogonal
projection. All support ranks and moment estimates are derived. -/
theorem finiteProjection_count_hs_trace_bound {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A Q : H →L[ℝ] H) (hQ : IsIdempotentElem Q)
    {t : ℝ} (ht : 0 ≤ t) :
    (finiteSingularCount A t : ℝ) * (t / 2) ^ 2 ≤
      ‖finiteOperatorColumns b (Q * A * Q)‖ ^ 2 + 2 * basisTrace b (1 - Q) * (t / 2) ^ 2 := by
  have hc : (finiteSingularCount A t : ℝ) ≤ (finiteSingularCount (Q * A * Q) (t / 2) : ℝ) +
      2 * (Module.finrank ℝ (1 - Q).range : ℝ) := by
    exact_mod_cast finiteProjection_count_split A Q ht
  have hp := finiteSingularCount_mul_rpow_le b (Q * A * Q) (p := 2) (by positivity : 0 ≤ t / 2) (by norm_num)
  simp only [Real.rpow_two, hsSchattenNorm_two] at hp
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg (t / 2))
  rw [← finiteProjection_trace_eq_rank b (1 - Q) (IsIdempotentElem.one_sub hQ)] at hmul
  nlinarith only [hmul, hp]

/-- The actual transform of the terminal field's prefix averages. -/
def walshPrefixTransform (F : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (N : ℕ)
    (ω : WalshCube n) : H →L[ℝ] H :=
  finiteWalshTransform (fun k => walshPrefixAverage (k + 1) F) σ N ω

/-- Actual final-corner HS energy of the original prefix transform. -/
theorem sum_hs_walshPrefix_corner_le {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) :
    (∑ ω : WalshCube n, ‖finiteOperatorColumns b
      (cuculescuWalshProjection F hF lam hlam (N + 1) ω * walshPrefixTransform F σ N ω *
        cuculescuWalshProjection F hF lam hlam (N + 1) ω)‖ ^ 2) ≤
      8 * lam * ∑ ω : WalshCube n, basisTrace b (F ω) := by
  apply (Finset.sum_le_sum (fun ω (_ : ω ∈ (Finset.univ : Finset (WalshCube n))) => ?_)).trans
    (sum_hs_walshStopped_transform_le b F hF lam hlam σ hσ N)
  change ‖finiteOperatorColumns b
    (cuculescuWalshProjection F hF lam hlam (N + 1) ω *
      finiteWalshTransform (fun k => walshPrefixAverage (k + 1) F) σ N ω *
      cuculescuWalshProjection F hF lam hlam (N + 1) ω)‖ ^ 2 ≤ _
  rw [walshTransform_final_corner F hF lam hlam σ N ω]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (finiteProjection_hs_corner_le b _ _
      (cuculescuWalshProjection_selfAdjoint F hF lam hlam (N + 1) ω)
      (cuculescuWalshProjection_idempotent F hF lam hlam (N + 1) ω))

/-- Genuine weak-(1,1) singular-count estimate for deterministic sign
transforms of positive terminal fields on the finite Walsh cube. The
threshold-dependent cutoff is the actual construction at lam=t/4. -/
theorem sum_walshPrefixTransform_weak_one_positive {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    t * (∑ ω : WalshCube n, (finiteSingularCount (walshPrefixTransform F σ N ω) t : ℝ)) ≤
      16 * ∑ ω : WalshCube n, basisTrace b (F ω) := by
  let lam := t / 4
  have hlam : 0 ≤ lam := by dsimp only [lam]; positivity
  let Q := cuculescuWalshProjection F hF lam hlam (N + 1)
  let A := walshPrefixTransform F σ N
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (WalshCube n))) (fun ω _ =>
    finiteProjection_count_hs_trace_bound b (A ω) (Q ω)
      (cuculescuWalshProjection_idempotent F hF lam hlam (N + 1) ω) ht.le)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at hs
  have he := sum_hs_walshPrefix_corner_le b F hF lam hlam σ hσ N
  have hp := sum_trace_cuculescuWalsh_tail_bound b F hF lam hlam (N + 1)
  have hpay := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * t by positivity)
  change _ ≤ 16 * ∑ ω : WalshCube n, basisTrace b (F ω)
  apply (mul_le_mul_iff_right₀ ht).mp
  dsimp only [lam] at he hpay
  change (∑ ω : WalshCube n, (finiteSingularCount (A ω) t : ℝ)) * (t / 2) ^ 2 ≤
    (∑ ω : WalshCube n, ‖finiteOperatorColumns b (Q ω * A ω * Q ω)‖ ^ 2) +
      2 * (∑ ω : WalshCube n, basisTrace b (1 - Q ω)) * (t / 2) ^ 2 at hs
  change (∑ ω : WalshCube n, ‖finiteOperatorColumns b (Q ω * A ω * Q ω)‖ ^ 2) ≤ _ at he
  change 2 * t * (t / 4 * ∑ ω : WalshCube n, basisTrace b (1 - Q ω)) ≤ _ at hpay
  dsimp only [A] at hs he
  nlinarith only [hs, he, hpay]

/-- The actual uniform-probability version of the proved positive-input
finite Walsh weak-(1,1) estimate. No weak bound is an input hypothesis. -/
theorem integral_walshPrefixTransform_weak_one_positive {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    t * (∫ ω, (finiteSingularCount (walshPrefixTransform F σ N ω) t : ℝ) ∂walshUniformMeasure n) ≤
      16 * ∫ ω, basisTrace b (F ω) ∂walshUniformMeasure n := by
  simp only [integral_walshUniform_eq, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (sum_walshPrefixTransform_weak_one_positive b F hF σ hσ N ht)
    (show 0 ≤ (Fintype.card (WalshCube n) : ℝ)⁻¹ by positivity)
  nlinarith only [h]

end
end KernelSeq
