import KernelSeq.CuculescuWalsh
import KernelSeq.SchattenFour

/-!
# Actual stopped Walsh supermartingales and their good-part energy

This follows the finite prefix-average version of Randrianantoanina,
Section 3, Lemmas 3.3--3.4 and equations (3.3)--(3.6):
https://arxiv.org/pdf/math/0111264.
All conditional averages are the constructed finite Walsh averages. No
supermartingale, Doob-decomposition, or energy certificate is assumed.
The stopped field is indexed from zero but uses cutoff/prefix level k+1,
so its initial value has already been truncated.
-/

open MeasureTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ}
local instance walshStoppedMeasurableSpace (n : ℕ) : MeasurableSpace (WalshCube n) := ⊤

theorem walshPrefixAverage_add {V : Type*} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (f g : WalshCube n → V) (ω : WalshCube n) :
    walshPrefixAverage k (fun η => f η + g η) ω =
      walshPrefixAverage k f ω + walshPrefixAverage k g ω := by
  simp only [walshPrefixAverage, Finset.sum_add_distrib, smul_add]

theorem walshPrefixAverage_sub {V : Type*} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (f g : WalshCube n → V) (ω : WalshCube n) :
    walshPrefixAverage k (fun η => f η - g η) ω =
      walshPrefixAverage k f ω - walshPrefixAverage k g ω := by
  simp only [walshPrefixAverage, Finset.sum_sub_distrib, smul_sub]

theorem walshPrefixAverage_map {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (f : WalshCube n → V)
    (L : V →ₗ[ℝ] W) (ω : WalshCube n) :
    walshPrefixAverage k (fun η => L (f η)) ω = L (walshPrefixAverage k f ω) := by
  simp only [walshPrefixAverage, map_sum, map_smul]

/-- Actual conditional tower identity, proved by merging finite cube tails. -/
theorem walshPrefixAverage_tower {V : Type*} [AddCommGroup V] [Module ℝ V]
    {k l : ℕ} (hkl : k ≤ l) (f : WalshCube n → V) (ω : WalshCube n) :
    walshPrefixAverage k (walshPrefixAverage l f) ω = walshPrefixAverage k f ω := by
  have hm (η ζ : WalshCube n) :
      walshMerge l (walshMerge k ω η) ζ = walshMerge k ω (walshMerge l η ζ) := by
    funext j
    by_cases hjk : (j : ℕ) < k
    · have hjl : (j : ℕ) < l := lt_of_lt_of_le hjk hkl
      simp only [walshMerge, if_pos hjk, if_pos hjl]
    · simp only [walshMerge, if_neg hjk]
  have he (η : WalshCube n) : walshPrefixAverage l f (walshMerge k ω η) =
      walshPrefixAverage l (fun ζ => f (walshMerge k ω ζ)) η := by
    simp only [walshPrefixAverage, hm]
  change _ • (∑ η : WalshCube n, walshPrefixAverage l f (walshMerge k ω η)) = _
  simp only [he, sum_walshPrefixAverage]
  rfl

theorem WalshAdapted.add {V : Type*} [Add V] {k : ℕ} {f g : WalshCube n → V}
    (hf : WalshAdapted k f) (hg : WalshAdapted k g) : WalshAdapted k (fun ω => f ω + g ω) := by
  intro ω η h
  change f ω + g ω = f η + g η
  rw [hf ω η h, hg ω η h]

theorem WalshAdapted.sub {V : Type*} [Sub V] {k : ℕ} {f g : WalshCube n → V}
    (hf : WalshAdapted k f) (hg : WalshAdapted k g) : WalshAdapted k (fun ω => f ω - g ω) := by
  intro ω η h
  change f ω - g ω = f η - g η
  rw [hf ω η h, hg ω η h]

theorem WalshAdapted.mul {V : Type*} [Mul V] {k : ℕ} {f g : WalshCube n → V}
    (hf : WalshAdapted k f) (hg : WalshAdapted k g) : WalshAdapted k (fun ω => f ω * g ω) := by
  intro ω η h
  change f ω * g ω = f η * g η
  rw [hf ω η h, hg ω η h]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem walshPrefixAverage_mul_left (k : ℕ) (A F : WalshCube n → H →L[ℝ] H)
    (hA : WalshAdapted k A) (ω : WalshCube n) :
    walshPrefixAverage k (fun η => A η * F η) ω = A ω * walshPrefixAverage k F ω := by
  simp only [walshPrefixAverage, hA.merge, ← Finset.mul_sum, mul_smul_comm]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem walshPrefixAverage_mul_right (k : ℕ) (F A : WalshCube n → H →L[ℝ] H)
    (hA : WalshAdapted k A) (ω : WalshCube n) :
    walshPrefixAverage k (fun η => F η * A η) ω = walshPrefixAverage k F ω * A ω := by
  simp only [walshPrefixAverage, hA.merge, ← Finset.sum_mul, smul_mul_assoc]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem walshPrefixAverage_mono (k : ℕ) (A B : WalshCube n → H →L[ℝ] H)
    (hAB : ∀ ω, A ω ≤ B ω) (ω : WalshCube n) :
    walshPrefixAverage k A ω ≤ walshPrefixAverage k B ω := by
  apply (ContinuousLinearMap.le_def _ _).mpr
  rw [← walshPrefixAverage_sub]
  exact walshPrefixAverage_positive _ (fun η => (ContinuousLinearMap.le_def _ _).mp (hAB η)) k ω

/-- The actual new spectral cutoff loses a positive compressed component.
This uses commutation with the compression, not an invalid general claim
that arbitrary smaller projections decrease positive compressions. -/
theorem cuculescuCutoff_compression_le (e X : H →L[ℝ] H)
    (he : IsSelfAdjoint e) (he2 : IsIdempotentElem e) (hX : X.IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    cuculescuCutoff e X he hX lam * X * cuculescuCutoff e X he hX lam ≤ e * X * e := by
  let T := e * X * e
  let D := cuculescuDrop e X he hX lam
  let q := cuculescuCutoff e X he hX lam
  have hDl : e * D = D := cuculescuDrop_left_absorb e X he he2 hX lam hlam
  have hDr : D * e = D := cuculescuDrop_right_absorb e X he he2 hX lam hlam
  have hql : e * q = q := cuculescuCutoff_left_absorb e X he he2 hX lam hlam
  have hqr : q * e = q := cuculescuCutoff_right_absorb e X he he2 hX lam hlam
  have hTe : T * e = T := by dsimp only [T]; simp only [mul_assoc, he2.eq]
  have hDT : D * T = T * D := compactSpectralProjection_commutes _ _ _ _
  have hqT : q * T = T * q := cuculescuCutoff_commutes_compression e X he he2 hX lam
  have hD2 : D * D = D := (cuculescuDrop_idempotent e X he hX lam).eq
  have hq2 : q * q = q := (cuculescuCutoff_idempotent e X he he2 hX lam hlam).eq
  have hDXD : D * T * D = D * X * D := by
    calc
      _ = ((D * e) * X) * (e * D) := by dsimp only [T]; noncomm_ring
      _ = _ := by rw [hDl, hDr]
  have hqXq : q * T * q = q * X * q := by
    calc
      _ = ((q * e) * X) * (e * q) := by dsimp only [T]; noncomm_ring
      _ = _ := by rw [hql, hqr]
  have hdiff : T - q * X * q = D * X * D := by
    calc
      _ = T - T * q := by rw [← hqXq, hqT, mul_assoc, hq2]
      _ = T * (e - q) := by rw [mul_sub, hTe]
      _ = T * D := by simp only [q, cuculescuCutoff, sub_sub_cancel, D]
      _ = D * T * D := by
        calc
          T * D = T * (D * D) := congrArg (fun A : H →L[ℝ] H => T * A) hD2.symm
          _ = (T * D) * D := (mul_assoc T D D).symm
          _ = (D * T) * D := congrArg (fun A : H →L[ℝ] H => A * D) hDT.symm
      _ = _ := hDXD
  apply (ContinuousLinearMap.le_def _ _).mpr
  change (T - q * X * q).IsPositive
  rw [hdiff]
  have hp := hX.conj_adjoint D
  change (D * X * D.adjoint).IsPositive at hp
  have hD : IsSelfAdjoint D := cuculescuDrop_selfAdjoint e X he hX lam
  simpa only [hD.adjoint_eq] using hp

/-- The genuine stopped positive field, at prefix/cutoff level k+1. -/
def walshStoppedField (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) : H →L[ℝ] H :=
  let q := cuculescuWalshProjection F hF lam hlam (k + 1) ω
  q * walshPrefixAverage (k + 1) F ω * q

theorem walshStoppedField_positive
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    (walshStoppedField F hF lam hlam k ω).IsPositive := by
  let q := cuculescuWalshProjection F hF lam hlam (k + 1) ω
  let X := walshPrefixAverage (k + 1) F ω
  have hq : IsSelfAdjoint q := cuculescuWalshProjection_selfAdjoint F hF lam hlam (k + 1) ω
  have hp := (walshPrefixAverage_positive F hF (k + 1) ω).conj_adjoint q
  change (q * X * q.adjoint).IsPositive at hp
  change (q * X * q).IsPositive
  simpa only [hq.adjoint_eq] using hp

theorem walshStoppedField_adapted
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) :
    WalshAdapted (k + 1) (walshStoppedField F hF lam hlam k) :=
  ((cuculescuWalshProjection_adapted F hF lam hlam (k + 1)).mul
    (walshPrefixAverage_adapted (k + 1) F)).mul
      (cuculescuWalshProjection_adapted F hF lam hlam (k + 1))

theorem walshStoppedField_supermartingale
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    walshPrefixAverage (k + 1) (walshStoppedField F hF lam hlam (k + 1)) ω ≤
      walshStoppedField F hF lam hlam k ω := by
  let q := cuculescuWalshProjection F hF lam hlam (k + 1)
  have hq := cuculescuWalshProjection_adapted F hF lam hlam (k + 1)
  have hstep (η : WalshCube n) : walshStoppedField F hF lam hlam (k + 1) η ≤
      q η * walshPrefixAverage (k + 2) F η * q η := by
    change cuculescuWalshProjection F hF lam hlam (k + 2) η * _ *
      cuculescuWalshProjection F hF lam hlam (k + 2) η ≤ _
    rw [show k + 2 = (k + 1) + 1 by omega, cuculescuWalshProjection_succ]
    exact cuculescuCutoff_compression_le _ _ _
      (cuculescuWalshProjection_idempotent F hF lam hlam (k + 1) η) _ _ hlam
  have hh := walshPrefixAverage_mono (k + 1) _ _ hstep ω
  rw [walshPrefixAverage_mul_right _ _ q hq,
    walshPrefixAverage_mul_left _ q _ hq,
    walshPrefixAverage_tower (by omega : k + 1 ≤ k + 2)] at hh
  exact hh

/-- Every stopped field is bounded above by the fixed scalar threshold. -/
theorem walshStoppedField_le_scalar
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    walshStoppedField F hF lam hlam k ω ≤ lam • (1 : H →L[ℝ] H) := by
  have hq : cuculescuWalshProjection F hF lam hlam (k + 1) ω ≤ 1 := by
    simpa only [cuculescuWalshProjection_zero] using
      cuculescuWalshProjection_antitone F hF lam hlam ω (Nat.zero_le (k + 1))
  have hs : lam • cuculescuWalshProjection F hF lam hlam (k + 1) ω ≤
      lam • (1 : H →L[ℝ] H) := by
    apply (ContinuousLinearMap.le_def _ _).mpr
    simpa only [smul_sub] using
      ((ContinuousLinearMap.le_def _ _).mp hq).smul_of_nonneg hlam
  exact (cuculescuWalshProjection_compression_upper F hF lam hlam k ω).trans hs

/-- The actual positive predictable compensator increment. -/
def walshGoodDrift (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) : H →L[ℝ] H :=
  walshStoppedField F hF lam hlam k ω -
    walshPrefixAverage (k + 1) (walshStoppedField F hF lam hlam (k + 1)) ω

theorem walshGoodDrift_positive
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) (ω : WalshCube n) :
    (walshGoodDrift F hF lam hlam k ω).IsPositive :=
  (ContinuousLinearMap.le_def _ _).mp (walshStoppedField_supermartingale F hF lam hlam k ω)

theorem walshGoodDrift_adapted
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) :
    WalshAdapted (k + 1) (walshGoodDrift F hF lam hlam k) :=
  (walshStoppedField_adapted F hF lam hlam k).sub (walshPrefixAverage_adapted _ _)

/-- Actual good martingale in the stopped Doob decomposition. -/
def walshGoodMartingale (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) (ω : WalshCube n) : H →L[ℝ] H :=
  walshStoppedField F hF lam hlam N ω +
    ∑ k ∈ Finset.range N, walshGoodDrift F hF lam hlam k ω

/-- Actual decreasing bad part; its increments are negatives of the
constructed positive predictable drifts. -/
def walshBadPart (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) (ω : WalshCube n) : H →L[ℝ] H :=
  -(∑ k ∈ Finset.range N, walshGoodDrift F hF lam hlam k ω)

theorem walshGoodBad_decomposition
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) (ω : WalshCube n) :
    walshGoodMartingale F hF lam hlam N ω + walshBadPart F hF lam hlam N ω =
      walshStoppedField F hF lam hlam N ω := by
  unfold walshGoodMartingale walshBadPart
  abel

theorem walshGoodMartingale_positive
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) (ω : WalshCube n) :
    (walshGoodMartingale F hF lam hlam N ω).IsPositive :=
  (walshStoppedField_positive F hF lam hlam N ω).add
    (ContinuousLinearMap.isPositive_sum _ (fun k _ => walshGoodDrift_positive F hF lam hlam k ω))

theorem walshGoodMartingale_adapted
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) :
    WalshAdapted (N + 1) (walshGoodMartingale F hF lam hlam N) := by
  intro ω η h
  unfold walshGoodMartingale
  rw [walshStoppedField_adapted F hF lam hlam N ω η h]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact ((walshGoodDrift_adapted F hF lam hlam k).mono (by
    have := Finset.mem_range.mp hk; omega)) ω η h

theorem walshGoodMartingale_succ
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) (ω : WalshCube n) :
    walshGoodMartingale F hF lam hlam (N + 1) ω =
      walshGoodMartingale F hF lam hlam N ω +
        (walshStoppedField F hF lam hlam (N + 1) ω -
          walshPrefixAverage (N + 1) (walshStoppedField F hF lam hlam (N + 1)) ω) := by
  simp only [walshGoodMartingale, Finset.sum_range_succ, walshGoodDrift]
  abel

theorem walshGoodMartingale_martingale
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) (ω : WalshCube n) :
    walshPrefixAverage (N + 1) (walshGoodMartingale F hF lam hlam (N + 1)) ω =
      walshGoodMartingale F hF lam hlam N ω := by
  have heq := funext (walshGoodMartingale_succ F hF lam hlam N)
  rw [heq, walshPrefixAverage_add, walshPrefixAverage_sub,
    walshPrefixAverage_of_adapted (walshGoodMartingale_adapted F hF lam hlam N),
    walshPrefixAverage_of_adapted (walshPrefixAverage_adapted _ _), sub_self, add_zero]

theorem walshBadPart_antitone
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (ω : WalshCube n) :
    Antitone (fun N => walshBadPart F hF lam hlam N ω) := by
  apply antitone_nat_of_succ_le
  intro N
  apply (ContinuousLinearMap.le_def _ _).mpr
  have heq : walshBadPart F hF lam hlam N ω - walshBadPart F hF lam hlam (N + 1) ω =
      walshGoodDrift F hF lam hlam N ω := by
    simp only [walshBadPart, Finset.sum_range_succ]
    abel
  rw [heq]
  exact walshGoodDrift_positive F hF lam hlam N ω

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem finiteBasisTrace_square_sub (b : HilbertBasis ι ℝ H) [Fintype ι]
    (A B : H →L[ℝ] H) :
    basisTrace b ((A - B) * (A - B)) =
      basisTrace b (A * A) - 2 * basisTrace b (A * B) + basisTrace b (B * B) := by
  have hop : (A - B) * (A - B) = (A * A - A * B) - B * A + B * B := by noncomm_ring
  rw [hop]
  simp only [← finiteBasisTraceCLM_apply, map_add, map_sub]
  simp only [finiteBasisTraceCLM_apply, finiteBasisTrace_mul_comm b B A]
  ring

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem finiteBasisTrace_square_add (b : HilbertBasis ι ℝ H) [Fintype ι]
    (A B : H →L[ℝ] H) :
    basisTrace b ((A + B) * (A + B)) =
      basisTrace b (A * A) + 2 * basisTrace b (B * A) + basisTrace b (B * B) := by
  have hop : (A + B) * (A + B) = (A * A + A * B) + B * A + B * B := by noncomm_ring
  rw [hop]
  simp only [← finiteBasisTraceCLM_apply, map_add]
  simp only [finiteBasisTraceCLM_apply, finiteBasisTrace_mul_comm b A B]
  ring

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- Actual finite conditional variance identity, at the level of trace squares. -/
theorem sum_trace_walsh_centered_square (b : HilbertBasis ι ℝ H) [Fintype ι]
    (k : ℕ) (A : WalshCube n → H →L[ℝ] H) :
    (∑ ω : WalshCube n, basisTrace b
      ((A ω - walshPrefixAverage k A ω) * (A ω - walshPrefixAverage k A ω))) =
      (∑ ω : WalshCube n, basisTrace b (A ω * A ω)) -
        ∑ ω : WalshCube n, basisTrace b (walshPrefixAverage k A ω * walshPrefixAverage k A ω) := by
  have hcross := sum_trace_walshPrefixAverage_mul b A (walshPrefixAverage k A)
    (walshPrefixAverage_adapted k A)
  simp_rw [finiteBasisTrace_square_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← hcross]
  ring

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem sum_trace_walsh_centered_mul (b : HilbertBasis ι ℝ H) [Fintype ι]
    (k : ℕ) (A Q : WalshCube n → H →L[ℝ] H) (hQ : WalshAdapted k Q) :
    (∑ ω : WalshCube n, basisTrace b ((A ω - walshPrefixAverage k A ω) * Q ω)) = 0 := by
  have hcross := sum_trace_walshPrefixAverage_mul b A Q hQ
  simp only [sub_mul, ← finiteBasisTraceCLM_apply, map_sub]
  simp only [finiteBasisTraceCLM_apply, Finset.sum_sub_distrib, hcross, sub_self]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- Actual trace-square orthogonality to every genuine adapted field. -/
theorem sum_trace_square_add_walsh_centered (b : HilbertBasis ι ℝ H) [Fintype ι]
    (k : ℕ) (A Q : WalshCube n → H →L[ℝ] H) (hQ : WalshAdapted k Q) :
    (∑ ω : WalshCube n, basisTrace b
      ((Q ω + (A ω - walshPrefixAverage k A ω)) *
        (Q ω + (A ω - walshPrefixAverage k A ω)))) =
      (∑ ω : WalshCube n, basisTrace b (Q ω * Q ω)) +
        ∑ ω : WalshCube n, basisTrace b
          ((A ω - walshPrefixAverage k A ω) * (A ω - walshPrefixAverage k A ω)) := by
  simp_rw [finiteBasisTrace_square_add]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_trace_walsh_centered_mul b k A Q hQ, mul_zero, add_zero]

omit [FiniteDimensional ℝ H] in
/-- Genuine trace comparison for two ordered positive bounded operators.
The operators need not commute. -/
theorem finiteBasisTrace_square_gap_le (b : HilbertBasis ι ℝ H) [Fintype ι]
    (A B : H →L[ℝ] H) (hBA : B ≤ A) (lam : ℝ)
    (hA : A ≤ lam • (1 : H →L[ℝ] H)) :
    basisTrace b (A * A) - basisTrace b (B * B) ≤
      2 * lam * basisTrace b (A - B) := by
  have hD : (A - B).IsPositive := (ContinuousLinearMap.le_def _ _).mp hBA
  have hsum : A + B ≤ (2 * lam) • (1 : H →L[ℝ] H) := by
    apply (ContinuousLinearMap.le_def _ _).mpr
    have hp := ((ContinuousLinearMap.le_def _ _).mp hA).add
      ((ContinuousLinearMap.le_def _ _).mp (hBA.trans hA))
    have heq : (2 * lam) • (1 : H →L[ℝ] H) - (A + B) =
        (lam • (1 : H →L[ℝ] H) - A) + (lam • (1 : H →L[ℝ] H) - B) := by
      rw [two_mul, add_smul]
      abel
    rw [heq]
    exact hp
  have h := finiteBasisTrace_mul_mono b (A - B) (A + B) ((2 * lam) • 1) hD hsum
  have heq : basisTrace b ((A - B) * (A + B)) =
      basisTrace b (A * A) - basisTrace b (B * B) := by
    have hop : (A - B) * (A + B) = (A * A + A * B) - B * A - B * B := by noncomm_ring
    rw [hop]
    simp only [← finiteBasisTraceCLM_apply, map_sub, map_add]
    simp only [finiteBasisTraceCLM_apply, finiteBasisTrace_mul_comm b B A]
    ring
  rw [heq] at h
  simp only [mul_smul_comm, mul_one, ← finiteBasisTraceCLM_apply, map_smul] at h
  simpa only [finiteBasisTraceCLM_apply, smul_eq_mul] using h

/-- Actual one-step good-martingale energy. Conditional variance and trace
order yield a telescoping bound with no energy premise. -/
theorem sum_trace_walshGood_increment_bound (b : HilbertBasis ι ℝ H) [Fintype ι]
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) :
    (∑ ω : WalshCube n, basisTrace b
      ((walshStoppedField F hF lam hlam (k + 1) ω -
          walshPrefixAverage (k + 1) (walshStoppedField F hF lam hlam (k + 1)) ω) *
        (walshStoppedField F hF lam hlam (k + 1) ω -
          walshPrefixAverage (k + 1) (walshStoppedField F hF lam hlam (k + 1)) ω))) ≤
      (∑ ω : WalshCube n, basisTrace b
        (walshStoppedField F hF lam hlam (k + 1) ω * walshStoppedField F hF lam hlam (k + 1) ω)) -
      (∑ ω : WalshCube n, basisTrace b
        (walshStoppedField F hF lam hlam k ω * walshStoppedField F hF lam hlam k ω)) +
      2 * lam * ((∑ ω : WalshCube n, basisTrace b (walshStoppedField F hF lam hlam k ω)) -
        ∑ ω : WalshCube n, basisTrace b (walshStoppedField F hF lam hlam (k + 1) ω)) := by
  let G := walshStoppedField F hF lam hlam
  let B := walshPrefixAverage (k + 1) (G (k + 1))
  have hmean : (∑ ω : WalshCube n, basisTrace b (B ω)) =
      ∑ ω : WalshCube n, basisTrace b (G (k + 1) ω) := by
    simpa only [mul_one] using sum_trace_walshPrefixAverage_mul b (G (k + 1))
      (fun _ => 1) (fun _ _ _ => rfl)
  have hdiff : (∑ ω : WalshCube n, basisTrace b (G k ω - B ω)) =
      (∑ ω : WalshCube n, basisTrace b (G k ω)) - ∑ ω : WalshCube n, basisTrace b (B ω) := by
    simp only [← finiteBasisTraceCLM_apply, map_sub, Finset.sum_sub_distrib]
  have hgap := Finset.sum_le_sum (s := (Finset.univ : Finset (WalshCube n))) (fun ω _ =>
    finiteBasisTrace_square_gap_le b (G k ω) (B ω)
      (walshStoppedField_supermartingale F hF lam hlam k ω) lam
      (walshStoppedField_le_scalar F hF lam hlam k ω))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hdiff, hmean] at hgap
  rw [sum_trace_walsh_centered_square]
  linarith only [hgap]

/-- The genuine telescoping estimate for the actual good martingale. -/
theorem sum_trace_walshGood_square_bound_refined (b : HilbertBasis ι ℝ H) [Fintype ι]
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) :
    (∑ ω : WalshCube n, basisTrace b
      (walshGoodMartingale F hF lam hlam N ω * walshGoodMartingale F hF lam hlam N ω)) ≤
      (∑ ω : WalshCube n, basisTrace b
        (walshStoppedField F hF lam hlam N ω * walshStoppedField F hF lam hlam N ω)) +
      2 * lam * ((∑ ω : WalshCube n, basisTrace b (walshStoppedField F hF lam hlam 0 ω)) -
        ∑ ω : WalshCube n, basisTrace b (walshStoppedField F hF lam hlam N ω)) := by
  induction N with
  | zero => simp only [walshGoodMartingale, Finset.range_zero, Finset.sum_empty, add_zero,
      sub_self, mul_zero, le_refl]
  | succ N ih =>
    have hrec : (∑ ω : WalshCube n, basisTrace b
        (walshGoodMartingale F hF lam hlam (N + 1) ω * walshGoodMartingale F hF lam hlam (N + 1) ω)) =
        (∑ ω : WalshCube n, basisTrace b
          (walshGoodMartingale F hF lam hlam N ω * walshGoodMartingale F hF lam hlam N ω)) +
        ∑ ω : WalshCube n, basisTrace b
          ((walshStoppedField F hF lam hlam (N + 1) ω -
              walshPrefixAverage (N + 1) (walshStoppedField F hF lam hlam (N + 1)) ω) *
            (walshStoppedField F hF lam hlam (N + 1) ω -
              walshPrefixAverage (N + 1) (walshStoppedField F hF lam hlam (N + 1)) ω)) := by
      simp_rw [walshGoodMartingale_succ]
      exact sum_trace_square_add_walsh_centered b (N + 1)
        (walshStoppedField F hF lam hlam (N + 1)) (walshGoodMartingale F hF lam hlam N)
        (walshGoodMartingale_adapted F hF lam hlam N)
    rw [hrec]
    have hinc := sum_trace_walshGood_increment_bound b F hF lam hlam N
    linarith only [ih, hinc]

/-- The initial stopped field's true trace is bounded by the terminal trace. -/
theorem sum_trace_walshStopped_initial_le (b : HilbertBasis ι ℝ H) [Fintype ι]
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∑ ω : WalshCube n, basisTrace b (walshStoppedField F hF lam hlam 0 ω)) ≤
      ∑ ω : WalshCube n, basisTrace b (F ω) := by
  let q := cuculescuWalshProjection F hF lam hlam 1
  have hcyc (ω : WalshCube n) : basisTrace b (walshStoppedField F hF lam hlam 0 ω) =
      basisTrace b (walshPrefixAverage 1 F ω * q ω) := by
    have hh := finiteBasisTrace_mul_cycle b (q ω) (walshPrefixAverage 1 F ω) (q ω)
    rw [(cuculescuWalshProjection_idempotent F hF lam hlam 1 ω).eq] at hh
    exact hh.trans (finiteBasisTrace_mul_comm b _ _)
  simp_rw [hcyc]
  rw [sum_trace_walshPrefixAverage_mul b F q (cuculescuWalshProjection_adapted F hF lam hlam 1)]
  apply Finset.sum_le_sum
  intro ω _
  have hq : q ω ≤ 1 := by
    simpa only [cuculescuWalshProjection_zero] using
      cuculescuWalshProjection_antitone F hF lam hlam ω (Nat.zero_le 1)
  simpa only [mul_one] using finiteBasisTrace_mul_mono b (F ω) (q ω) 1 (hF ω) hq

/-- A genuine finite good-part trace-energy bound. Using the exact finite
conditional variance identity gives constant two, hence also the source's
coarser constant six. The terminal field is positive as in the source's
positive-martingale reduction. -/
theorem sum_trace_walshGood_square_le (b : HilbertBasis ι ℝ H) [Fintype ι]
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) :
    (∑ ω : WalshCube n, basisTrace b
      (walshGoodMartingale F hF lam hlam N ω * walshGoodMartingale F hF lam hlam N ω)) ≤
      2 * lam * ∑ ω : WalshCube n, basisTrace b (F ω) := by
  have hGN : (∑ ω : WalshCube n, basisTrace b
      (walshStoppedField F hF lam hlam N ω * walshStoppedField F hF lam hlam N ω)) ≤
      lam * ∑ ω : WalshCube n, basisTrace b (walshStoppedField F hF lam hlam N ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    have h := finiteBasisTrace_mul_mono b (walshStoppedField F hF lam hlam N ω)
      (walshStoppedField F hF lam hlam N ω) (lam • 1)
      (walshStoppedField_positive F hF lam hlam N ω)
      (walshStoppedField_le_scalar F hF lam hlam N ω)
    simp only [mul_smul_comm, mul_one, ← finiteBasisTraceCLM_apply, map_smul] at h
    simpa only [finiteBasisTraceCLM_apply, smul_eq_mul] using h
  have hnonneg : 0 ≤ ∑ ω : WalshCube n, basisTrace b (walshStoppedField F hF lam hlam N ω) :=
    Finset.sum_nonneg (fun ω _ => finiteBasisTrace_nonneg b _ (walshStoppedField_positive F hF lam hlam N ω))
  have hi := mul_le_mul_of_nonneg_left (sum_trace_walshStopped_initial_le b F hF lam hlam)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlam)
  have href := sum_trace_walshGood_square_bound_refined b F hF lam hlam N
  have hp := mul_nonneg hlam hnonneg
  linarith only [href, hGN, hi, hp]

/-- The actual good martingale has the required genuine HS second moment.
Every column is constructed from the finite basis; no norm/trace identity
or good-part energy bound is assumed. -/
theorem integral_hs_walshGood_energy_le (b : HilbertBasis ι ℝ H) [Fintype ι]
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) (N : ℕ) :
    (∫ ω, ‖finiteOperatorColumns b (walshGoodMartingale F hF lam hlam N ω)‖ ^ 2
      ∂walshUniformMeasure n) ≤
      2 * lam * ∫ ω, basisTrace b (F ω) ∂walshUniformMeasure n := by
  have heq (ω : WalshCube n) : ‖finiteOperatorColumns b (walshGoodMartingale F hF lam hlam N ω)‖ ^ 2 =
      basisTrace b (walshGoodMartingale F hF lam hlam N ω * walshGoodMartingale F hF lam hlam N ω) := by
    rw [finiteOperatorColumns_norm_sq_trace,
      (walshGoodMartingale_positive F hF lam hlam N ω).isSelfAdjoint.adjoint_eq]
  simp only [integral_walshUniform_eq, smul_eq_mul, heq]
  have h := mul_le_mul_of_nonneg_left (sum_trace_walshGood_square_le b F hF lam hlam N)
    (show 0 ≤ (Fintype.card (WalshCube n) : ℝ)⁻¹ by positivity)
  nlinarith only [h]

/-- Actual later projections absorb every earlier projection. This is
derived from the constructed successive corner inclusions. -/
theorem cuculescuWalshProjection_mul_earlier
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) {k N : ℕ} (hkN : k ≤ N) (ω : WalshCube n) :
    cuculescuWalshProjection F hF lam hlam N ω * cuculescuWalshProjection F hF lam hlam k ω =
      cuculescuWalshProjection F hF lam hlam N ω := by
  induction N generalizing k with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    simp
  | succ N ih =>
    by_cases hk : k ≤ N
    · let q := fun j => cuculescuWalshProjection F hF lam hlam j ω
      have hstep : q (N + 1) * q N = q (N + 1) := by
        dsimp only [q]
        rw [cuculescuWalshProjection_succ]
        exact cuculescuCutoff_right_absorb _ _ _
          (cuculescuWalshProjection_idempotent F hF lam hlam N ω) _ _ hlam
      change q (N + 1) * q k = q (N + 1)
      calc
        _ = (q (N + 1) * q N) * q k := congrArg (fun A : H →L[ℝ] H => A * q k) hstep.symm
        _ = q (N + 1) * (q N * q k) := mul_assoc _ _ _
        _ = q (N + 1) * q N := congrArg (fun A : H →L[ℝ] H => q (N + 1) * A) (ih hk)
        _ = _ := hstep
    · have hkeq : k = N + 1 := by omega
      subst k
      exact (cuculescuWalshProjection_idempotent F hF lam hlam (N + 1) ω).eq

theorem cuculescuWalshProjection_earlier_mul
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) {k N : ℕ} (hkN : k ≤ N) (ω : WalshCube n) :
    cuculescuWalshProjection F hF lam hlam k ω * cuculescuWalshProjection F hF lam hlam N ω =
      cuculescuWalshProjection F hF lam hlam N ω := by
  have hh := congrArg star (cuculescuWalshProjection_mul_earlier F hF lam hlam hkN ω)
  simpa only [star_mul, (cuculescuWalshProjection_selfAdjoint F hF lam hlam k ω).star_eq,
    (cuculescuWalshProjection_selfAdjoint F hF lam hlam N ω).star_eq] using hh

/-- Inside the final good corner, every stopped field is exactly its
original prefix field. This is the genuine operator identity used before
the weak-type transform estimate, rather than a support certificate. -/
theorem walshStoppedField_final_corner
    (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, (F ω).IsPositive)
    (lam : ℝ) (hlam : 0 ≤ lam) {k N : ℕ} (hkN : k ≤ N) (ω : WalshCube n) :
    let Q := cuculescuWalshProjection F hF lam hlam (N + 1) ω
    Q * walshStoppedField F hF lam hlam k ω * Q =
      Q * walshPrefixAverage (k + 1) F ω * Q := by
  dsimp only [walshStoppedField]
  have hl := cuculescuWalshProjection_mul_earlier F hF lam hlam (Nat.succ_le_succ hkN) ω
  have hr := cuculescuWalshProjection_earlier_mul F hF lam hlam (Nat.succ_le_succ hkN) ω
  calc
    _ = ((cuculescuWalshProjection F hF lam hlam (N + 1) ω *
        cuculescuWalshProjection F hF lam hlam (k + 1) ω) * walshPrefixAverage (k + 1) F ω) *
        (cuculescuWalshProjection F hF lam hlam (k + 1) ω *
          cuculescuWalshProjection F hF lam hlam (N + 1) ω) := by noncomm_ring
    _ = _ := by rw [hl, hr]

end
end KernelSeq
