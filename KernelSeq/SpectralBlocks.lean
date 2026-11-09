import KernelSeq.ContinuousCompactCalculus
import KernelSeq.SpectralEnergy
import KernelSeq.SpectralSeparation
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Actual separated spectral blocks and their Sylvester multiplier

Spectral subspaces are ranges of constructed indicator multipliers on the
actual compact eigenbasis. Their completeness, invariance, and high/low bounds
are proved, rather than provided as certificates. The two operators need not
commute and their ambient real Hilbert spaces need not be separable.
-/

open LinearMap Module.End Submodule

namespace KernelSeq

noncomputable section
attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual spectral projection associated with a set of real eigenvalues. -/
noncomputable def compactSpectralProjection (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) : H →L[ℝ] H := by
  classical
  exact compactSpectralMultiplier T hc hp (fun t => if t ∈ s then 1 else 0) 1 zero_le_one
    (fun t _ => by split_ifs <;> norm_num)

@[simp]
theorem compactSpectralProjection_repr (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) (x : H)
    (i : CompactSpectralIndex T) :
    (compactEigenbasis T hc hp.isSymmetric).repr (compactSpectralProjection T hc hp s x) i =
      (if i.1 ∈ s then 1 else 0) * (compactEigenbasis T hc hp.isSymmetric).repr x i := by
  classical
  exact compactSpectralMultiplier_repr _ _ _ _ _ _ _ _ _

theorem compactSpectralProjection_isIdempotent (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    IsIdempotentElem (compactSpectralProjection T hc hp s) := by
  classical
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [mul_apply_eq_comp, compactSpectralProjection_repr]
  split_ifs <;> simp

theorem compactSpectralProjection_isSymmetric (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    (compactSpectralProjection T hc hp s).IsSymmetric := by
  unfold compactSpectralProjection compactSpectralMultiplier
  exact hilbertDiagonal_isSymmetric _ _ _ _ _

theorem compactSpectralProjection_norm_le_one (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    ‖compactSpectralProjection T hc hp s‖ ≤ 1 := by
  unfold compactSpectralProjection
  apply compactSpectralMultiplier_norm_le

/-- The actual spectral space is the range of its actual indicator projection. -/
abbrev SpectralSubspace (T : H →L[ℝ] H) (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :=
  (compactSpectralProjection T hc hp s).range

theorem spectralSubspace_isClosed (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    IsClosed (SpectralSubspace T hc hp s : Set H) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range (compactSpectralProjection_isIdempotent T hc hp s)

instance spectralSubspace_completeSpace (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    CompleteSpace (SpectralSubspace T hc hp s) :=
  (spectralSubspace_isClosed T hc hp s).completeSpace_coe

theorem compactSpectralProjection_commutes (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    compactSpectralProjection T hc hp s * T = T * compactSpectralProjection T hc hp s := by
  classical
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [mul_apply_eq_comp, compactSpectralProjection_repr, compactEigenbasis_repr_apply]
  ring

theorem spectralSubspace_invariant (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    ∀ x ∈ SpectralSubspace T hc hp s, T x ∈ SpectralSubspace T hc hp s := by
  rintro x ⟨y, rfl⟩
  exact ⟨T y, congrArg (fun F : H →L[ℝ] H => F y) (compactSpectralProjection_commutes T hc hp s)⟩

/-- The original operator restricted to its actual spectral space. -/
noncomputable def spectralRestriction (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    SpectralSubspace T hc hp s →L[ℝ] SpectralSubspace T hc hp s :=
  T.restrict (spectralSubspace_invariant T hc hp s)

@[simp]
theorem spectralRestriction_coe (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) (x : SpectralSubspace T hc hp s) :
    (spectralRestriction T hc hp s x : H) = T (x : H) := rfl

theorem spectralRestriction_isSymmetric (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    (spectralRestriction T hc hp s).IsSymmetric := by
  intro x y
  change inner ℝ (T (x : H)) (y : H) = inner ℝ (x : H) (T (y : H))
  exact hp.isSymmetric _ _

theorem spectralRestriction_isPositive (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) :
    (spectralRestriction T hc hp s).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨spectralRestriction_isSymmetric T hc hp s, fun x => ?_⟩
  change 0 ≤ inner ℝ (T (x : H)) (x : H)
  exact hp.inner_nonneg_left _

/-- Membership in the projection range forces all excluded coordinates to vanish. -/
theorem spectralSubspace_coefficient_eq_zero (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (x : SpectralSubspace T hc hp s) (i : CompactSpectralIndex T) (hi : i.1 ∉ s) :
    (compactEigenbasis T hc hp.isSymmetric).repr (x : H) i = 0 := by
  classical
  have hx : compactSpectralProjection T hc hp s (x : H) = (x : H) :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap (compactSpectralProjection_isIdempotent T hc hp s))).mp x.property
  have he := congrArg (fun y : H => (compactEigenbasis T hc hp.isSymmetric).repr y i) hx
  simpa only [compactSpectralProjection_repr, if_neg hi, zero_mul] using he.symm

/-- The restriction norm bound comes from a genuinely bounded truncated
spectral multiplier, not from an assumed spectral radius bound. -/
theorem spectralRestriction_norm_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ∈ s, |t| ≤ C) :
    ‖spectralRestriction T hc hp s‖ ≤ C := by
  classical
  let b := compactEigenbasis T hc hp.isSymmetric
  let w : CompactSpectralIndex T → ℝ := fun i => if i.1 ∈ s then i.1 else 0
  have hw : ∀ i, ‖w i‖ ≤ C := by
    intro i
    dsimp only [w]
    split_ifs with hi
    · exact hb i.1 hi
    · simpa only [norm_zero] using hC
  let D := hilbertDiagonal b w C hC hw
  have hD (x : SpectralSubspace T hc hp s) : T (x : H) = D (x : H) := by
    apply b.repr.injective
    ext i
    rw [compactEigenbasis_repr_apply, hilbertDiagonal_repr]
    change i.1 * b.repr (x : H) i = w i * b.repr (x : H) i
    by_cases hi : i.1 ∈ s
    · simp only [w, if_pos hi]
    · have hz : b.repr (x : H) i = 0 := spectralSubspace_coefficient_eq_zero T hc hp s x i hi
      simp only [w, if_neg hi, hz, mul_zero]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  change ‖T (x : H)‖ ≤ C * ‖(x : H)‖
  rw [hD]
  exact D.le_of_opNorm_le (hilbertDiagonal_norm_le b w C hC hw) _

/-- The quadratic form is the actual weighted coefficient sum. -/
theorem compact_quadratic_hasSum (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hp : T.IsPositive) (x : H) :
    HasSum (fun i : CompactSpectralIndex T => i.1 *
      (compactEigenbasis T hc hp.isSymmetric).repr x i ^ 2) (inner ℝ x (T x)) := by
  let b := compactEigenbasis T hc hp.isSymmetric
  change HasSum (fun i : CompactSpectralIndex T => i.1 * b.repr x i ^ 2) (inner ℝ x (T x))
  have ht : (fun i : CompactSpectralIndex T => i.1 * b.repr x i ^ 2) =
      (fun i => inner ℝ x (b i) * inner ℝ (b i) (T x)) := by
    funext i
    calc
      _ = b.repr x i * b.repr (T x) i := by rw [compactEigenbasis_repr_apply]; ring
      _ = _ := by rw [b.repr_apply_apply, b.repr_apply_apply, real_inner_comm (b i) x]
  rw [ht]
  exact b.hasSum_inner_mul_inner x (T x)

/-- Spectral lower bounds give actual quadratic coercivity on the restriction. -/
theorem spectralRestriction_quadratic_lower (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (s : Set ℝ) (a : ℝ)
    (hb : ∀ t ∈ s, a ≤ t) (x : SpectralSubspace T hc hp s) :
    a * ‖x‖ ^ 2 ≤ inner ℝ x (spectralRestriction T hc hp s x) := by
  classical
  let b := compactEigenbasis T hc hp.isSymmetric
  have hleft := (hilbertBasis_coefficients_sq_summable b (x : H)).mul_left a
  have hright := compact_quadratic_hasSum T hc hp (x : H)
  have hi (i : CompactSpectralIndex T) : a * b.repr (x : H) i ^ 2 ≤ i.1 * b.repr (x : H) i ^ 2 := by
    by_cases ht : i.1 ∈ s
    · exact mul_le_mul_of_nonneg_right (hb i.1 ht) (sq_nonneg _)
    · have hz : b.repr (x : H) i = 0 := spectralSubspace_coefficient_eq_zero T hc hp s x i ht
      simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  have hs := Summable.tsum_le_tsum hi hleft hright.summable
  rw [tsum_mul_left, ← hilbertBasis_norm_sq_eq_tsum b, hright.tsum_eq] at hs
  exact hs

abbrev HighSpectralSpace (T : H →L[ℝ] H) (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) :=
  SpectralSubspace T hc hp (Set.Ici (2 * τ))

abbrev LowSpectralSpace (T : H →L[ℝ] H) (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) :=
  SpectralSubspace T hc hp (Set.Icc 0 τ)

noncomputable def highSpectralRestriction (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) :
    HighSpectralSpace T hc hp τ →L[ℝ] HighSpectralSpace T hc hp τ :=
  spectralRestriction T hc hp (Set.Ici (2 * τ))

noncomputable def lowSpectralRestriction (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) :
    LowSpectralSpace T hc hp τ →L[ℝ] LowSpectralSpace T hc hp τ :=
  spectralRestriction T hc hp (Set.Icc 0 τ)

theorem highSpectralRestriction_coercive (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) (x : HighSpectralSpace T hc hp τ) :
    (2 * τ) * ‖x‖ ^ 2 ≤ inner ℝ x (highSpectralRestriction T hc hp τ x) :=
  spectralRestriction_quadratic_lower T hc hp (Set.Ici (2 * τ)) (2 * τ) (fun _ ht => ht) x

theorem lowSpectralRestriction_norm_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖lowSpectralRestriction T hc hp τ‖ ≤ τ :=
  spectralRestriction_norm_le T hc hp (Set.Icc 0 τ) τ hτ
    (fun _ ht => by simpa only [abs_of_nonneg ht.1] using ht.2)

theorem highSpectralRestriction_norm_coercive (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) (x : HighSpectralSpace T hc hp τ) :
    (2 * τ) * ‖x‖ ≤ ‖highSpectralRestriction T hc hp τ x‖ := by
  have hq := highSpectralRestriction_coercive T hc hp τ x
  have hi := real_inner_le_norm x (highSpectralRestriction T hc hp τ x)
  by_cases hx : x = 0
  · simp [hx]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith

/-- Invertibility of the actual high restriction follows from its spectral
coercivity. No inverse or closed-range certificate is assumed. -/
theorem highSpectralRestriction_isUnit (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) (hτ : 0 < τ) :
    IsUnit (highSpectralRestriction T hc hp τ) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (c := ⟨2 * τ, by positivity⟩) _
    (by exact_mod_cast (show (0 : ℝ) < 2 * τ from by positivity))
  intro x
  have hq := highSpectralRestriction_coercive T hc hp τ x
  have ha : inner ℝ x (highSpectralRestriction T hc hp τ x) ≤
      ‖inner ℝ (highSpectralRestriction T hc hp τ x) x‖ := by
    rw [Real.norm_eq_abs]
    exact (real_inner_comm (highSpectralRestriction T hc hp τ x) x).le.trans (le_abs_self _)
  change ‖x‖ ^ 2 * (2 * τ) ≤ ‖inner ℝ (highSpectralRestriction T hc hp τ x) x‖
  nlinarith [hq.trans ha]

/-- The actual high inverse has the exact `1/(2τ)` bound. -/
theorem highSpectralRestriction_inverse_norm_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (τ : ℝ) (hτ : 0 < τ) :
    ‖Ring.inverse (highSpectralRestriction T hc hp τ)‖ ≤ 1 / (2 * τ) := by
  let U := highSpectralRestriction T hc hp τ
  have hu : IsUnit U := highSpectralRestriction_isUnit T hc hp τ hτ
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hx : U (Ring.inverse U x) = x :=
    congrArg (fun F : HighSpectralSpace T hc hp τ →L[ℝ] HighSpectralSpace T hc hp τ => F x)
      (Ring.mul_inverse_cancel U hu)
  have hb := highSpectralRestriction_norm_coercive T hc hp τ (Ring.inverse U x)
  change (2 * τ) * ‖Ring.inverse U x‖ ≤ ‖U (Ring.inverse U x)‖ at hb
  rw [hx] at hb
  change ‖Ring.inverse U x‖ ≤ 1 / (2 * τ) * ‖x‖
  rw [one_div_mul_eq_div]
  exact (le_div_iff₀ (by positivity : 0 < 2 * τ)).mpr (by simpa only [mul_comm] using hb)

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

local instance : NormedSpace ℝ H := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ G := InnerProductSpace.toNormedSpace

local instance blockOperatorsNormedAddCommGroup
    (U : H →L[ℝ] H) (V : G →L[ℝ] G)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedAddCommGroup (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ) :=
  inferInstance

local instance blockOperatorsNormedSpace
    (U : H →L[ℝ] H) (V : G →L[ℝ] G)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) :
    NormedSpace ℝ (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ) :=
  inferInstance

/-- Actual separated spectral restrictions give the rectangular Sylvester
multiplier. The high and low spaces may lie in different Hilbert spaces; no
commutation, finite dimension, or separability is required. -/
theorem separatedSpectralBlocks_multiplier
    (U : H →L[ℝ] H) (V : G →L[ℝ] G)
    (hcU : IsCompactOperator U) (hcV : IsCompactOperator V)
    (hpU : U.IsPositive) (hpV : V.IsPositive) (τ : ℝ) (hτ : 0 < τ) :
    ∃ S : (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ) →L[ℝ]
        (LowSpectralSpace V hcV hpV τ →L[ℝ] HighSpectralSpace U hcU hpU τ),
      ‖S‖ ≤ τ⁻¹ ∧ ∀ C,
        (highSpectralRestriction U hcU hpU τ).comp (S C) -
          (S C).comp (lowSpectralRestriction V hcV hpV τ) = C :=
  rectangularSylvester_multiplier_of_gap (highSpectralRestriction U hcU hpU τ)
    (lowSpectralRestriction V hcV hpV τ)
    (highSpectralRestriction_isUnit U hcU hpU τ hτ) hτ
    (highSpectralRestriction_inverse_norm_le U hcU hpU τ hτ)
    (lowSpectralRestriction_norm_le V hcV hpV τ hτ.le)

end
end KernelSeq
