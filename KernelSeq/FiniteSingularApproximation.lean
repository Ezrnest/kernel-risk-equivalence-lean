import KernelSeq.FiniteSingularOrder
import KernelSeq.FiniteSpectralCompression
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Actual finite singular truncations and rank approximation

Uses Mathlib's actual sorted singular values of the actual linear map. No
min--max, best-rank approximation or product singular-value inequality is an
input certificate. Actual sorted truncations attain the best rank error;
rank approximation of products then proves the product singular-value bound.
The project Schatten powers are identified with the actual zero-extended
singular-value series. Empty spaces and rank-deficient maps remain included.
-/

open scoped BigOperators
open Module Submodule

namespace KernelSeq

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/-- The actual sorted right singular basis, constructed from `A* A`. -/
def finiteRightSingularBasis (A : H →L[ℝ] H) :
    OrthonormalBasis (Fin (Module.finrank ℝ H)) ℝ H :=
  A.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

omit [CompleteSpace H] in
/-- Genuine finite singular-coordinate Parseval energy for every vector. -/
theorem finiteRightSingularBasis_energy (A : H →L[ℝ] H) (x : H) :
    ‖A x‖ ^ 2 = ∑ i : Fin (Module.finrank ℝ H),
      A.toLinearMap.singularValues i ^ 2 * (finiteRightSingularBasis A).repr x i ^ 2 := by
  let e := finiteRightSingularBasis A
  let T := A.toLinearMap.adjoint.comp A.toLinearMap
  have hnorm : ‖A x‖ ^ 2 = inner ℝ x (T x) := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    rfl
  rw [hnorm, ← e.sum_inner_mul_inner x (T x)]
  apply Finset.sum_congr rfl
  intro i _
  have hleft : inner ℝ x (e i) = e.repr x i := by
    rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
  have hcoef : e.repr (T x) i =
      A.toLinearMap.isSymmetric_adjoint_comp_self.eigenvalues rfl i * e.repr x i :=
    A.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis_apply_self_apply rfl x i
  have hright : inner ℝ (e i) (T x) =
      A.toLinearMap.singularValues i ^ 2 * e.repr x i := by
    rw [← OrthonormalBasis.repr_apply_apply, hcoef, A.toLinearMap.sq_singularValues_fin rfl i]
  rw [hleft, hright]
  ring

/-- The first `k` actual sorted right singular coordinates. -/
def finiteSingularPrefix (k : ℕ) : Finset (Fin (Module.finrank ℝ H)) :=
  Finset.univ.filter (fun i => i.val < k)

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
@[simp]
theorem mem_finiteSingularPrefix (k : ℕ) (i : Fin (Module.finrank ℝ H)) :
    i ∈ finiteSingularPrefix (H := H) k ↔ i.val < k := by
  simp [finiteSingularPrefix]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- The prefix has at most `k` genuine basis indices. -/
theorem finiteSingularPrefix_card_le (k : ℕ) :
    (finiteSingularPrefix (H := H) k).card ≤ k := by
  let s := finiteSingularPrefix (H := H) k
  let f : s → Fin k := fun i => ⟨i.val.val, (mem_finiteSingularPrefix k i.val).mp i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin k => z.val) hij
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using h

/-- The actual sorted singular truncation, an actual bounded operator. -/
def finiteSingularTruncation (A : H →L[ℝ] H) (k : ℕ) : H →L[ℝ] H :=
  A * finiteBasisProjection (finiteRightSingularBasis A).toHilbertBasis (finiteSingularPrefix k)

/-- The genuine truncation remainder keeps exactly the tail coordinates. -/
theorem finiteSingularTruncation_remainder_repr (A : H →L[ℝ] H) (k : ℕ) (x : H)
    (i : Fin (Module.finrank ℝ H)) :
    (finiteRightSingularBasis A).toHilbertBasis.repr
      (x - finiteBasisProjection (finiteRightSingularBasis A).toHilbertBasis (finiteSingularPrefix k) x) i =
        if i.val < k then 0 else (finiteRightSingularBasis A).toHilbertBasis.repr x i := by
  rw [map_sub, lp.coeFn_sub, Pi.sub_apply, finiteBasisProjection_repr]
  by_cases h : i.val < k <;> simp only [mem_finiteSingularPrefix, h, if_true, if_false, sub_self, sub_zero]

/-- The actual best-singular truncation upper bound, proved directly from the
actual singular-coordinate energy and sorted singular values. -/
theorem finiteSingularTruncation_error_le (A : H →L[ℝ] H) (k : ℕ) :
    ‖A - finiteSingularTruncation A k‖ ≤ A.toLinearMap.singularValues k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (A.toLinearMap.singularValues_nonneg k)
  intro x
  let e := (finiteRightSingularBasis A).toHilbertBasis
  let y := x - finiteBasisProjection e (finiteSingularPrefix k) x
  have hvec : (A - finiteSingularTruncation A k) x = A y := by
    simp only [sub_apply, finiteSingularTruncation, mul_apply_eq_comp, y, map_sub, e]
  rw [hvec]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (A.toLinearMap.singularValues_nonneg k) (norm_nonneg x))).mp
  rw [mul_pow, finiteRightSingularBasis_energy]
  have hx : ‖x‖ ^ 2 = ∑ i : Fin (Module.finrank ℝ H), e.repr x i ^ 2 := by
    simpa only [tsum_fintype] using hilbertBasis_norm_sq_eq_tsum e x
  rw [hx, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hrepr : (finiteRightSingularBasis A).repr y i = if i.val < k then 0 else e.repr x i := by
    simpa only [e, y, HilbertBasis.repr_apply_apply, OrthonormalBasis.coe_toHilbertBasis,
      ← OrthonormalBasis.repr_apply_apply] using finiteSingularTruncation_remainder_repr A k x i
  rw [hrepr]
  by_cases hi : i.val < k
  · simp only [hi, if_true, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    positivity
  · rw [if_neg hi]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (A.toLinearMap.singularValues_nonneg i)
      (A.toLinearMap.singularValues_antitone (Nat.le_of_not_gt hi)) 2

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- The actual coordinate projection has rank at most the number of
selected coordinates. No rank certificate is an input. -/
theorem finiteBasisProjection_finrank_range_le_card {I : Type*}
    (b : HilbertBasis I ℝ H) (s : Finset I) :
    Module.finrank ℝ (finiteBasisProjection b s).range ≤ s.card := by
  classical
  have h := Submodule.finrank_mono (finiteBasisProjection_range_le b s)
  have hset : b '' (s : Set I) = ((s.image b : Finset H) : Set H) := by simp only [Finset.coe_image]
  rw [hset] at h
  exact h.trans ((finrank_span_finset_le_card (R := ℝ) (s.image b)).trans Finset.card_image_le)

/-- The actual sorted singular truncation has actual range dimension at most
`k`, even when `k` exceeds the ambient dimension. -/
theorem finiteSingularTruncation_rank_le (A : H →L[ℝ] H) (k : ℕ) :
    Module.finrank ℝ (finiteSingularTruncation A k).range ≤ k := by
  let e := (finiteRightSingularBasis A).toHilbertBasis
  let P := finiteBasisProjection e (finiteSingularPrefix (H := H) k)
  have hrange : (finiteSingularTruncation A k).range = P.range.map A.toLinearMap := by
    exact LinearMap.range_comp P.toLinearMap A.toLinearMap
  rw [hrange]
  exact (Submodule.finrank_map_le A.toLinearMap P.range).trans
    ((finiteBasisProjection_finrank_range_le_card e _).trans (finiteSingularPrefix_card_le k))

/-- Genuine best-rank lower bound. The nonzero vector in the top `k+1`
singular directions killed by `F` is derived from rank-nullity, not assumed. -/
theorem finiteSingularValue_le_rank_approximation (A F : H →L[ℝ] H) (k : ℕ)
    (hF : Module.finrank ℝ F.range ≤ k) :
    A.toLinearMap.singularValues k ≤ ‖A - F‖ := by
  classical
  by_cases hk : Module.finrank ℝ H ≤ k
  · rw [A.toLinearMap.singularValues_of_finrank_le hk]
    exact norm_nonneg _
  have hkn : k + 1 ≤ Module.finrank ℝ H := by omega
  let e := finiteRightSingularBasis A
  let f : Fin (k + 1) → Fin (Module.finrank ℝ H) := Fin.castLE hkn
  let v : Fin (k + 1) → H := fun i => e (f i)
  let W := Submodule.span ℝ (Set.range v)
  have hli : LinearIndependent ℝ v := e.orthonormal.linearIndependent.comp f (Fin.castLE_injective hkn)
  have hdim : Module.finrank ℝ W = k + 1 := by
    simpa only [W, Fintype.card_fin] using finrank_span_eq_card hli
  have hsupport (x : H) (hx : x ∈ W) : ∀ i : Fin (Module.finrank ℝ H), k < i.val → inner ℝ (e i) x = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i hi
      have hne : i ≠ f j := by
        intro h
        have hh := congrArg Fin.val h
        change i.val = j.val at hh
        omega
      exact e.orthonormal.inner_eq_zero hne
    | zero => intro i _; simp
    | add x y _ _ hx hy =>
      intro i hi
      rw [inner_add_right, hx i hi, hy i hi, add_zero]
    | smul a x _ hx =>
      intro i hi
      rw [inner_smul_right, hx i hi, mul_zero]
  have hlower (x : H) (hx : x ∈ W) : A.toLinearMap.singularValues k * ‖x‖ ≤ ‖A x‖ := by
    apply (sq_le_sq₀ (mul_nonneg (A.toLinearMap.singularValues_nonneg k) (norm_nonneg x)) (norm_nonneg _)).mp
    rw [mul_pow, finiteRightSingularBasis_energy]
    have hxnorm : ‖x‖ ^ 2 = ∑ i : Fin (Module.finrank ℝ H), e.repr x i ^ 2 := by
      simpa only [tsum_fintype, HilbertBasis.repr_apply_apply, OrthonormalBasis.coe_toHilbertBasis,
        ← OrthonormalBasis.repr_apply_apply] using hilbertBasis_norm_sq_eq_tsum e.toHilbertBasis x
    rw [hxnorm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i.val ≤ k
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (A.toLinearMap.singularValues_nonneg k)
        (A.toLinearMap.singularValues_antitone hi) 2
    · have hz : e.repr x i = 0 := by
        rw [OrthonormalBasis.repr_apply_apply]
        exact hsupport x hx i (Nat.lt_of_not_ge hi)
      change _ ≤ A.toLinearMap.singularValues i ^ 2 * e.repr x i ^ 2
      rw [hz]
      simp
  let G := F.toLinearMap.rangeRestrict.domRestrict W
  have hker : G.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by rw [hdim]; omega)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hzF : F (z : H) = 0 := congrArg (fun w : F.range => (w : H)) (LinearMap.mem_ker.mp hz)
  have hzn : 0 < ‖(z : H)‖ := norm_pos_iff.mpr (fun h => hz0 (Subtype.ext h))
  have hu : ‖A (z : H)‖ ≤ ‖A - F‖ * ‖(z : H)‖ := by
    simpa only [sub_apply, hzF, sub_zero] using (A - F).le_opNorm (z : H)
  exact (mul_le_mul_iff_of_pos_right hzn).mp ((hlower (z : H) z.property).trans hu)

/-- The actual sorted singular truncation attains the true best-rank error. -/
theorem finiteSingularTruncation_error_eq (A : H →L[ℝ] H) (k : ℕ) :
    ‖A - finiteSingularTruncation A k‖ = A.toLinearMap.singularValues k :=
  le_antisymm (finiteSingularTruncation_error_le A k)
    (finiteSingularValue_le_rank_approximation A _ k (finiteSingularTruncation_rank_le A k))

omit [CompleteSpace H] in
/-- Actual rank subadditivity for finite operator ranges. -/
theorem finiteOperator_rank_add_le (A B : H →L[ℝ] H) :
    Module.finrank ℝ (A + B).range ≤ Module.finrank ℝ A.range + Module.finrank ℝ B.range :=
  (Submodule.finrank_mono (LinearMap.range_add_le A.toLinearMap B.toLinearMap)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

omit [CompleteSpace H] in
/-- Actual product rank is bounded by the rank of its left factor. -/
theorem finiteOperator_rank_mul_le_left (A B : H →L[ℝ] H) :
    Module.finrank ℝ (A * B).range ≤ Module.finrank ℝ A.range := by
  apply Submodule.finrank_mono
  rintro _ ⟨x, rfl⟩
  exact ⟨B x, rfl⟩

omit [CompleteSpace H] in
/-- Actual product rank is bounded by the rank of its right factor. -/
theorem finiteOperator_rank_mul_le_right (A B : H →L[ℝ] H) :
    Module.finrank ℝ (A * B).range ≤ Module.finrank ℝ B.range := by
  have hr : (A * B).range = B.range.map A.toLinearMap := LinearMap.range_comp B.toLinearMap A.toLinearMap
  rw [hr]
  exact Submodule.finrank_map_le A.toLinearMap B.range

/-- Genuine product singular-value Weyl bound, proved by an actual rank
approximation assembled from the two actual singular truncations. -/
theorem finiteSingularValue_mul_le (A B : H →L[ℝ] H) (k j : ℕ) :
    (A * B).toLinearMap.singularValues (k + j) ≤
      A.toLinearMap.singularValues k * B.toLinearMap.singularValues j := by
  let Ak := finiteSingularTruncation A k
  let Bj := finiteSingularTruncation B j
  let F := Ak * B + (A - Ak) * Bj
  have hF : Module.finrank ℝ F.range ≤ k + j :=
    (finiteOperator_rank_add_le _ _).trans (add_le_add
      ((finiteOperator_rank_mul_le_left Ak B).trans (finiteSingularTruncation_rank_le A k))
      ((finiteOperator_rank_mul_le_right (A - Ak) Bj).trans (finiteSingularTruncation_rank_le B j)))
  have heq : A * B - F = (A - Ak) * (B - Bj) := by
    dsimp only [F]
    noncomm_ring
  calc
    _ ≤ ‖A * B - F‖ := finiteSingularValue_le_rank_approximation (A * B) F (k + j) hF
    _ = ‖(A - Ak) * (B - Bj)‖ := congrArg norm heq
    _ ≤ ‖A - Ak‖ * ‖B - Bj‖ := norm_mul_le _ _
    _ ≤ _ := mul_le_mul (finiteSingularTruncation_error_le A k) (finiteSingularTruncation_error_le B j)
      (norm_nonneg _) (A.toLinearMap.singularValues_nonneg k)

/-- The actual right singular basis is also the eigenbasis of the actual
bounded-operator covariance, with exactly the squared actual singular values. -/
theorem finiteRightSingularBasis_covariance_eigen (A : H →L[ℝ] H)
    (i : Fin (Module.finrank ℝ H)) :
    (A.adjoint * A) (finiteRightSingularBasis A i) =
      A.toLinearMap.singularValues i ^ 2 • finiteRightSingularBasis A i := by
  have h := A.toLinearMap.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis
    (rfl : Module.finrank ℝ H = Module.finrank ℝ H) i
  rw [← A.toLinearMap.sq_singularValues_fin rfl i] at h
  have hA : LinearMap.toContinuousLinearMap A.toLinearMap = A :=
    LinearMap.toContinuousLinearMap.apply_symm_apply A
  simpa only [finiteRightSingularBasis, RCLike.ofReal_real_eq_id, id_eq,
    LinearMap.comp_apply, LinearMap.adjoint_eq_toCLM_adjoint, LinearMap.coe_toContinuousLinearMap,
    ContinuousLinearMap.coe_coe, hA, mul_apply_eq_comp] using h

section Schatten

variable {ι : Type*} [Fintype ι]

/-- The project actual Schatten power equals the genuine sorted finite
singular-value power sum. This connects the rank-approximation theorem to the
existing Schatten definitions, rather than postulating a singular-value list. -/
theorem finiteSchatten_rpow_eq_sum_singularValues (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b A) p ^ p =
      ∑ i : Fin (Module.finrank ℝ H), A.toLinearMap.singularValues i ^ p := by
  let C := A.adjoint * A
  have hC : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hcov : hsSingularCovariance b (finiteOperatorColumns b A) = C := by
    simp only [hsSingularCovariance, hilbertSchmidtOperator_finiteOperatorColumns, C,
      ContinuousLinearMap.mul_def]
  let e := (finiteRightSingularBasis A).toHilbertBasis
  calc
    _ = compactPositivePowerSum C (p / 2) := by
      have h := hsSchattenNorm_rpow b (finiteOperatorColumns b A) hp
      change _ = compactPositivePowerSum (hsSingularCovariance b (finiteOperatorColumns b A)) (p / 2) at h
      rw [hcov] at h
      exact h
    _ = basisTrace e (finitePositivePower C hC (p / 2) (by positivity)) :=
      (finitePositivePower_trace e C hC _ (by positivity)).symm
    _ = _ := by
      simp only [basisTrace, tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _
      have he : C (e i) = A.toLinearMap.singularValues i ^ 2 • e i := by
        simpa only [C, e, OrthonormalBasis.coe_toHilbertBasis] using finiteRightSingularBasis_covariance_eigen A i
      rw [finitePositivePower_eigen C hC _ _ he]
      simp only [inner_smul_right, real_inner_self_eq_norm_sq, e.orthonormal.norm_eq_one, one_pow, mul_one]
      calc
        (A.toLinearMap.singularValues i ^ 2) ^ (p / 2) =
            A.toLinearMap.singularValues i ^ ((2 : ℝ) * (p / 2)) := by
          rw [Real.rpow_mul (A.toLinearMap.singularValues_nonneg i), Real.rpow_two]
        _ = _ := by congr 1; ring

omit [CompleteSpace H] in
/-- Actual finite singular power series are summable; their zero tail is
proved from Mathlib's actual dimension cutoff. -/
theorem finiteSingularPower_summable (A : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    Summable (fun n : ℕ => A.toLinearMap.singularValues n ^ p) := by
  apply summable_of_ne_finset_zero (s := Finset.range (Module.finrank ℝ H))
  intro n hn
  rw [A.toLinearMap.singularValues_of_finrank_le (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)),
    Real.zero_rpow hp.ne']

/-- The actual project Schatten power also equals the zero-extended natural
singular-value series, ready for index splitting and scalar Hölder estimates. -/
theorem finiteSchatten_rpow_eq_tsum_singularValues (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) {p : ℝ} (hp : 0 < p) :
    hsSchattenNorm b (finiteOperatorColumns b A) p ^ p =
      ∑' n : ℕ, A.toLinearMap.singularValues n ^ p := by
  rw [finiteSchatten_rpow_eq_sum_singularValues b A hp,
    Fin.sum_univ_eq_sum_range (fun n : ℕ => A.toLinearMap.singularValues n ^ p) (Module.finrank ℝ H)]
  symm
  apply tsum_eq_sum
  intro n hn
  rw [A.toLinearMap.singularValues_of_finrank_le (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)),
    Real.zero_rpow hp.ne']

end Schatten
end
end KernelSeq
