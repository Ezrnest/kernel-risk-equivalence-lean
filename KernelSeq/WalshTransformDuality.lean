import KernelSeq.FiniteFieldDuality
import KernelSeq.WalshWeakType

/-!
# Actual prefix Walsh transform duality and L2 contraction

The prefix averages are genuine finite conditional projections. Their
tower identity constructs the linear sign transform, its square and its
trace selfadjointness. The initial prefix-one component is retained, as in
`walshPrefixTransform`; no transform certificate is assumed.
-/

open scoped BigOperators

namespace KernelSeq
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The actual finite prefix average as a linear field projection. -/
def walshPrefixLinearMap {V : Type*} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) : (WalshCube n → V) →ₗ[ℝ] (WalshCube n → V) where
  toFun := walshPrefixAverage k
  map_add' F G := funext fun ω => walshPrefixAverage_add k F G ω
  map_smul' a F := by
    funext ω
    simp only [walshPrefixAverage, Pi.smul_apply, ← Finset.smul_sum]
    exact smul_comm _ _ _

@[simp]
theorem walshPrefixLinearMap_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (F : WalshCube n → V) : walshPrefixLinearMap k F = walshPrefixAverage k F := rfl

/-- Actual conditional projections compose at their minimum prefix. -/
theorem walshPrefixLinearMap_mul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (j k : ℕ) :
    walshPrefixLinearMap (n := n) (V := V) j * walshPrefixLinearMap k =
      walshPrefixLinearMap (min j k) := by
  apply LinearMap.ext
  intro F
  funext ω
  change walshPrefixAverage j (walshPrefixAverage k F) ω = walshPrefixAverage (min j k) F ω
  by_cases hjk : j ≤ k
  · rw [min_eq_left hjk]
    exact walshPrefixAverage_tower hjk F ω
  · have hkj : k ≤ j := le_of_not_ge hjk
    rw [min_eq_right hkj]
    exact walshPrefixAverage_of_adapted ((walshPrefixAverage_adapted k F).mono hkj) ω

/-- A real linear field map equal to the actual prefix sign transform. -/
def walshPrefixTransformLinearMap {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : ℕ → ℝ) (N : ℕ) : (WalshCube n → V) →ₗ[ℝ] (WalshCube n → V) :=
  walshPrefixLinearMap 1 + ∑ k ∈ Finset.range N,
    σ k • (walshPrefixLinearMap (k + 2) - walshPrefixLinearMap (k + 1))

theorem walshPrefixTransformLinearMap_succ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : ℕ → ℝ) (N : ℕ) :
    walshPrefixTransformLinearMap (n := n) (V := V) σ (N + 1) =
      walshPrefixTransformLinearMap σ N +
        σ N • (walshPrefixLinearMap (N + 2) - walshPrefixLinearMap (N + 1)) := by
  simp only [walshPrefixTransformLinearMap, Finset.sum_range_succ]
  abel

theorem walshPrefixTransformLinearMap_mul_prefix {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : ℕ → ℝ) (N k : ℕ) (hk : N + 1 ≤ k) :
    walshPrefixTransformLinearMap (n := n) (V := V) σ N * walshPrefixLinearMap k =
      walshPrefixTransformLinearMap σ N := by
  unfold walshPrefixTransformLinearMap
  rw [add_mul, Finset.sum_mul]
  have h1 : min 1 k = 1 := min_eq_left (by omega)
  rw [walshPrefixLinearMap_mul, h1]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjN := Finset.mem_range.mp hj
  rw [smul_mul_assoc, sub_mul, walshPrefixLinearMap_mul, walshPrefixLinearMap_mul,
    min_eq_left (by omega : j + 2 ≤ k), min_eq_left (by omega : j + 1 ≤ k)]

theorem walshPrefixLinearMap_mul_transform {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : ℕ → ℝ) (N k : ℕ) (hk : N + 1 ≤ k) :
    walshPrefixLinearMap (n := n) (V := V) k * walshPrefixTransformLinearMap σ N =
      walshPrefixTransformLinearMap σ N := by
  unfold walshPrefixTransformLinearMap
  rw [mul_add, Finset.mul_sum]
  have h1 : min k 1 = 1 := min_eq_right (by omega)
  rw [walshPrefixLinearMap_mul, h1]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjN := Finset.mem_range.mp hj
  rw [mul_smul_comm, mul_sub, walshPrefixLinearMap_mul, walshPrefixLinearMap_mul,
    min_eq_right (by omega : j + 2 ≤ k), min_eq_right (by omega : j + 1 ≤ k)]

/-- Actual orthogonal prefix differences give the exact transform square. -/
theorem walshPrefixTransformLinearMap_square {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) :
    walshPrefixTransformLinearMap (n := n) (V := V) σ N * walshPrefixTransformLinearMap σ N =
      walshPrefixLinearMap (N + 1) := by
  induction N with
  | zero => simp [walshPrefixTransformLinearMap, walshPrefixLinearMap_mul]
  | succ N ih =>
    let T := walshPrefixTransformLinearMap (n := n) (V := V) σ N
    let P := walshPrefixLinearMap (n := n) (V := V) (N + 1)
    let Q := walshPrefixLinearMap (n := n) (V := V) (N + 2)
    have hTT : T * T = P := ih
    have hTP : T * P = T := walshPrefixTransformLinearMap_mul_prefix σ N _ le_rfl
    have hTQ : T * Q = T := walshPrefixTransformLinearMap_mul_prefix σ N _ (by omega)
    have hPT : P * T = T := walshPrefixLinearMap_mul_transform σ N _ le_rfl
    have hQT : Q * T = T := walshPrefixLinearMap_mul_transform σ N _ (by omega)
    have hPP : P * P = P := by simp [P, walshPrefixLinearMap_mul]
    have hQQ : Q * Q = Q := by simp [Q, walshPrefixLinearMap_mul]
    have hPQ : P * Q = P := by simp [P, Q, walshPrefixLinearMap_mul]
    have hQP : Q * P = P := by simp [P, Q, walshPrefixLinearMap_mul]
    have hs : σ N * σ N = 1 := by nlinarith [sq_abs (σ N), hσ N]
    rw [walshPrefixTransformLinearMap_succ]
    change (T + σ N • (Q - P)) * (T + σ N • (Q - P)) = Q
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      sub_mul, mul_sub, hTT, hTP, hTQ, hPT, hQT, hPP, hQQ, hPQ, hQP]
    simp only [sub_self, smul_zero, add_zero, add_sub_cancel_left, smul_smul, hs, one_smul]
    abel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- The bundled map is the existing actual transform, with its original
initial-prefix and difference indexing. -/
theorem walshPrefixTransformLinearMap_apply (F : WalshCube n → H →L[ℝ] H)
    (σ : ℕ → ℝ) (N : ℕ) :
    walshPrefixTransformLinearMap σ N F = fun ω => walshPrefixTransform F σ N ω := by
  ext ω x
  simp only [walshPrefixTransformLinearMap, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, walshPrefixLinearMap_apply,
    walshPrefixTransform, finiteWalshTransform, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Finset.sum_apply, add_apply]

variable {ι : Type*} [Fintype ι]

private def walshTracePairingLinear (b : HilbertBasis ι ℝ H)
    (G : WalshCube n → H →L[ℝ] H) : (WalshCube n → H →L[ℝ] H) →ₗ[ℝ] ℝ where
  toFun F := finiteFieldTracePairing b F G
  map_add' F K := by
    simp only [finiteFieldTracePairing, Pi.add_apply, finiteOperatorColumns_trace_inner,
      finiteOperatorColumns_add, inner_add_left, Finset.sum_add_distrib, mul_add]
  map_smul' a F := finiteFieldTracePairing_smul_left b a F G

omit [FiniteDimensional ℝ H] in
/-- Adjoint commutes with the actual finite conditional prefix average. -/
theorem walshPrefixAverage_adjoint (F : WalshCube n → H →L[ℝ] H) (k : ℕ) (ω : WalshCube n) :
    (walshPrefixAverage k F ω).adjoint = walshPrefixAverage k (fun η => (F η).adjoint) ω := by
  exact (walshPrefixAverage_map k F ContinuousLinearMap.adjoint.toLinearEquiv.toLinearMap ω).symm

omit [FiniteDimensional ℝ H] in
/-- The actual adapted trace pullout, for the adjoint trace pairing. -/
theorem finiteFieldTracePairing_prefix_adapted (b : HilbertBasis ι ℝ H)
    (F G : WalshCube n → H →L[ℝ] H) (k : ℕ) (hG : WalshAdapted k G) :
    finiteFieldTracePairing b (walshPrefixAverage k F) G = finiteFieldTracePairing b F G := by
  unfold finiteFieldTracePairing
  simp_rw [walshPrefixAverage_adjoint]
  rw [sum_trace_walshPrefixAverage_mul b (fun ω => (F ω).adjoint) G hG]

omit [FiniteDimensional ℝ H] in
/-- Each actual prefix projection is selfadjoint for the actual averaged
trace pairing, on arbitrary (not necessarily selfadjoint) fields. -/
theorem walshPrefixLinearMap_trace_selfadjoint (b : HilbertBasis ι ℝ H)
    (F G : WalshCube n → H →L[ℝ] H) (k : ℕ) :
    finiteFieldTracePairing b (walshPrefixLinearMap k F) G =
      finiteFieldTracePairing b F (walshPrefixLinearMap k G) := by
  have hF := walshPrefixAverage_adapted k F
  have hG := walshPrefixAverage_adapted k G
  have h1 := finiteFieldTracePairing_prefix_adapted b F (walshPrefixAverage k G) k hG
  have h2 := finiteFieldTracePairing_prefix_adapted b G (walshPrefixAverage k F) k hF
  rw [finiteFieldTracePairing_comm b (walshPrefixAverage k G) (walshPrefixAverage k F),
    finiteFieldTracePairing_comm b G (walshPrefixAverage k F)] at h2
  exact h2.symm.trans h1

omit [FiniteDimensional ℝ H] in
private theorem walshTransform_trace_expand (b : HilbertBasis ι ℝ H)
    (F G : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (N : ℕ) :
    finiteFieldTracePairing b (walshPrefixTransformLinearMap σ N F) G =
      finiteFieldTracePairing b (walshPrefixLinearMap 1 F) G + ∑ k ∈ Finset.range N,
        σ k * (finiteFieldTracePairing b (walshPrefixLinearMap (k + 2) F) G -
          finiteFieldTracePairing b (walshPrefixLinearMap (k + 1) F) G) := by
  change walshTracePairingLinear b G (walshPrefixTransformLinearMap σ N F) = _
  simp only [walshPrefixTransformLinearMap, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, map_add, map_sum, map_smul, map_sub, smul_eq_mul]
  rfl

omit [FiniteDimensional ℝ H] in
/-- The actual prefix sign transform is trace-selfadjoint; its signs need
not have modulus one for this identity. -/
theorem walshPrefixTransformLinearMap_trace_selfadjoint (b : HilbertBasis ι ℝ H)
    (F G : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (N : ℕ) :
    finiteFieldTracePairing b (walshPrefixTransformLinearMap σ N F) G =
      finiteFieldTracePairing b F (walshPrefixTransformLinearMap σ N G) := by
  rw [finiteFieldTracePairing_comm b F (walshPrefixTransformLinearMap σ N G),
    walshTransform_trace_expand, walshTransform_trace_expand]
  have he (k) : finiteFieldTracePairing b (walshPrefixLinearMap k F) G =
      finiteFieldTracePairing b (walshPrefixLinearMap k G) F :=
    (walshPrefixLinearMap_trace_selfadjoint b F G k).trans (finiteFieldTracePairing_comm b F _)
  simp_rw [he]

omit [FiniteDimensional ℝ H] in
/-- The genuine diagonal trace pairing is exactly the field M2 moment. -/
theorem finiteFieldTracePairing_self_eq_moment_two (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) :
    finiteFieldTracePairing b F F = finiteFieldSchattenMoment b F 2 := by
  simp only [finiteFieldTracePairing, finiteFieldSchattenMoment, finiteOperatorColumns_trace_inner,
    real_inner_self_eq_norm_sq, hsSchattenNorm_two, Real.rpow_two]

/-- Actual prefix averaging contracts the normalized M2 moment. -/
theorem walshPrefixLinearMap_moment_two_le (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (k : ℕ) :
    finiteFieldSchattenMoment b (walshPrefixLinearMap k F) 2 ≤ finiteFieldSchattenMoment b F 2 := by
  let G := walshPrefixLinearMap k F
  have hcross : finiteFieldTracePairing b G G = finiteFieldTracePairing b F G :=
    finiteFieldTracePairing_prefix_adapted b F G k (walshPrefixAverage_adapted k F)
  have hh := finiteFieldTracePairing_holder b F G Real.HolderConjugate.two_two (le_refl (2 : ℝ))
  rw [← hcross, finiteFieldTracePairing_self_eq_moment_two,
    abs_of_nonneg (finiteFieldSchattenMoment_nonneg b G 2)] at hh
  have hGpow := finiteFieldSchattenNorm_rpow b G (by norm_num : 0 < (2 : ℝ))
  have hFpow := finiteFieldSchattenNorm_rpow b F (by norm_num : 0 < (2 : ℝ))
  simp only [Real.rpow_two] at hGpow hFpow
  have hGn := finiteFieldSchattenNorm_nonneg b G 2
  have hFn := finiteFieldSchattenNorm_nonneg b F 2
  have hnorm : finiteFieldSchattenNorm b G 2 ≤ finiteFieldSchattenNorm b F 2 := by
    by_contra h
    have hlt := lt_of_not_ge h
    have hgpos : 0 < finiteFieldSchattenNorm b G 2 := hFn.trans_lt hlt
    nlinarith [mul_pos hgpos (sub_pos.mpr hlt)]
  nlinarith [sq_nonneg (finiteFieldSchattenNorm b F 2 - finiteFieldSchattenNorm b G 2)]

/-- The actual deterministic-sign transform contracts normalized M2.
This is derived from the exact square and true conditional projections. -/
theorem walshPrefixTransformLinearMap_moment_two_le (b : HilbertBasis ι ℝ H)
    (F : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) :
    finiteFieldSchattenMoment b (walshPrefixTransformLinearMap σ N F) 2 ≤
      finiteFieldSchattenMoment b F 2 := by
  have hsq : walshPrefixTransformLinearMap σ N (walshPrefixTransformLinearMap σ N F) =
      walshPrefixLinearMap (N + 1) F :=
    congrArg (fun L : (WalshCube n → H →L[ℝ] H) →ₗ[ℝ] (WalshCube n → H →L[ℝ] H) => L F)
      (walshPrefixTransformLinearMap_square σ hσ N)
  have hcross := finiteFieldTracePairing_prefix_adapted b F
    (walshPrefixLinearMap (N + 1) F) (N + 1) (walshPrefixAverage_adapted _ F)
  calc
    _ = finiteFieldTracePairing b (walshPrefixTransformLinearMap σ N F)
        (walshPrefixTransformLinearMap σ N F) := (finiteFieldTracePairing_self_eq_moment_two b _).symm
    _ = finiteFieldTracePairing b F (walshPrefixLinearMap (N + 1) F) := by
      rw [walshPrefixTransformLinearMap_trace_selfadjoint, hsq]
    _ = finiteFieldSchattenMoment b (walshPrefixLinearMap (N + 1) F) 2 := by
      rw [← hcross]
      exact finiteFieldTracePairing_self_eq_moment_two b _
    _ ≤ _ := walshPrefixLinearMap_moment_two_le b F (N + 1)

end
end KernelSeq
