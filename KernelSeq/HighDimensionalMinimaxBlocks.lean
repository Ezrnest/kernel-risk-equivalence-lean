import KernelSeq.HighDimensionalMinimaxEigenBlocks
import KernelSeq.HighDimensionalMinimaxPrior

/-!
# Finite one-block and two-block lower bounds in the actual spherical model

The Gaussian variances allocate the prescribed source energy uniformly within
each actual degree block. The corresponding sequence Bayes loss is the
parallel sum of the block signal budget and its noise variance.
-/

namespace KernelSeq
open MeasureTheory Filter Set
open scoped BigOperators
noncomputable section

def highDimensionalBlockBayesRisk (A B : ℝ) : ℝ := A*B/(A+B)

private theorem block_source_weight_eq {t : ℝ} (ht : 0 < t) (s M budget : ℝ) :
    t^(-s)*(budget*t^s/M) = budget/M := by
  calc
    _ = budget*(t^(-s)*t^s)/M := by ring
    _ = _ := by rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, mul_one]

private theorem block_bayes_risk_eq {M A σ : ℝ} (hM : 0 < M) (hA : 0 < A) (hσ : 0 < σ)
    {n : ℕ} (hn : 0 < n) :
    M * (((A/M)⁻¹ + (n : ℝ)*(σ^2)⁻¹)⁻¹) =
      highDimensionalBlockBayesRisk A (M*σ^2/n) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hB : 0 < M*σ^2/(n : ℝ) := by positivity
  have hs : 0 < (A/M)⁻¹ + (n : ℝ)*(σ^2)⁻¹ := by positivity
  unfold highDimensionalBlockBayesRisk
  field_simp [hM.ne', hA.ne', hσ.ne', hnR.ne', hs.ne', (add_pos hA hB).ne']
  ring

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
  [RKHS ℝ H (KernelSphere (EuclideanSpace ℝ ι)) ℝ]
  (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
  (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
    rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
  (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
  (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
  {κ s R σ ε B : ℝ} (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
  (hs : 0 ≤ s) (hR : 0 < R) (hσ : 0 < σ) (hε : 0 < ε) (hε1 : ε < 1)
  (hB : 0 < B) (hBsmall : B ≤ 1/4) (n : ℕ) (hn : 0 < n)

include hkernel hκ hdiag in
omit [DecidableEq ι] [Nonempty ι] [SecondCountableTopology H] in
private theorem spherical_minimax_feature_bound :
    ∀ᵐ x ∂uniformSphere (E := EuclideanSpace ℝ ι), ‖rkhsFeature (H := H) x‖ ≤ κ := by
  apply Eventually.of_forall
  apply rkhsFeature_norm_le κ hκ
  intro x
  rw [hkernel, zonalSphereKernel_diag]
  exact hdiag

include ha hseries hκ hdiag hR hσ hε hε1 hB hBsmall hn

theorem spherical_minimax_single_block_lower (m : ℕ) (hmd : m ≤ Fintype.card ι)
    (hweight : (1-ε)*R^2/((Fintype.card ι).choose m : ℝ) ≤ B) :
    let k := rkhsFeature (H := H)
    let hk := zonalSphereFeature_memLp Φ hΦ hkernel
    highDimensionalBlockBayesRisk ((1-ε)*R^2*zonalSphereDegreeValue (ι := ι) a m^s)
      (((Fintype.card ι).choose m : ℝ)*σ^2/n) ≤
      (gaussianRangeMinimaxRisk k hk σ n (featureSourceBall k hk s hs R)).toReal +
        finiteGaussianShavingConstant κ s R*Real.exp (-priorShavingExponent ε R/(2*B)) := by
  classical
  dsimp only
  let k := rkhsFeature (H := H)
  let hk := zonalSphereFeature_memLp Φ hΦ hkernel
  let t := zonalSphereDegreeValue (ι := ι) a m
  let M := ((Fintype.card ι).choose m : ℝ)
  let S := (1-ε)*R^2
  let v : SquarefreeSphereIndex ι m → ℝ := fun _ => S*t^s/M
  have ht : 0 < t := zonalSphereDegreeValue_pos a (fun j => (ha j).le) Φ hseries m hmd (ha m)
  have hM : 0 < M := Nat.cast_pos.mpr (Nat.choose_pos hmd)
  have hS : 0 < S := by dsimp [S]; positivity
  have hA : 0 < S*t^s := mul_pos hS (Real.rpow_pos_of_pos ht _)
  obtain ⟨jmap, hj, hval⟩ := zonalSphere_exists_squarefree_prediction_index_embedding
    Φ hΦ hkernel a (fun j => (ha j).le) hseries m hmd (ha m)
  have hw (j : SquarefreeSphereIndex ι m) : (jmap j).1.1^(-s)*v j = S/M := by
    rw [hval]
    exact block_source_weight_eq ht s M S
  have hm : (∑ j, (jmap j).1.1^(-s)*v j) = S := by
    simp only [hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_squarefreeSphereIndex]
    change M*(S/M) = S
    field_simp
  have hmin := finiteGaussian_minimax_sourceBall_lower_exponential k hk jmap hj hκ
    (spherical_minimax_feature_bound Φ hkernel hκ hdiag) hs hR hσ n v
    (fun _ => div_pos hA hM) hε hε1 hB hBsmall (fun j => (hw j).trans_le hweight) hm
  have heq : (∑ j, ((v j)⁻¹+(n:ℝ)*(σ^2)⁻¹)⁻¹) =
      highDimensionalBlockBayesRisk (S*t^s) (M*σ^2/n) := by
    simp only [v, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_squarefreeSphereIndex]
    exact block_bayes_risk_eq hM hA hσ hn
  rwa [heq] at hmin

theorem spherical_minimax_two_block_lower (m : ℕ) (hmd : m+1 ≤ Fintype.card ι)
    (hgap : zonalSphereDegreeValue (ι := ι) a m ≠ zonalSphereDegreeValue (ι := ι) a (m+1))
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hweight0 : (1-ε)*R^2/((Fintype.card ι).choose m : ℝ) ≤ B)
    (hweight1 : (1-ε)*R^2/((Fintype.card ι).choose (m+1) : ℝ) ≤ B) :
    let k := rkhsFeature (H := H)
    let hk := zonalSphereFeature_memLp Φ hΦ hkernel
    highDimensionalBlockBayesRisk (r*((1-ε)*R^2)*zonalSphereDegreeValue (ι := ι) a m^s)
      (((Fintype.card ι).choose m : ℝ)*σ^2/n) +
    highDimensionalBlockBayesRisk ((1-r)*((1-ε)*R^2)*zonalSphereDegreeValue (ι := ι) a (m+1)^s)
      (((Fintype.card ι).choose (m+1) : ℝ)*σ^2/n) ≤
      (gaussianRangeMinimaxRisk k hk σ n (featureSourceBall k hk s hs R)).toReal +
        finiteGaussianShavingConstant κ s R*Real.exp (-priorShavingExponent ε R/(2*B)) := by
  classical
  dsimp only
  let k := rkhsFeature (H := H)
  let hk := zonalSphereFeature_memLp Φ hΦ hkernel
  let J₀ := SquarefreeSphereIndex ι m
  let J₁ := SquarefreeSphereIndex ι (m+1)
  let t₀ := zonalSphereDegreeValue (ι := ι) a m
  let t₁ := zonalSphereDegreeValue (ι := ι) a (m+1)
  let M₀ := ((Fintype.card ι).choose m : ℝ)
  let M₁ := ((Fintype.card ι).choose (m+1) : ℝ)
  let S := (1-ε)*R^2
  let S₀ := r*S
  let S₁ := (1-r)*S
  let v : J₀ ⊕ J₁ → ℝ := Sum.elim (fun _ => S₀*t₀^s/M₀) (fun _ => S₁*t₁^s/M₁)
  have hmd₀ : m ≤ Fintype.card ι := by omega
  have ht₀ : 0 < t₀ := zonalSphereDegreeValue_pos a (fun j => (ha j).le) Φ hseries m hmd₀ (ha m)
  have ht₁ : 0 < t₁ := zonalSphereDegreeValue_pos a (fun j => (ha j).le) Φ hseries (m+1) hmd (ha (m+1))
  have hM₀ : 0 < M₀ := Nat.cast_pos.mpr (Nat.choose_pos hmd₀)
  have hM₁ : 0 < M₁ := Nat.cast_pos.mpr (Nat.choose_pos hmd)
  have hS : 0 < S := by dsimp [S]; positivity
  have hS₀ : 0 < S₀ := mul_pos hr.1 hS
  have hS₁ : 0 < S₁ := mul_pos (sub_pos.mpr hr.2) hS
  have hA₀ : 0 < S₀*t₀^s := mul_pos hS₀ (Real.rpow_pos_of_pos ht₀ _)
  have hA₁ : 0 < S₁*t₁^s := mul_pos hS₁ (Real.rpow_pos_of_pos ht₁ _)
  obtain ⟨j₀, hj₀, hval₀⟩ := zonalSphere_exists_squarefree_prediction_index_embedding
    Φ hΦ hkernel a (fun j => (ha j).le) hseries m hmd₀ (ha m)
  obtain ⟨j₁, hj₁, hval₁⟩ := zonalSphere_exists_squarefree_prediction_index_embedding
    Φ hΦ hkernel a (fun j => (ha j).le) hseries (m+1) hmd (ha (m+1))
  let jmap : J₀ ⊕ J₁ → PredictionSingularIndex (featureEmbedding uniformSphere k hk) := Sum.elim j₀ j₁
  have hj : Function.Injective jmap := hj₀.sumElim hj₁ (by
    intro i j he
    apply hgap
    rw [← hval₀ i, ← hval₁ j, he])
  have hv (j : J₀ ⊕ J₁) : 0 < v j := by
    cases j with
    | inl i => exact div_pos hA₀ hM₀
    | inr i => exact div_pos hA₁ hM₁
  have hw₀ (j : J₀) : (jmap (Sum.inl j)).1.1^(-s)*v (Sum.inl j) = S₀/M₀ := by
    change (j₀ j).1.1^(-s)*(S₀*t₀^s/M₀) = _
    rw [hval₀]
    exact block_source_weight_eq ht₀ s M₀ S₀
  have hw₁ (j : J₁) : (jmap (Sum.inr j)).1.1^(-s)*v (Sum.inr j) = S₁/M₁ := by
    change (j₁ j).1.1^(-s)*(S₁*t₁^s/M₁) = _
    rw [hval₁]
    exact block_source_weight_eq ht₁ s M₁ S₁
  have hw (j : J₀ ⊕ J₁) : (jmap j).1.1^(-s)*v j ≤ B := by
    cases j with
    | inl i =>
      rw [hw₀]
      exact (div_le_div_of_nonneg_right (mul_le_of_le_one_left hS.le hr.2.le) hM₀.le).trans hweight0
    | inr i =>
      rw [hw₁]
      exact (div_le_div_of_nonneg_right (mul_le_of_le_one_left hS.le (by linarith [hr.1])) hM₁.le).trans hweight1
  have hm : (∑ j, (jmap j).1.1^(-s)*v j) = S := by
    rw [Fintype.sum_sum_type]
    simp only [hw₀, hw₁, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard₀ : (Fintype.card J₀ : ℝ) = M₀ := by dsimp [J₀, M₀]; rw [card_squarefreeSphereIndex]
    have hcard₁ : (Fintype.card J₁ : ℝ) = M₁ := by dsimp [J₁, M₁]; rw [card_squarefreeSphereIndex]
    rw [hcard₀, hcard₁]
    field_simp
    dsimp [S₀, S₁]
    ring
  have hmin := finiteGaussian_minimax_sourceBall_lower_exponential k hk jmap hj hκ
    (spherical_minimax_feature_bound Φ hkernel hκ hdiag) hs hR hσ n v hv hε hε1 hB hBsmall hw hm
  have heq : (∑ j, ((v j)⁻¹+(n:ℝ)*(σ^2)⁻¹)⁻¹) =
      highDimensionalBlockBayesRisk (S₀*t₀^s) (M₀*σ^2/n) +
      highDimensionalBlockBayesRisk (S₁*t₁^s) (M₁*σ^2/n) := by
    rw [Fintype.sum_sum_type]
    simp only [v, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard₀ : (Fintype.card J₀ : ℝ) = M₀ := by dsimp [J₀, M₀]; rw [card_squarefreeSphereIndex]
    have hcard₁ : (Fintype.card J₁ : ℝ) = M₁ := by dsimp [J₁, M₁]; rw [card_squarefreeSphereIndex]
    rw [hcard₀, hcard₁, block_bayes_risk_eq hM₀ hA₀ hσ hn, block_bayes_risk_eq hM₁ hA₁ hσ hn]
  rwa [heq] at hmin

end
end KernelSeq
