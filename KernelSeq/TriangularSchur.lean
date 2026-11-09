import KernelSeq.FourierSchur
import Mathlib.Data.Real.Sign

/-!
# Finite triangular Schur multipliers and the actual Cotlar identity

For an arbitrary finite real Hilbert basis and arbitrary scalar labels, the
sign multiplier and the projection onto equal-label blocks are constructed
from actual finite Hilbert--Schmidt columns. Repeated labels are retained as
whole diagonal blocks. The Cotlar identity below is an equality of actual
bounded operators, derived from the scalar sign identity and finite basis
multiplication. No triangular Schatten estimate or HMS bound is assumed.
-/

open scoped BigOperators

namespace KernelSeq

noncomputable section

/-- The scalar Cotlar identity, including all equal-label cases. -/
theorem triangularSign_cotlar (s t u : ℝ) :
    Real.sign (s - t) * Real.sign (t - u) =
      Real.sign (s - u) * (Real.sign (s - t) + Real.sign (t - u)) - 1 +
        (if s = t then 1 else 0) * (if t = u then 1 else 0) := by
  unfold Real.sign
  split_ifs <;> norm_num at * <;> grind

/-- Every real sign has modulus at most one. -/
theorem triangularSign_norm_le (s : ℝ) : ‖Real.sign s‖ ≤ 1 := by
  rcases Real.sign_apply_eq s with h | h | h <;> rw [h] <;> norm_num

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Actual HS columns of every operator with finite basis domain. -/
def finiteOperatorColumns (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    HilbertSchmidtColumns ι H := by
  classical
  exact ∑ j, lp.single 2 j (A (b j))

omit [CompleteSpace H] in
@[simp]
theorem finiteOperatorColumns_apply (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (j : ι) :
    finiteOperatorColumns b A j = A (b j) := by
  classical
  simp only [finiteOperatorColumns, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  simp

/-- Finite columns reconstruct the original actual operator. -/
theorem hilbertSchmidtOperator_finiteOperatorColumns (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) : hilbertSchmidtOperator b (finiteOperatorColumns b A) = A := by
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro j
  simp only [hilbertSchmidtOperator_basis, finiteOperatorColumns_apply]

/-- Matrix entries in the given actual Hilbert basis. -/
def finiteBasisEntry (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (i j : ι) : ℝ :=
  inner ℝ (b i) (A (b j))

omit [Fintype ι] [CompleteSpace H] in
/-- Equality of the actual finite-basis entries implies operator equality. -/
theorem finiteBasisEntry_ext (b : HilbertBasis ι ℝ H) {A B : H →L[ℝ] H}
    (h : ∀ i j, finiteBasisEntry b A i j = finiteBasisEntry b B i j) : A = B := by
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro j
  apply b.repr.injective
  ext i
  simpa only [HilbertBasis.repr_apply_apply, finiteBasisEntry] using h i j

omit [Fintype ι] [CompleteSpace H] in
@[simp]
theorem finiteBasisEntry_add (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b (A + B) i j = finiteBasisEntry b A i j + finiteBasisEntry b B i j := by
  simp only [finiteBasisEntry, add_apply, inner_add_right]

omit [Fintype ι] [CompleteSpace H] in
@[simp]
theorem finiteBasisEntry_sub (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b (A - B) i j = finiteBasisEntry b A i j - finiteBasisEntry b B i j := by
  simp only [finiteBasisEntry, sub_apply, inner_sub_right]

omit [Fintype ι] [CompleteSpace H] in
@[simp]
theorem finiteBasisEntry_neg (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b (-A) i j = -finiteBasisEntry b A i j := by
  simp only [finiteBasisEntry, neg_apply, inner_neg_right]

omit [CompleteSpace H] in
/-- Actual operator multiplication is finite basis matrix multiplication. -/
theorem finiteBasisEntry_mul (b : HilbertBasis ι ℝ H) (A B : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b (A * B) i j = ∑ k, finiteBasisEntry b A i k * finiteBasisEntry b B k j := by
  classical
  have hexp : (∑ k, inner ℝ (b k) (B (b j)) • b k) = B (b j) := by
    simpa only [← HilbertBasis.repr_apply_apply, tsum_fintype] using (b.hasSum_repr (B (b j))).tsum_eq
  conv_lhs => unfold finiteBasisEntry; rw [mul_apply_eq_comp, ← hexp]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, finiteBasisEntry]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Fintype ι] in
@[simp]
theorem finiteBasisEntry_adjoint (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b A.adjoint i j = finiteBasisEntry b A j i := by
  simp only [finiteBasisEntry, A.adjoint_inner_right, real_inner_comm]

/-- The actual finite Schur operator, built from genuine HS columns. -/
def finiteSchurOperator (b : HilbertBasis ι ℝ H) (M : ι → ι → ℝ) (A : H →L[ℝ] H) :
    H →L[ℝ] H :=
  hilbertSchmidtOperator b (finiteMatrixSchurColumns b M (finiteOperatorColumns b A))

@[simp]
theorem finiteSchurOperator_entry (b : HilbertBasis ι ℝ H) (M : ι → ι → ℝ)
    (A : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b (finiteSchurOperator b M A) i j = M i j * finiteBasisEntry b A i j := by
  exact (finiteMatrixSchurColumns_coefficient b b M (finiteOperatorColumns b A) i j).trans
    (by rw [finiteOperatorColumns_apply]; rfl)

/-- Finite real sign Schur multiplier with arbitrary, possibly repeated labels. -/
def triangularSchur (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) : H →L[ℝ] H :=
  finiteSchurOperator b (fun i j => Real.sign (x i - x j)) A

/-- The actual equal-label block projection; this is not merely the index diagonal. -/
def diagonalBlockSchur (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) : H →L[ℝ] H :=
  finiteSchurOperator b (fun i j => if x i = x j then 1 else 0) A

@[simp]
theorem triangularSchur_entry (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (A : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b (triangularSchur b x A) i j =
      Real.sign (x i - x j) * finiteBasisEntry b A i j := finiteSchurOperator_entry b _ A i j

@[simp]
theorem diagonalBlockSchur_entry (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (A : H →L[ℝ] H) (i j : ι) :
    finiteBasisEntry b (diagonalBlockSchur b x A) i j =
      (if x i = x j then 1 else 0) * finiteBasisEntry b A i j := finiteSchurOperator_entry b _ A i j

/-- The actual Cotlar identity. The final block term is necessary when scalar
labels coincide, including a wholly constant label family. -/
theorem triangularSchur_cotlar (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A B : H →L[ℝ] H) :
    triangularSchur b x A * triangularSchur b x B =
      triangularSchur b x (triangularSchur b x A * B + A * triangularSchur b x B) -
        A * B + diagonalBlockSchur b x A * diagonalBlockSchur b x B := by
  classical
  apply finiteBasisEntry_ext b
  intro i j
  simp only [finiteBasisEntry_mul, finiteBasisEntry_add, finiteBasisEntry_sub,
    triangularSchur_entry, diagonalBlockSchur_entry]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hs := triangularSign_cotlar (x i) (x k) (x j)
  calc
    _ = (Real.sign (x i - x k) * Real.sign (x k - x j)) *
        finiteBasisEntry b A i k * finiteBasisEntry b B k j := by ring
    _ = _ := by rw [hs]; ring

/-- The sign multiplier anticommutes with the actual adjoint. -/
theorem triangularSchur_adjoint (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) :
    triangularSchur b x A.adjoint = -(triangularSchur b x A).adjoint := by
  apply finiteBasisEntry_ext b
  intro i j
  simp only [triangularSchur_entry, finiteBasisEntry_adjoint, finiteBasisEntry_neg]
  have hs : Real.sign (x i - x j) = -Real.sign (x j - x i) := by
    rw [← Real.sign_neg, neg_sub]
  rw [hs]
  ring

/-- The equal-label block projection preserves actual adjoints. -/
theorem diagonalBlockSchur_adjoint (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) :
    diagonalBlockSchur b x A.adjoint = (diagonalBlockSchur b x A).adjoint := by
  apply finiteBasisEntry_ext b
  intro i j
  simp only [diagonalBlockSchur_entry, finiteBasisEntry_adjoint]
  by_cases h : x i = x j <;> simp [h, eq_comm]

omit [Fintype ι] [CompleteSpace H] in
/-- A real Schur kernel is symmetric as a map on the HS Hilbert space.
This is distinct from the adjoint of each reconstructed operator. -/
theorem hsSchurMultiplier_isSymmetric (b : HilbertBasis ι ℝ H)
    (M : ι → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K) :
    (hsSchurMultiplier b M K hK hM).IsSymmetric := by
  intro c d
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  exact hilbertDiagonal_isSymmetric b (fun i => M i j) K hK (fun i => hM i j) (c j) (d j)

/-- The genuine HS sign multiplier, as an actual bounded linear map. -/
def triangularSchurHS (b : HilbertBasis ι ℝ H) (x : ι → ℝ) :
    HilbertSchmidtColumns ι H →L[ℝ] HilbertSchmidtColumns ι H :=
  hsSchurMultiplier b (fun i j => Real.sign (x i - x j)) 1 zero_le_one
    (fun i j => triangularSign_norm_le (x i - x j))

/-- The genuine HS equal-label block projection. -/
def diagonalBlockSchurHS (b : HilbertBasis ι ℝ H) (x : ι → ℝ) :
    HilbertSchmidtColumns ι H →L[ℝ] HilbertSchmidtColumns ι H :=
  hsSchurMultiplier b (fun i j => if x i = x j then 1 else 0) 1 zero_le_one
    (fun i j => by split_ifs <;> norm_num)

/-- The genuine HS sign map agrees with the explicit finite matrix columns. -/
theorem triangularSchurHS_eq_finite (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (c : HilbertSchmidtColumns ι H) :
    triangularSchurHS b x c = finiteMatrixSchurColumns b (fun i j => Real.sign (x i - x j)) c :=
  (finiteMatrixSchurColumns_eq b b _ 1 zero_le_one _ c).symm

/-- The genuine HS block map agrees with the explicit finite matrix columns. -/
theorem diagonalBlockSchurHS_eq_finite (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (c : HilbertSchmidtColumns ι H) :
    diagonalBlockSchurHS b x c = finiteMatrixSchurColumns b (fun i j => if x i = x j then 1 else 0) c :=
  (finiteMatrixSchurColumns_eq b b _ 1 zero_le_one _ c).symm

omit [Fintype ι] [CompleteSpace H] in
/-- Both maps are actual contractions on the HS Hilbert space. -/
theorem triangularSchurHS_norm_le (b : HilbertBasis ι ℝ H) (x : ι → ℝ) :
    ‖triangularSchurHS b x‖ ≤ 1 := hsSchurMultiplier_norm_le b _ 1 zero_le_one _

omit [Fintype ι] [CompleteSpace H] in
theorem diagonalBlockSchurHS_norm_le (b : HilbertBasis ι ℝ H) (x : ι → ℝ) :
    ‖diagonalBlockSchurHS b x‖ ≤ 1 := hsSchurMultiplier_norm_le b _ 1 zero_le_one _

omit [Fintype ι] [CompleteSpace H] in
/-- The real sign multiplier is selfadjoint on the HS Hilbert space. -/
theorem triangularSchurHS_isSymmetric (b : HilbertBasis ι ℝ H) (x : ι → ℝ) :
    (triangularSchurHS b x).IsSymmetric := hsSchurMultiplier_isSymmetric b _ 1 zero_le_one _

omit [Fintype ι] [CompleteSpace H] in
/-- The equal-label block projection is selfadjoint on the HS Hilbert space. -/
theorem diagonalBlockSchurHS_isSymmetric (b : HilbertBasis ι ℝ H) (x : ι → ℝ) :
    (diagonalBlockSchurHS b x).IsSymmetric := hsSchurMultiplier_isSymmetric b _ 1 zero_le_one _

/-- Finite columns of a reconstructed HS operator are the original columns. -/
theorem finiteOperatorColumns_hilbertSchmidtOperator (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι H) :
    finiteOperatorColumns b (hilbertSchmidtOperator b c) = c := by
  ext j
  rw [finiteOperatorColumns_apply, hilbertSchmidtOperator_basis]

/-- The finite sign operator has exactly the genuine transformed HS columns. -/
theorem finiteOperatorColumns_triangularSchur (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (A : H →L[ℝ] H) :
    finiteOperatorColumns b (triangularSchur b x A) = triangularSchurHS b x (finiteOperatorColumns b A) := by
  rw [triangularSchur, finiteSchurOperator, finiteOperatorColumns_hilbertSchmidtOperator,
    triangularSchurHS_eq_finite]

/-- The finite block operator has exactly the genuine transformed HS columns. -/
theorem finiteOperatorColumns_diagonalBlockSchur (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (A : H →L[ℝ] H) :
    finiteOperatorColumns b (diagonalBlockSchur b x A) = diagonalBlockSchurHS b x (finiteOperatorColumns b A) := by
  rw [diagonalBlockSchur, finiteSchurOperator, finiteOperatorColumns_hilbertSchmidtOperator,
    diagonalBlockSchurHS_eq_finite]

/-- Actual finite operators satisfy the genuine HS contraction inequality. -/
theorem triangularSchur_hs_norm_le (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) :
    ‖finiteOperatorColumns b (triangularSchur b x A)‖ ≤ ‖finiteOperatorColumns b A‖ := by
  rw [finiteOperatorColumns_triangularSchur]
  simpa only [one_mul] using (triangularSchurHS b x).le_of_opNorm_le (triangularSchurHS_norm_le b x) _

theorem diagonalBlockSchur_hs_norm_le (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) :
    ‖finiteOperatorColumns b (diagonalBlockSchur b x A)‖ ≤ ‖finiteOperatorColumns b A‖ := by
  rw [finiteOperatorColumns_diagonalBlockSchur]
  simpa only [one_mul] using (diagonalBlockSchurHS b x).le_of_opNorm_le (diagonalBlockSchurHS_norm_le b x) _

/-- Applying the block map twice is the actual operator projection identity. -/
theorem diagonalBlockSchur_idempotent (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) :
    diagonalBlockSchur b x (diagonalBlockSchur b x A) = diagonalBlockSchur b x A := by
  apply finiteBasisEntry_ext b
  intro i j
  simp only [diagonalBlockSchur_entry]
  split_ifs <;> ring

/-- The square of the real sign multiplier is the complement of the
whole equal-label block map. -/
theorem triangularSchur_square (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) :
    triangularSchur b x (triangularSchur b x A) = A - diagonalBlockSchur b x A := by
  apply finiteBasisEntry_ext b
  intro i j
  simp only [triangularSchur_entry, finiteBasisEntry_sub, diagonalBlockSchur_entry]
  by_cases h : x i = x j
  · simp [h]
  · rw [if_neg h]
    rcases Real.sign_apply_eq_of_ne_zero (x i - x j) (sub_ne_zero.mpr h) with hs | hs <;> rw [hs] <;> ring

/-- Actual reconstruction intertwines the HS sign map with the finite
operator sign map. -/
theorem hilbertSchmidtOperator_triangularSchurHS (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (c : HilbertSchmidtColumns ι H) :
    hilbertSchmidtOperator b (triangularSchurHS b x c) = triangularSchur b x (hilbertSchmidtOperator b c) := by
  rw [triangularSchurHS_eq_finite, triangularSchur, finiteSchurOperator,
    finiteOperatorColumns_hilbertSchmidtOperator]

/-- Actual reconstruction intertwines the two block maps. -/
theorem hilbertSchmidtOperator_diagonalBlockSchurHS (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (c : HilbertSchmidtColumns ι H) :
    hilbertSchmidtOperator b (diagonalBlockSchurHS b x c) = diagonalBlockSchur b x (hilbertSchmidtOperator b c) := by
  rw [diagonalBlockSchurHS_eq_finite, diagonalBlockSchur, finiteSchurOperator,
    finiteOperatorColumns_hilbertSchmidtOperator]

/-- The block map is an actual orthogonal projection on the HS Hilbert space. -/
theorem diagonalBlockSchurHS_idempotent (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (c : HilbertSchmidtColumns ι H) :
    diagonalBlockSchurHS b x (diagonalBlockSchurHS b x c) = diagonalBlockSchurHS b x c := by
  apply hilbertSchmidtOperator_injective b
  rw [hilbertSchmidtOperator_diagonalBlockSchurHS, hilbertSchmidtOperator_diagonalBlockSchurHS,
    diagonalBlockSchur_idempotent]

/-- The true square of the HS sign map is the orthogonal block complement. -/
theorem triangularSchurHS_square (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (c : HilbertSchmidtColumns ι H) :
    triangularSchurHS b x (triangularSchurHS b x c) = c - diagonalBlockSchurHS b x c := by
  apply hilbertSchmidtOperator_injective b
  rw [hilbertSchmidtOperator_triangularSchurHS, hilbertSchmidtOperator_triangularSchurHS,
    triangularSchur_square, map_sub, hilbertSchmidtOperator_diagonalBlockSchurHS]

/-- Exact HS energy splitting between unequal-label entries and equal-label
blocks. In particular, neither a nonempty index nor distinct labels are needed. -/
theorem triangularSchurHS_energy (b : HilbertBasis ι ℝ H) (x : ι → ℝ)
    (c : HilbertSchmidtColumns ι H) :
    ‖triangularSchurHS b x c‖ ^ 2 + ‖diagonalBlockSchurHS b x c‖ ^ 2 = ‖c‖ ^ 2 := by
  have hH := triangularSchurHS_isSymmetric b x c (triangularSchurHS b x c)
  have hD := diagonalBlockSchurHS_isSymmetric b x c (diagonalBlockSchurHS b x c)
  change inner ℝ (triangularSchurHS b x c) (triangularSchurHS b x c) =
    inner ℝ c (triangularSchurHS b x (triangularSchurHS b x c)) at hH
  change inner ℝ (diagonalBlockSchurHS b x c) (diagonalBlockSchurHS b x c) =
    inner ℝ c (diagonalBlockSchurHS b x (diagonalBlockSchurHS b x c)) at hD
  rw [triangularSchurHS_square, inner_sub_right] at hH
  rw [diagonalBlockSchurHS_idempotent] at hD
  simp only [real_inner_self_eq_norm_sq] at hH hD
  linarith

/-- The same exact energy identity for arbitrary actual finite operators. -/
theorem triangularSchur_hs_energy (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A : H →L[ℝ] H) :
    ‖finiteOperatorColumns b (triangularSchur b x A)‖ ^ 2 +
      ‖finiteOperatorColumns b (diagonalBlockSchur b x A)‖ ^ 2 = ‖finiteOperatorColumns b A‖ ^ 2 := by
  rw [finiteOperatorColumns_triangularSchur, finiteOperatorColumns_diagonalBlockSchur]
  exact triangularSchurHS_energy b x (finiteOperatorColumns b A)

/-- The block map has the actual left module property of a conditional
expectation onto equal-label block operators. -/
theorem diagonalBlockSchur_mul_left (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A B : H →L[ℝ] H) :
    diagonalBlockSchur b x (diagonalBlockSchur b x A * B) =
      diagonalBlockSchur b x A * diagonalBlockSchur b x B := by
  classical
  apply finiteBasisEntry_ext b
  intro i j
  simp only [diagonalBlockSchur_entry, finiteBasisEntry_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : x i = x k
  · by_cases hkj : x k = x j
    · have hij := hik.trans hkj
      simp only [if_pos hik, if_pos hkj, if_pos hij, one_mul]
    · have hij : x i ≠ x j := by simpa only [hik] using hkj
      simp only [if_pos hik, if_neg hkj, if_neg hij, zero_mul, one_mul, mul_zero]
  · simp only [if_neg hik, zero_mul, mul_zero]

/-- The corresponding actual right module property. -/
theorem diagonalBlockSchur_mul_right (b : HilbertBasis ι ℝ H) (x : ι → ℝ) (A B : H →L[ℝ] H) :
    diagonalBlockSchur b x (A * diagonalBlockSchur b x B) =
      diagonalBlockSchur b x A * diagonalBlockSchur b x B := by
  classical
  apply finiteBasisEntry_ext b
  intro i j
  simp only [diagonalBlockSchur_entry, finiteBasisEntry_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkj : x k = x j
  · by_cases hik : x i = x k
    · have hij := hik.trans hkj
      simp only [if_pos hik, if_pos hkj, if_pos hij, one_mul]
    · have hij : x i ≠ x j := by simpa only [← hkj] using hik
      simp only [if_neg hik, if_pos hkj, if_neg hij, zero_mul, one_mul]
  · simp only [if_neg hkj, zero_mul, mul_zero]

/-- Constant scalar grids, including the empty index case, give the zero sign
operator. -/
theorem triangularSchur_const (b : HilbertBasis ι ℝ H) (r : ℝ) (A : H →L[ℝ] H) :
    triangularSchur b (fun _ => r) A = 0 := by
  apply finiteBasisEntry_ext b
  intro i j
  rw [triangularSchur_entry]
  simp [finiteBasisEntry]

/-- For a constant grid, the equal-label block map is the identity. -/
theorem diagonalBlockSchur_const (b : HilbertBasis ι ℝ H) (r : ℝ) (A : H →L[ℝ] H) :
    diagonalBlockSchur b (fun _ => r) A = A := by
  apply finiteBasisEntry_ext b
  intro i j
  simp

end
end KernelSeq
