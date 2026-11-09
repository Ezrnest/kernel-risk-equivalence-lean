import KernelSeq.SpectralEnergy
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Weighted spectral sums in two actual Hilbert eigenbases

Cross Parseval accounts for every multiplicity even when eigenvalues repeat.
The extended nonnegative sum needs no summability assumption. Finiteness
and regrouping of a real nonnegative series are then proved rather than
assigned to the second basis.
-/

namespace KernelSeq

open scoped ENNReal BigOperators RealInnerProductSpace
noncomputable section

variable {G I J : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem hilbertBasis_tsum_ofReal_inner_sq (b : HilbertBasis I ℝ G) (x : G) :
    (∑' i, ENNReal.ofReal (inner ℝ (b i) x ^ 2)) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have hrep (i : I) : inner ℝ (b i) x = b.repr x i := by rw [b.repr_apply_apply]
  simp only [hrep]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hilbertBasis_coefficients_sq_summable b x),
    ← hilbertBasis_norm_sq_eq_tsum b x]

theorem eigenbases_tsum_eq_ennreal
    (T : G →L[ℝ] G) (hT : T.IsSymmetric) (b : HilbertBasis I ℝ G) (e : HilbertBasis J ℝ G)
    (t : I → ℝ) (u : J → ℝ) (hb : ∀ i, T (b i) = t i • b i)
    (he : ∀ j, T (e j) = u j • e j) (w : ℝ → ℝ≥0∞) :
    (∑' i, w (t i)) = ∑' j, w (u j) := by
  let P (i : I) (j : J) := ENNReal.ofReal (inner ℝ (b i) (e j) ^ 2)
  have hcol (j : J) : (∑' i, P i j) = 1 := by
    dsimp only [P]
    rw [hilbertBasis_tsum_ofReal_inner_sq, e.orthonormal.norm_eq_one j]
    simp
  have hrow (i : I) : (∑' j, P i j) = 1 := by
    have hs : (fun j => P i j) = (fun j => ENNReal.ofReal (inner ℝ (e j) (b i) ^ 2)) := by
      funext j
      exact congrArg (fun r : ℝ => ENNReal.ofReal (r^2)) (real_inner_comm _ _)
    rw [hs, hilbertBasis_tsum_ofReal_inner_sq, b.orthonormal.norm_eq_one i]
    simp
  have hentry (i : I) (j : J) : w (t i) * P i j = w (u j) * P i j := by
    by_cases h : t i = u j
    · rw [h]
    have hh := hT (b i) (e j)
    change inner ℝ (T (b i)) (e j) = inner ℝ (b i) (T (e j)) at hh
    rw [hb i, he j, real_inner_smul_left, real_inner_smul_right] at hh
    have hm : (t i-u j) * inner ℝ (b i) (e j) = 0 := by linarith only [hh]
    have h0 := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h)
    simp [P, h0]
  calc
    (∑' i, w (t i)) = ∑' i, ∑' j, w (t i) * P i j := by
      apply tsum_congr; intro i
      rw [ENNReal.tsum_mul_left, hrow, mul_one]
    _ = ∑' i, ∑' j, w (u j) * P i j := by
      exact tsum_congr (fun i => tsum_congr (hentry i))
    _ = ∑' j, ∑' i, w (u j) * P i j := ENNReal.tsum_comm
    _ = ∑' j, w (u j) := by
      apply tsum_congr; intro j
      rw [ENNReal.tsum_mul_left, hcol, mul_one]

/-- Transfer finite nonnegative spectral mass and sum from one true
eigenbasis to another. Neither index is required to be countable. -/
theorem eigenbases_hasSum_of_nonneg
    (T : G →L[ℝ] G) (hT : T.IsSymmetric) (b : HilbertBasis I ℝ G) (e : HilbertBasis J ℝ G)
    (t : I → ℝ) (u : J → ℝ) (hb : ∀ i, T (b i) = t i • b i)
    (he : ∀ j, T (e j) = u j • e j) (w : ℝ → ℝ)
    (ht : ∀ i, 0 ≤ w (t i)) (hu : ∀ j, 0 ≤ w (u j)) (hs : Summable (fun i => w (t i))) :
    HasSum (fun j => w (u j)) (∑' i, w (t i)) := by
  have h := eigenbases_tsum_eq_ennreal T hT b e t u hb he (fun r => ENNReal.ofReal (w r))
  change (∑' i, ENNReal.ofReal (w (t i))) = (∑' j, ENNReal.ofReal (w (u j))) at h
  rw [← ENNReal.ofReal_tsum_of_nonneg ht hs] at h
  have hne : (∑' j, ENNReal.ofReal (w (u j))) ≠ ∞ := h ▸ ENNReal.ofReal_ne_top
  have hout := ENNReal.hasSum_toReal hne
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), ← h,
    ENNReal.toReal_ofReal (tsum_nonneg ht)] at hout
  simpa only [ENNReal.toReal_ofReal (hu _)] using hout

/-- Regroup a positive spectral series over the actual finite multiplicities
of its labelled layers. The grouped series has the same genuine sum. -/
theorem hasSum_finiteMultiplicity_of_nonneg {M : Type*} (d : M → ℕ) (w : M → ℝ)
    (hw : ∀ m, 0 ≤ w m) {v : ℝ}
    (hs : HasSum (fun p : Σ m, Fin (d m) => w p.1) v) :
    HasSum (fun m => (d m : ℝ) * w m) v := by
  have h := ENNReal.tsum_sigma' (fun p : Σ m, Fin (d m) => ENNReal.ofReal (w p.1))
  have hv : 0 ≤ v := hs.tsum_eq ▸ tsum_nonneg (fun p => hw p.1)
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun p : Σ m, Fin (d m) => w p.1)
    (fun p => hw p.1) hs.summable, hs.tsum_eq] at h
  have hinner (m : M) : (∑' _ : Fin (d m), ENNReal.ofReal (w m)) = ENNReal.ofReal ((d m : ℝ)*w m) := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  simp only [hinner] at h
  have hne : (∑' m, ENNReal.ofReal ((d m : ℝ)*w m)) ≠ ∞ := h ▸ ENNReal.ofReal_ne_top
  have hout := ENNReal.hasSum_toReal hne
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), ← h,
    ENNReal.toReal_ofReal hv] at hout
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (hw _))] using hout

end
end KernelSeq
