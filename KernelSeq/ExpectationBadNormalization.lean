import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalizing the actual global bad-risk envelope

The exact sequence risk dominates its strictly positive noise variance term.
This elementary reduction preserves that denominator even when the bias or
the total risk tends to zero. Its inputs are numerical inequalities, supplied
by the actual risk and sequence identities in the application.
-/

namespace KernelSeq

theorem normalize_bad_risk_envelope_le {I D n lam Q σ F K p : ℝ}
    (hn : 0 < n) (hlam : 0 < lam) (hQ : 0 < Q) (hσ : 0 < σ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hD : σ ^ 2 / n * Q ≤ D)
    (hI : I ≤ (F + K / lam ^ 2) * p) :
    I / D ≤ ((F + K) / σ ^ 2) *
      (1 + n / Q + n / (lam ^ 2 * Q)) * p := by
  have hbase : 0 < σ ^ 2 / n * Q := mul_pos (div_pos (sq_pos_of_pos hσ) hn) hQ
  have hDpos : 0 < D := hbase.trans_le hD
  have hC : 0 ≤ (F + K) / σ ^ 2 := by positivity
  calc
    _ ≤ ((F + K / lam ^ 2) * p) / D :=
      div_le_div_of_nonneg_right hI hDpos.le
    _ ≤ ((F + K / lam ^ 2) * p) / (σ ^ 2 / n * Q) :=
      div_le_div_of_nonneg_left (by positivity) hbase hD
    _ = (F / σ ^ 2 * (n / Q) + K / σ ^ 2 * (n / (lam ^ 2 * Q))) * p := by
      field_simp
    _ ≤ (((F + K) / σ ^ 2) * (n / Q) +
        ((F + K) / σ ^ 2) * (n / (lam ^ 2 * Q))) * p := by
      gcongr <;> linarith
    _ ≤ _ := by
      nlinarith [mul_nonneg hC hp]

end KernelSeq
