import KernelSeq.CovarianceMoments
import KernelSeq.OperatorTrace
import Mathlib.Probability.Independence.Basic

/-!
# The common-variance finite Bernstein interface needed by covariance sums

Unlike the broader general intrinsic Bernstein proposition, this interface
uses a common per-increment variance majorant `V/n`. This is exactly the
structure of the sampled centered rank-one covariance operators. Its proof
can use Golden--Thompson and a scalar recurrence, without a general Lieb
concavity theorem. The actual constructor is proved in `ProvedBernstein`;
merely defining this proposition is not that proof.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ι H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace Ω]

local instance uniformBernsteinMeasurableSpace : MeasurableSpace (H →L[ℝ] H) := borel _
local instance uniformBernsteinBorelSpace : BorelSpace (H →L[ℝ] H) := ⟨rfl⟩

/-- The common-majorant version, with precisely the intrinsic trace factor,
threshold and exponent used by the actual covariance application. The
per-increment condition is an upstream deterministic variance bound, not a
desired concentration or asymptotic-rate premise. -/
def FiniteUniformIntrinsicBernstein (b : HilbertBasis ι ℝ H) (P : Measure Ω) : Prop :=
  IsProbabilityMeasure P → FiniteDimensional ℝ H →
  ∀ (n : ℕ) (Y : Fin n → Ω → H →L[ℝ] H) (R : ℝ) (V : H →L[ℝ] H) (t : ℝ),
    0 ≤ R →
    (∀ i, AEStronglyMeasurable (Y i) P) →
    (∀ i, Integrable (Y i) P) →
    (∀ i, Integrable (fun ω => Y i ω * Y i ω) P) →
    iIndepFun Y P →
    (∀ i, (∫ ω, Y i ω ∂P) = 0) →
    (∀ i, ∀ᵐ ω ∂P, IsSelfAdjoint (Y i ω)) →
    (∀ i, ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ R) →
    V.IsPositive →
    (∀ i, (∫ ω, Y i ω * Y i ω ∂P) ≤ (n : ℝ)⁻¹ • V) →
    0 < ‖V‖ → Real.sqrt ‖V‖ + R / 3 ≤ t →
    P {ω | t ≤ ‖∑ i, Y i ω‖} ≤
      ENNReal.ofReal (8 * (basisTrace b V / ‖V‖) *
        Real.exp (-(t ^ 2) / (2 * (‖V‖ + R * t / 3))))

end
end KernelSeq
