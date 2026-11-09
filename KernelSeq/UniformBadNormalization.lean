import KernelSeq.ExpectationBadNormalization
import KernelSeq.ExpectationScale

/-!
# Common normalization constants for varying targets and noise levels

Only a positive common lower bound on noise standard deviations is used.
The displayed source-derived target envelope removes all target dependence
from the constant. Actual source and bad-risk bounds are supplied in the
model specialization, rather than postulated there.
-/

namespace KernelSeq
noncomputable section

def uniformBadRiskConstant (A κ s0 : ℝ) : ℝ :=
  8 * (((A*κ^2)^2+2*(1+(A*κ^2)^2)/s0^2) *
    (1+A^2*(1+κ^2)) * ((A*κ^2)^2+2))

theorem uniformBadRiskConstant_nonneg (A κ s0 : ℝ) : 0≤uniformBadRiskConstant A κ s0 := by
  unfold uniformBadRiskConstant
  positivity

theorem uniformBadRiskConstant_pos (A κ : ℝ) {s0 : ℝ} (hs0 : 0<s0) :
    0<uniformBadRiskConstant A κ s0 := by
  have hd : 0<2*(1+(A*κ^2)^2)/s0^2 := by positivity
  unfold uniformBadRiskConstant
  positivity

theorem uniform_noise_normalization_le {F B σ s0 : ℝ}
    (hF : 0≤F) (hB : 0≤B) (hs0 : 0<s0) (hσ : s0≤σ) :
    (2*F+B*(2*F+σ^2))/σ^2 ≤ (B+2*(1+B)/s0^2)*(1+F) := by
  have hσ0 : 0<σ := hs0.trans_le hσ
  have hsquares : s0^2≤σ^2 := pow_le_pow_left₀ hs0.le hσ 2
  have hD : 0≤2*(1+B)/s0^2 := by positivity
  calc
    _ = B+(2*(1+B)*F)/σ^2 := by field_simp; ring
    _ ≤ B+(2*(1+B)*F)/s0^2 := add_le_add le_rfl
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hs0) hsquares)
    _ = B+(2*(1+B)/s0^2)*F := by ring
    _ ≤ _ := by nlinarith [mul_nonneg hB hF]

theorem one_add_target_le_source_polynomial {F a H ζ : ℝ}
    (ha : 0≤a) (hH : 0≤H) (hζ : 0≤ζ) (hF : F≤a*(1+H)*ζ) :
    1+F≤(1+a)*(1+H)*(1+ζ) := by
  nlinarith [mul_nonneg ha hH, mul_nonneg hH hζ]

/-- A genuine scalar reduction with a common constant independent of the
target, noise upper bound, regularization and sample size. The finite-model
theorem below supplies every displayed numerical inequality from actual data. -/
theorem uniform_normalize_bad_risk_envelope_le {I D n lam Q σ s0 F A κ p : ℝ}
    (hn : 1≤n) (hlam : 0<lam) (hQ : 0<Q) (hQn : Q≤n)
    (hs0 : 0<s0) (hσ : s0≤σ) (hF : 0≤F) (hp : 0≤p)
    {ζ : ℝ} (hζ : 0≤ζ)
    (hsource : F≤A^2*(1+κ^2)*(1+n/(lam*Q))*ζ)
    (hsquare : lam^2*Q≤(A*κ^2)^2)
    (hD : σ^2/n*Q≤D)
    (hI : I≤(2*F+(A*κ^2/lam)^2*(2*F+σ^2))*(8*p)) :
    I/D≤uniformBadRiskConstant A κ s0*(1+n/(lam*Q))^3*(1+ζ)*p := by
  let B := (A*κ^2)^2
  let C0 := B+2*(1+B)/s0^2
  let H := n/(lam*Q)
  let a := A^2*(1+κ^2)
  have hn0 : 0<n := by linarith
  have hσ0 : 0<σ := hs0.trans_le hσ
  have hB : 0≤B := sq_nonneg _
  have hC0 : 0≤C0 := by dsimp only [C0]; positivity
  have hH : 0≤H := by dsimp only [H]; positivity
  have ha : 0≤a := by dsimp only [a]; positivity
  have hIt : I≤(2*F+(B*(2*F+σ^2))/lam^2)*(8*p) := by
    convert hI using 1
    dsimp only [B]
    ring
  have hb := normalize_bad_risk_envelope_le hn0 hlam hQ hσ0
    (show 0≤2*F by positivity) (show 0≤B*(2*F+σ^2) by positivity)
    (show 0≤8*p by positivity) hD hIt
  have hnorm : (2*F+B*(2*F+σ^2))/σ^2≤C0*(1+F) :=
    uniform_noise_normalization_le hF hB hs0 hσ
  have htarget : 1+F≤(1+a)*(1+H)*(1+ζ) :=
    one_add_target_le_source_polynomial ha hH hζ hsource
  have hpoly : 1+n/Q+n/(lam^2*Q)≤(B+2)*(1+H)^2 :=
    expectation_global_envelope_le_of_square_bound hn hlam hQ hQn hB hsquare
  calc
    _ ≤ ((2*F+B*(2*F+σ^2))/σ^2)*(1+n/Q+n/(lam^2*Q))*(8*p) := hb
    _ ≤ (C0*((1+a)*(1+H)*(1+ζ)))*((B+2)*(1+H)^2)*(8*p) := by
      gcongr
      exact hnorm.trans (mul_le_mul_of_nonneg_left htarget hC0)
    _ = _ := by dsimp only [uniformBadRiskConstant, C0, B, a, H]; ring

end
end KernelSeq
