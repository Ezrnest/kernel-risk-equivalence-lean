import KernelSeq.PinskerVarianceAsymptotics
import Mathlib.Analysis.Asymptotics.Theta

/-!
# The original Pinsker oracle and sharp leading constant

The Pinsker oracle scale and leading risk constant use `rho=s*beta`.
The scale comparison and the leading objective identities are actual scalar
proofs; an oracle balance equation is not assumed.
-/

namespace KernelSeq

open Filter Topology Asymptotics
noncomputable section

def pinskerOracleExponent (s β : ℝ) : ℝ := β / (s * β + 1)
def pinskerRiskExponent (s β : ℝ) : ℝ := (s * β) / (s * β + 1)

def pinskerOracleScale (s β R σ D n : ℝ) : ℝ :=
  (σ ^ 2 * D * (s * β) / (n * R ^ 2 * (s * β + 1) * (s * β + 2))) ^
    (β / (s * β + 1))

/-- Exactly the displayed manuscript constant, without replacing it by a
different normalization of the oracle objective. -/
def pinskerUpperConstant (s β R σ D : ℝ) : ℝ :=
  D ^ ((s * β) / (s * β + 1)) * R ^ (2 / (s * β + 1)) *
    (σ ^ 2) ^ ((s * β) / (s * β + 1)) * (s * β + 1) ^ (1 / (s * β + 1)) *
    ((s * β) / (s * β + 2)) ^ ((s * β) / (s * β + 1))

def pinskerLeadingObjective (s β R σ D n lam : ℝ) : ℝ :=
  R ^ 2 * lam ^ s + (σ ^ 2 * D / n) * pinskerVarianceConstant s β * lam ^ (-(1 / β))

private def oracleCoefficient (s β R σ D : ℝ) : ℝ :=
  σ ^ 2 * D * (s * β) / (R ^ 2 * (s * β + 1) * (s * β + 2))

private theorem oracleCoefficient_pos {s β R σ D : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) :
    0 < oracleCoefficient s β R σ D := by unfold oracleCoefficient; positivity

theorem pinskerOracleExponent_pos {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    0 < pinskerOracleExponent s β := by unfold pinskerOracleExponent; positivity

theorem pinskerOracleExponent_lt_one {s β : ℝ} (hs : 1 ≤ s) (hβ : 0 < β) :
    pinskerOracleExponent s β < 1 := by
  unfold pinskerOracleExponent
  apply (div_lt_one (by positivity : 0 < s * β + 1)).2
  nlinarith

theorem pinskerOracleScale_pos {s β R σ D n : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n) :
    0 < pinskerOracleScale s β R σ D n := by unfold pinskerOracleScale; positivity

theorem pinskerUpperConstant_pos {s β R σ D : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) :
    0 < pinskerUpperConstant s β R σ D := by unfold pinskerUpperConstant; positivity

private theorem oracleScale_eq_mul {s β R σ D n : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n) :
    pinskerOracleScale s β R σ D n =
      oracleCoefficient s β R σ D ^ pinskerOracleExponent s β * n ^ (-pinskerOracleExponent s β) := by
  have hc := oracleCoefficient_pos hs hβ hR hσ hD
  have hb : σ ^ 2 * D * (s * β) / (n * R ^ 2 * (s * β + 1) * (s * β + 2)) =
      oracleCoefficient s β R σ D / n := by unfold oracleCoefficient; field_simp
  rw [pinskerOracleScale, hb, Real.div_rpow hc.le hn.le, Real.rpow_neg hn.le]
  rfl

/-- The actual oracle has the exact original sample-power schedule, with
fixed comparison constants and no asymptotic rate premise. -/
theorem pinskerOracleScale_isTheta {I : Type*} {l : Filter I} (n : I → ℝ)
    (hn : ∀ i, 0 < n i) {s β R σ D : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) :
    (fun i => pinskerOracleScale s β R σ D (n i)) =Θ[l]
      (fun i => n i ^ (-pinskerOracleExponent s β)) := by
  have hc := oracleCoefficient_pos hs hβ hR hσ hD
  have heq : (fun i => pinskerOracleScale s β R σ D (n i)) =
      (fun i => oracleCoefficient s β R σ D ^ pinskerOracleExponent s β *
        n i ^ (-pinskerOracleExponent s β)) :=
    funext (fun i => oracleScale_eq_mul hs hβ hR hσ hD (hn i))
  rw [heq]
  exact isTheta_rfl.const_mul_left (Real.rpow_pos_of_pos hc _).ne'

/-- The defining oracle power equation is proved from the displayed scale. -/
theorem pinskerOracleScale_power {s β R σ D n : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n) :
    pinskerOracleScale s β R σ D n ^ (s + 1 / β) =
      σ ^ 2 * D * (s * β) / (n * R ^ 2 * (s * β + 1) * (s * β + 2)) := by
  have hr : 0 < s * β := mul_pos hs hβ
  unfold pinskerOracleScale
  rw [← Real.rpow_mul (by positivity)]
  have he : β / (s * β + 1) * (s + 1 / β) = 1 := by field_simp
  rw [he, Real.rpow_one]

/-- The leading variance at the actual oracle is `s*beta` times its bias. -/
theorem pinskerOracleScale_balance {s β R σ D n : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n) :
    (σ ^ 2 * D / n) * pinskerVarianceConstant s β *
      pinskerOracleScale s β R σ D n ^ (-(1 / β)) =
      (s * β) * (R ^ 2 * pinskerOracleScale s β R σ D n ^ s) := by
  have hl := pinskerOracleScale_pos hs hβ hR hσ hD hn
  have hp := pinskerOracleScale_power hs hβ hR hσ hD hn
  rw [Real.rpow_add hl] at hp
  rw [Real.rpow_neg hl.le, ← div_eq_mul_inv]
  apply (div_eq_iff (Real.rpow_pos_of_pos hl (1 / β)).ne').2
  rw [show (s * β) * (R ^ 2 * pinskerOracleScale s β R σ D n ^ s) *
      pinskerOracleScale s β R σ D n ^ (1 / β) =
      (s * β) * R ^ 2 * (pinskerOracleScale s β R σ D n ^ s *
        pinskerOracleScale s β R σ D n ^ (1 / β)) by ring, hp]
  unfold pinskerVarianceConstant
  have hr : 0 < s * β := mul_pos hs hβ
  have hz1 : s * β + 1 ≠ 0 := by positivity
  have hz2 : s * β + 2 ≠ 0 := by positivity
  field_simp

private theorem upperConstant_eq_factor {s β R σ D : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) :
    pinskerUpperConstant s β R σ D =
      ((s * β + 1) * R ^ 2) * oracleCoefficient s β R σ D ^ pinskerRiskExponent s β := by
  let r := s * β
  let a := r / (r + 1)
  have hr : 0 < r := mul_pos hs hβ
  have hz : 0 < r + 1 := by positivity
  have hw : 0 < r + 2 := by positivity
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have ha : 1 / (r + 1) + a = 1 := by dsimp only [a]; field_simp; ring
  have hRa : 2 / (r + 1) + 2 * a = 2 := by dsimp only [a]; field_simp; ring
  have hRfac : R ^ (2 / (r + 1)) * (R ^ 2) ^ a = R ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hR.le, ← Real.rpow_add hR, hRa, Real.rpow_two]
  have hZfac : (r + 1) ^ (1 / (r + 1)) * (r + 1) ^ a = r + 1 := by
    rw [← Real.rpow_add hz, ha, Real.rpow_one]
  have hfac : ((r + 1) ^ (1 / (r + 1)) * R ^ (2 / (r + 1))) *
      ((R ^ 2) ^ a * (r + 1) ^ a) = (r + 1) * R ^ 2 := by
    calc
      _ = (R ^ (2 / (r + 1)) * (R ^ 2) ^ a) *
        ((r + 1) ^ (1 / (r + 1)) * (r + 1) ^ a) := by ring
      _ = _ := by rw [hRfac, hZfac]; ring
  change D ^ a * R ^ (2 / (r + 1)) * (σ ^ 2) ^ a * (r + 1) ^ (1 / (r + 1)) *
    (r / (r + 2)) ^ a = ((r + 1) * R ^ 2) *
      (σ ^ 2 * D * r / (R ^ 2 * (r + 1) * (r + 2))) ^ a
  rw [Real.div_rpow hr.le hw.le, Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ σ ^ 2 * D) hr.le,
    Real.mul_rpow (sq_nonneg σ) hD.le,
    Real.mul_rpow (by positivity : 0 ≤ R ^ 2 * (r + 1)) hw.le,
    Real.mul_rpow hR2.le hz.le]
  have h1 := (Real.rpow_pos_of_pos hR2 a).ne'
  have h2 := (Real.rpow_pos_of_pos hz a).ne'
  have h3 := (Real.rpow_pos_of_pos hw a).ne'
  field_simp
  convert hfac using 1; ring

/-- The actual leading objective equals the original sharp constant times
the manuscript's sample power, for every positive sample size. -/
theorem pinskerOracleScale_objective {s β R σ D n : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n) :
    pinskerLeadingObjective s β R σ D n (pinskerOracleScale s β R σ D n) =
      pinskerUpperConstant s β R σ D * n ^ (-pinskerRiskExponent s β) := by
  have hl := pinskerOracleScale_pos hs hβ hR hσ hD hn
  have hc := oracleCoefficient_pos hs hβ hR hσ hD
  have he : pinskerOracleExponent s β * s = pinskerRiskExponent s β := by
    unfold pinskerOracleExponent pinskerRiskExponent
    ring
  have hpow : pinskerOracleScale s β R σ D n ^ s =
      oracleCoefficient s β R σ D ^ pinskerRiskExponent s β * n ^ (-pinskerRiskExponent s β) := by
    rw [oracleScale_eq_mul hs hβ hR hσ hD hn,
      Real.mul_rpow (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hn.le _),
      ← Real.rpow_mul hc.le, ← Real.rpow_mul hn.le, he]
    rw [neg_mul, he]
  rw [pinskerLeadingObjective, pinskerOracleScale_balance hs hβ hR hσ hD hn, hpow,
    upperConstant_eq_factor hs hβ hR hσ hD]
  ring

theorem pinskerRiskExponent_pos {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    0 < pinskerRiskExponent s β := by unfold pinskerRiskExponent; positivity

theorem pinskerRiskExponent_lt_one {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    pinskerRiskExponent s β < 1 := by
  unfold pinskerRiskExponent
  exact (div_lt_one (by positivity : 0 < s * β + 1)).2 (by linarith)

/-- Exact bias component of the original oracle objective. -/
theorem pinskerOracleScale_bias {s β R σ D n : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n) :
    R ^ 2 * pinskerOracleScale s β R σ D n ^ s =
      (pinskerUpperConstant s β R σ D / (s * β + 1)) * n ^ (-pinskerRiskExponent s β) := by
  have hz : 0 < s * β + 1 := by positivity
  have hh := pinskerOracleScale_objective hs hβ hR hσ hD hn
  rw [pinskerLeadingObjective, pinskerOracleScale_balance hs hβ hR hσ hD hn] at hh
  calc
    _ = (pinskerUpperConstant s β R σ D * n ^ (-pinskerRiskExponent s β)) / (s * β + 1) := by
      apply (eq_div_iff hz.ne').2
      convert hh using 1; ring
    _ = _ := by ring

theorem pinskerOracleScale_tendsto_zero {I : Type*} {l : Filter I} (n : I → ℝ)
    (hn0 : ∀ i, 0 < n i) (hn : Tendsto n l atTop) {s β R σ D : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) :
    Tendsto (fun i => pinskerOracleScale s β R σ D (n i)) l (𝓝 0) :=
  (pinskerOracleScale_isTheta n hn0 hs hβ hR hσ hD).tendsto_zero_iff.mpr
    ((tendsto_rpow_neg_atTop (pinskerOracleExponent_pos hs hβ)).comp hn)

private theorem balanced_power_sum_strict {s γ x : ℝ}
    (hs : 0 < s) (hγ : 0 < γ) (hx : 0 < x) (hx1 : x ≠ 1) :
    1 + s / γ < x ^ s + (s / γ) * x ^ (-γ) := by
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  have h1 := Real.add_one_lt_exp (mul_ne_zero hlog hs.ne')
  have h2 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (Real.log x * (-γ)))
    (div_pos hs hγ).le
  have he : (s / γ) * (Real.log x * (-γ)) = -(Real.log x * s) := by field_simp
  rw [mul_add, mul_one, he] at h2
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx]
  linarith

private theorem balanced_power_sum_min {s γ x : ℝ}
    (hs : 0 < s) (hγ : 0 < γ) (hx : 0 < x) :
    1 + s / γ ≤ x ^ s + (s / γ) * x ^ (-γ) := by
  by_cases hx1 : x = 1
  · simp [hx1]
  · exact (balanced_power_sum_strict hs hγ hx hx1).le

/-- Every other positive regularization has a strictly larger leading
objective. The proof uses the genuine exponential tangent inequality, and
the oracle balance is the previously proved identity for the actual scale. -/
theorem pinskerOracleScale_strict_min {s β R σ D n lam : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n)
    (hlam : 0 < lam) (hne : lam ≠ pinskerOracleScale s β R σ D n) :
    pinskerLeadingObjective s β R σ D n (pinskerOracleScale s β R σ D n) <
      pinskerLeadingObjective s β R σ D n lam := by
  let a := pinskerOracleScale s β R σ D n
  let x := lam / a
  let b := R ^ 2 * a ^ s
  have ha : 0 < a := pinskerOracleScale_pos hs hβ hR hσ hD hn
  have hx : 0 < x := div_pos hlam ha
  have hb : 0 < b := mul_pos (sq_pos_of_pos hR) (Real.rpow_pos_of_pos ha _)
  have hγ : 0 < 1 / β := one_div_pos.mpr hβ
  have hr : s / (1 / β) = s * β := by field_simp
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    exact (div_eq_one_iff_eq ha.ne').mp h
  have hscale (q : ℝ) : lam ^ q = a ^ q * x ^ q := by
    rw [← Real.mul_rpow ha.le hx.le]
    congr 1
    dsimp only [x]
    field_simp
  have hbal : (σ ^ 2 * D / n) * pinskerVarianceConstant s β * a ^ (-(1 / β)) =
      (s * β) * b := pinskerOracleScale_balance hs hβ hR hσ hD hn
  have hF : pinskerLeadingObjective s β R σ D n lam = b * (x ^ s + (s * β) * x ^ (-(1 / β))) := by
    unfold pinskerLeadingObjective
    rw [hscale s, hscale (-(1 / β))]
    calc
      _ = b * x ^ s + ((σ ^ 2 * D / n) * pinskerVarianceConstant s β * a ^ (-(1 / β))) *
          x ^ (-(1 / β)) := by dsimp only [b]; ring
      _ = _ := by rw [hbal]; ring
  have hFa : pinskerLeadingObjective s β R σ D n a = b * (1 + s * β) := by
    unfold pinskerLeadingObjective
    rw [hbal]
    dsimp only [b]
    ring
  have hmin := balanced_power_sum_strict hs hγ hx hx1
  rw [hr] at hmin
  change pinskerLeadingObjective s β R σ D n a < _
  rw [hFa, hF]
  exact mul_lt_mul_of_pos_left hmin hb

theorem pinskerOracleScale_global_min {s β R σ D n lam : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n)
    (hlam : 0 < lam) :
    pinskerLeadingObjective s β R σ D n (pinskerOracleScale s β R σ D n) ≤
      pinskerLeadingObjective s β R σ D n lam := by
  by_cases he : lam = pinskerOracleScale s β R σ D n
  · rw [he]
  · exact (pinskerOracleScale_strict_min hs hβ hR hσ hD hn hlam he).le

theorem pinskerOracleScale_objective_eq_iff {s β R σ D n lam : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n)
    (hlam : 0 < lam) :
    pinskerLeadingObjective s β R σ D n lam =
      pinskerLeadingObjective s β R σ D n (pinskerOracleScale s β R σ D n) ↔
      lam = pinskerOracleScale s β R σ D n := by
  constructor
  · intro he
    by_contra hne
    exact (pinskerOracleScale_strict_min hs hβ hR hσ hD hn hlam hne).ne he.symm
  · rintro rfl
    rfl

theorem pinskerLeadingObjective_hasDerivAt {s β R σ D n lam : ℝ} (hlam : 0 < lam) :
    HasDerivAt (pinskerLeadingObjective s β R σ D n)
      ((s * R ^ 2 * lam ^ s - (1 / β) * ((σ ^ 2 * D / n) * pinskerVarianceConstant s β) *
        lam ^ (-(1 / β))) / lam) lam := by
  change HasDerivAt (fun z => R ^ 2 * z ^ s +
    (σ ^ 2 * D / n) * pinskerVarianceConstant s β * z ^ (-(1 / β))) _ lam
  have h1 := (Real.hasDerivAt_rpow_const (p := s) (Or.inl hlam.ne')).const_mul (R ^ 2)
  have h2 := (Real.hasDerivAt_rpow_const (p := -(1 / β)) (Or.inl hlam.ne')).const_mul
    ((σ ^ 2 * D / n) * pinskerVarianceConstant s β)
  apply (h1.add h2).congr_deriv
  rw [Real.rpow_sub_one hlam.ne', Real.rpow_sub_one hlam.ne']
  ring

/-- The original scale is the unique positive critical point of the actual
leading objective. The derivative and balance equation are derived here. -/
theorem pinskerLeadingObjective_deriv_eq_zero_iff {s β R σ D n lam : ℝ}
    (hs : 0 < s) (hβ : 0 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D) (hn : 0 < n)
    (hlam : 0 < lam) :
    deriv (pinskerLeadingObjective s β R σ D n) lam = 0 ↔
      lam = pinskerOracleScale s β R σ D n := by
  let a := pinskerOracleScale s β R σ D n
  let γ := 1 / β
  let v := (σ ^ 2 * D / n) * pinskerVarianceConstant s β
  have ha : 0 < a := pinskerOracleScale_pos hs hβ hR hσ hD hn
  have hγ : 0 < γ := one_div_pos.mpr hβ
  have hLp : 0 < lam ^ γ := Real.rpow_pos_of_pos hlam _
  have hSR : 0 < s * R ^ 2 := mul_pos hs (sq_pos_of_pos hR)
  have hpower : 0 < s + γ := add_pos hs hγ
  have hconst : s * R ^ 2 * a ^ (s + γ) = γ * v := by
    dsimp only [a, γ, v]
    rw [pinskerOracleScale_power hs hβ hR hσ hD hn]
    unfold pinskerVarianceConstant
    have hr : 0 < s * β := mul_pos hs hβ
    field_simp
  have hscaled : (s * R ^ 2 * lam ^ s - γ * v * lam ^ (-γ)) * lam ^ γ =
      (s * R ^ 2) * (lam ^ (s + γ) - a ^ (s + γ)) := by
    rw [Real.rpow_add hlam, Real.rpow_neg hlam.le]
    have htmp : (s * R ^ 2 * lam ^ s - γ * v * (lam ^ γ)⁻¹) * lam ^ γ =
        s * R ^ 2 * (lam ^ s * lam ^ γ) - γ * v := by field_simp
    rw [htmp, ← hconst, Real.rpow_add ha]
    ring
  have heq : (s * R ^ 2 * lam ^ s - γ * v * lam ^ (-γ) = 0) ↔
      lam ^ (s + γ) - a ^ (s + γ) = 0 := by
    have he : (s * R ^ 2 * lam ^ s - γ * v * lam ^ (-γ)) * lam ^ γ = 0 ↔
        (s * R ^ 2) * (lam ^ (s + γ) - a ^ (s + γ)) = 0 := by rw [hscaled]
    simpa only [mul_eq_zero, hLp.ne', or_false, hSR.ne', false_or] using he
  rw [(pinskerLeadingObjective_hasDerivAt hlam).deriv, div_eq_zero_iff]
  simp only [hlam.ne', or_false]
  change (s * R ^ 2 * lam ^ s - γ * v * lam ^ (-γ) = 0) ↔ _
  rw [heq, sub_eq_zero, Real.rpow_left_inj hlam.le ha.le hpower.ne']

end
end KernelSeq
