import CompND.SemiConvexDiffAtMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-- Differentiability of `u` at a maximum point of the relabelled difference. If
`y ↦ u y + λ e^{u y}` is locally semi-convex on `Ω`, `-v` is locally semi-convex on `Ω`,
and `x ∈ Ω` maximizes `(u + λ e^{u}) - v` over `Ω`, then `u` itself is Fréchet
differentiable at `x`. The relabelling `ψ_λ(s) = s + λ e^{s}` is expanding and has
derivative `1 + λ e^{s} ≥ 1`, so the differentiability of `ψ_λ ∘ u` supplied by
`SemiConvexDiffAtMax` descends to `u`, with derivative scaled by `(1 + λ e^{u x})⁻¹`. -/
theorem ExpRelabelledMaxDifferentiability {N : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin N)))
    (lam : ℝ) (hlam : 0 < lam) (u v : EuclideanSpace ℝ (Fin N) → ℝ)
    (hulamsc : LocallySemiConvexOn Ω (fun y => u y + lam * Real.exp (u y)))
    (hvsc : LocallySemiConvexOn Ω (fun y => -v y))
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ Ω)
    (hmax : IsMaxOn (fun y => (u y + lam * Real.exp (u y)) - v y) Ω x) :
    ∃ D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ, HasFDerivAt u D x := by
  -- name the relabelling `ψ_λ(s) = s + λ e^s` and transfer the two hypotheses to it
  obtain ⟨psi, hpsidef⟩ : ∃ psi : ℝ → ℝ, ∀ s, psi s = s + lam * Real.exp s :=
    ⟨fun s => s + lam * Real.exp s, fun _ => rfl⟩
  have hpsifun : psi = fun s => s + lam * Real.exp s := funext hpsidef
  have hulamsc' : LocallySemiConvexOn Ω (fun y => psi (u y)) := by
    have hfe : (fun y => psi (u y)) = fun y => u y + lam * Real.exp (u y) :=
      funext fun y => hpsidef (u y)
    rw [hfe]
    exact hulamsc
  have hmax' : IsMaxOn (fun y => psi (u y) - v y) Ω x := by
    have hfe : (fun y => psi (u y) - v y)
        = fun y => (u y + lam * Real.exp (u y)) - v y :=
      funext fun y => by rw [hpsidef]
    rw [hfe]
    exact hmax
  -- `ψ_λ` is differentiable with `ψ_λ′(s) = 1 + λ e^s`: an elementary computation for an
  -- explicit function, so no relabelling node is needed here
  have hpHD : ∀ a : ℝ, HasDerivAt psi (1 + lam * Real.exp a) a := by
    intro a
    rw [hpsifun]
    exact (hasDerivAt_id a).add (HasDerivAt.const_mul lam (Real.hasDerivAt_exp a))
  have hpdiff : Differentiable ℝ psi := fun a => (hpHD a).differentiableAt
  have hpderiv : ∀ a : ℝ, deriv psi a = 1 + lam * Real.exp a := fun a => (hpHD a).deriv
  -- `ψ_λ` is expanding because `ψ_λ s - ψ_λ s' = (s - s') + λ (e^s - e^{s'})`
  have hexpand : ∀ s s' : ℝ, |s - s'| ≤ |psi s - psi s'| := by
    intro s s'
    have hd : psi s - psi s' = s - s' + lam * (Real.exp s - Real.exp s') := by
      simp only [hpsidef]; ring
    rcases le_total s' s with h | h
    · have hp : (0:ℝ) ≤ lam * (Real.exp s - Real.exp s') :=
        mul_nonneg hlam.le (by linarith [Real.exp_le_exp.2 h])
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - s'), hd, abs_of_nonneg (by linarith)]
      linarith
    · have hp : lam * (Real.exp s - Real.exp s') ≤ 0 := by
        nlinarith [Real.exp_le_exp.2 h, hlam.le]
      rw [abs_of_nonpos (by linarith : s - s' ≤ 0), hd, abs_of_nonpos (by linarith)]
      linarith
  obtain ⟨Dl, hDl, -⟩ :=
    (SemiConvexDiffAtMax Ω (fun y => psi (u y)) v hulamsc' hvsc).2 x hx hmax'
  have ht1 : (1:ℝ) ≤ 1 + lam * Real.exp (u x) := by
    nlinarith [hlam.le, Real.exp_pos (u x)]
  have htpos : (0:ℝ) < 1 + lam * Real.exp (u x) := by linarith
  have hpa := (hpdiff (u x)).hasDerivAt
  rw [hpderiv (u x)] at hpa
  refine ⟨(1 + lam * Real.exp (u x))⁻¹ • Dl, ?_⟩
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hLpos : (0:ℝ) < ‖Dl‖ + 1 := by positivity
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1
    (Asymptotics.isLittleO_iff.1 (hasFDerivAt_iff_isLittleO.1 hDl) (c := 1) one_pos)
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.1
    (Asymptotics.isLittleO_iff.1 (hasFDerivAt_iff_isLittleO.1 hDl)
      (c := c * (1 + lam * Real.exp (u x)) / 2) (by positivity))
  obtain ⟨η, hη, hbp⟩ := Metric.eventually_nhds_iff_ball.1
    (Asymptotics.isLittleO_iff.1 (hasDerivAt_iff_isLittleO.1 hpa)
      (c := c * (1 + lam * Real.exp (u x)) / (2 * (‖Dl‖ + 1))) (by positivity))
  refine Metric.eventually_nhds_iff_ball.2
    ⟨min δ₁ (min δ₂ (η / (‖Dl‖ + 2))),
      lt_min hδ₁ (lt_min hδ₂ (by positivity)), fun y hy => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hy1 : y ∈ Metric.ball x δ₁ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hy ((min_le_left _ _))
  have hy2 : y ∈ Metric.ball x δ₂ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_left _ _))
  have hy3 : ‖y - x‖ < η / (‖Dl‖ + 2) :=
    lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_right _ _))
  have hnn : (0:ℝ) ≤ ‖y - x‖ := norm_nonneg _
  -- the crude bound `|u y - u x| ≤ (‖Dl‖ + 1) ‖y - x‖`
  have hc1 : |psi (u y) - psi (u x) - Dl (y - x)| ≤ 1 * ‖y - x‖ := by
    simpa [Real.norm_eq_abs] using hb₁ y hy1
  have hDlb : |Dl (y - x)| ≤ ‖Dl‖ * ‖y - x‖ := by
    simpa [Real.norm_eq_abs] using Dl.le_opNorm (y - x)
  have hcrude : |u y - u x| ≤ (‖Dl‖ + 1) * ‖y - x‖ := by
    refine (hexpand (u y) (u x)).trans ?_
    rw [abs_le] at hc1 hDlb ⊢
    constructor <;> linarith only [hc1.1, hc1.2, hDlb.1, hDlb.2]
  -- the `ψ_λ`-Taylor bound at `s := u y`, legitimate because `|u y - u x| < η`
  have hyη : u y ∈ Metric.ball (u x) η := by
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : (‖Dl‖ + 1) * ‖y - x‖ ≤ (‖Dl‖ + 1) * (η / (‖Dl‖ + 2)) :=
      mul_le_mul_of_nonneg_left hy3.le hLpos.le
    have h2 : (‖Dl‖ + 1) * (η / (‖Dl‖ + 2)) < η := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg Dl, hη]
    linarith only [hcrude, h1, h2]
  have hc3 : |psi (u y) - psi (u x) - (u y - u x) * (1 + lam * Real.exp (u x))|
      ≤ c * (1 + lam * Real.exp (u x)) / (2 * (‖Dl‖ + 1)) * |u y - u x| := by
    simpa [Real.norm_eq_abs] using hbp (u y) hyη
  have hc2 : |psi (u y) - psi (u x) - Dl (y - x)|
      ≤ c * (1 + lam * Real.exp (u x)) / 2 * ‖y - x‖ := by
    simpa [Real.norm_eq_abs] using hb₂ y hy2
  -- combine: `|t (u y - u x) - Dl (y - x)| ≤ c t ‖y - x‖`
  have hstep : c * (1 + lam * Real.exp (u x)) / (2 * (‖Dl‖ + 1)) * |u y - u x|
      ≤ c * (1 + lam * Real.exp (u x)) / 2 * ‖y - x‖ := by
    have h1 : c * (1 + lam * Real.exp (u x)) / (2 * (‖Dl‖ + 1)) * |u y - u x|
        ≤ c * (1 + lam * Real.exp (u x)) / (2 * (‖Dl‖ + 1))
          * ((‖Dl‖ + 1) * ‖y - x‖) :=
      mul_le_mul_of_nonneg_left hcrude (by positivity)
    have h2 : c * (1 + lam * Real.exp (u x)) / (2 * (‖Dl‖ + 1))
          * ((‖Dl‖ + 1) * ‖y - x‖)
        = c * (1 + lam * Real.exp (u x)) / 2 * ‖y - x‖ := by
      field_simp
    linarith only [h1, h2]
  have hcomb : |(u y - u x) * (1 + lam * Real.exp (u x)) - Dl (y - x)|
      ≤ c * (1 + lam * Real.exp (u x)) * ‖y - x‖ := by
    have hid2 : (u y - u x) * (1 + lam * Real.exp (u x)) - Dl (y - x)
        = -(psi (u y) - psi (u x)
              - (u y - u x) * (1 + lam * Real.exp (u x)))
          + (psi (u y) - psi (u x) - Dl (y - x)) := by ring
    rw [hid2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith only [hc3, hc2, hstep]
  -- divide by `t ≥ 1`
  have hfin : ‖u y - u x - ((1 + lam * Real.exp (u x))⁻¹ • Dl) (y - x)‖
      ≤ c * ‖y - x‖ := by
    have happ : ((1 + lam * Real.exp (u x))⁻¹ • Dl) (y - x)
        = (1 + lam * Real.exp (u x))⁻¹ * Dl (y - x) := by simp
    have hinv : (0:ℝ) < (1 + lam * Real.exp (u x))⁻¹ := by positivity
    have hrw : u y - u x - (1 + lam * Real.exp (u x))⁻¹ * Dl (y - x)
        = (1 + lam * Real.exp (u x))⁻¹
          * ((u y - u x) * (1 + lam * Real.exp (u x)) - Dl (y - x)) := by
      field_simp
    rw [Real.norm_eq_abs, happ, hrw, abs_mul, abs_of_pos hinv]
    have h1 : (1 + lam * Real.exp (u x))⁻¹
          * |(u y - u x) * (1 + lam * Real.exp (u x)) - Dl (y - x)|
        ≤ (1 + lam * Real.exp (u x))⁻¹
          * (c * (1 + lam * Real.exp (u x)) * ‖y - x‖) :=
      mul_le_mul_of_nonneg_left hcomb hinv.le
    have h2 : (1 + lam * Real.exp (u x))⁻¹
          * (c * (1 + lam * Real.exp (u x)) * ‖y - x‖) = c * ‖y - x‖ := by
      field_simp
    linarith only [h1, h2]
  simpa using hfin
