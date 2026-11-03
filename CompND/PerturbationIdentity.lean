import CompND.Lop
import CompND.NormalizedAH
import CompND.Ellip
import CompND.TwiceDiffAt
import Mathlib.Analysis.Calculus.Taylor

/-- lem:tech: if `ψ ∈ C²(ℝ)` has `ψ'(w x₀) > 0` and `w` has a second-order jet `(D, B)` at
`x₀` with non-vanishing horizontal gradient `ξ₀`, then `ψ ∘ w` has the second-order jet
`(t D, t B + ψ''(w x₀) D ⊗ D)` at `x₀` with `t = ψ'(w x₀)`, its horizontal gradient is
`t ξ₀`, and eq:estLh holds:
`ℒ(ψ ∘ w)(x₀) = t [ℒw(x₀) - (ψ''/ψ')(w x₀) 𝓔(ξ₀)]`. -/
theorem PerturbationIdentity {n m : ℕ}
    (sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ) (hN : NormalizedAH m A H)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hw : TwiceDiffAt w x₀ D B) (hg : hgrad sig x₀ D ≠ 0)
    (ht : 0 < deriv ψ (w x₀)) :
    TwiceDiffAt (fun y => ψ (w y)) x₀ (deriv ψ (w x₀) • D)
        (deriv ψ (w x₀) • B + deriv (deriv ψ) (w x₀) • D.smulRight D) ∧
      hgrad sig x₀ (deriv ψ (w x₀) • D) = deriv ψ (w x₀) • hgrad sig x₀ D ∧
      Lop sig A H x₀ (deriv ψ (w x₀) • D)
          (deriv ψ (w x₀) • B + deriv (deriv ψ) (w x₀) • D.smulRight D)
        = deriv ψ (w x₀) *
            (Lop sig A H x₀ D B
              - deriv (deriv ψ) (w x₀) / deriv ψ (w x₀) * Ellip A (hgrad sig x₀ D)) := by
  set t : ℝ := deriv ψ (w x₀) with hdt
  set c : ℝ := deriv (deriv ψ) (w x₀) with hdc
  set ξ₀ : EuclideanSpace ℝ (Fin m) := hgrad sig x₀ D with hξ
  -- the first jet scales
  have hgr : hgrad sig x₀ (t • D) = t • ξ₀ := by
    ext i
    simp [hgrad, hξ]
  -- the correction matrix is linear in the first jet
  have hMf : Mfield sig x₀ (t • D) = t • Mfield sig x₀ D := by
    ext i j
    simp [Mfield]
    ring
  -- the second jet splits
  set Xi : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => ξ₀ i * ξ₀ j with hXidef
  have hcomp : ∀ i : Fin m, D (sig x₀ i) = ξ₀ i := by
    intro i; simp [hξ, hgrad]
  have hhe : hhessS sig x₀ (t • D) (t • B + c • D.smulRight D)
      = t • hhessS sig x₀ D B + c • Xi := by
    ext i j
    simp [hhessS, hMf, hXidef, hcomp i, hcomp j, Matrix.add_apply]
    ring
  -- the trace against `Xi` is the ellipticity function
  have hXitr : (A ξ₀ * Xi).trace = Ellip A ξ₀ := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Ellip, hXidef, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨?_, hgr, ?_⟩
  · -- the second-order jet of `ψ ∘ w` at `x₀`
    -- Step 1: a Peano expansion for `ψ` at `a := w x₀`, from Taylor's little-o theorem.
    have step1 : ∀ e : ℝ, 0 < e → ∃ ρ > 0, ∀ s : ℝ, |s| < ρ →
        |ψ (w x₀ + s) - ψ (w x₀) - t * s - 1 / 2 * c * s ^ 2| ≤ e * s ^ 2 := by
      intro e he
      have hlo := taylor_isLittleO_univ (f := ψ) (x₀ := w x₀) (n := 2) hψ
      rw [Asymptotics.isLittleO_iff] at hlo
      obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlo he)
      refine ⟨ρ, hρ, fun s hs => ?_⟩
      have hmem : w x₀ + s ∈ Metric.ball (w x₀) ρ := by
        rw [Metric.mem_ball, Real.dist_eq]
        simpa using hs
      have h := hball _ hmem
      have heq : ψ (w x₀ + s) - taylorWithinEval ψ 2 Set.univ (w x₀) (w x₀ + s)
          = ψ (w x₀ + s) - ψ (w x₀) - t * s - 1 / 2 * c * s ^ 2 := by
        simp [iteratedDerivWithin_univ, iteratedDeriv_succ, iteratedDeriv_zero, hdt, hdc]
        ring
      have habs : ‖(w x₀ + s - w x₀) ^ 2‖ = s ^ 2 := by
        rw [show w x₀ + s - w x₀ = s by ring, Real.norm_eq_abs]
        exact abs_of_nonneg (by positivity)
      rw [Real.norm_eq_abs, heq, habs] at h
      exact h
    -- the two jets of `ψ ∘ w`, applied
    have hDapp : ∀ u : EuclideanSpace ℝ (Fin n), (t • D) u = t * D u := by
      intro u; simp
    have hBapp : ∀ u v : EuclideanSpace ℝ (Fin n),
        (t • B + c • D.smulRight D) u v = t * B u v + c * (D u * D v) := by
      intro u v; simp
    constructor
    · -- symmetry of the second jet
      intro u v
      rw [hBapp, hBapp, hw.1 u v]
      ring
    -- Step 2: the Peano estimate.
    intro ε hε
    set C₀ : ℝ := ‖D‖ + ‖B‖ / 2 + 1 with hC₀
    set C₁ : ℝ := ‖B‖ / 2 + 1 with hC₁
    have hC₀pos : 0 < C₀ := by rw [hC₀]; positivity
    have hC₁pos : 0 < C₁ := by rw [hC₁]; positivity
    obtain ⟨ρ, hρ, hstep1⟩ := step1 (ε / (3 * (C₀ ^ 2 + 1))) (by positivity)
    obtain ⟨δ₁, hδ₁, hRe⟩ := hw.2 (ε / (3 * (|t| + 1))) (by positivity)
    obtain ⟨δ₀, hδ₀, hR0⟩ := hw.2 1 one_pos
    have hden : (0:ℝ) < 3 * (|c| + 1) * C₁ * (C₀ + ‖D‖ + 1) := by positivity
    have hC01 : (0:ℝ) < C₀ + 1 := by linarith
    refine ⟨min (min δ₀ 1) (min δ₁ (min (ρ / (C₀ + 1))
        (2 * ε / (3 * (|c| + 1) * C₁ * (C₀ + ‖D‖ + 1))))), ?_, ?_⟩
    · exact lt_min (lt_min hδ₀ one_pos) (lt_min hδ₁ (lt_min (by positivity) (by positivity)))
    intro y hy
    set hv : EuclideanSpace ℝ (Fin n) := y - x₀ with hhv
    set S : ℝ := w y - w x₀ with hS
    have hb0 : ‖hv‖ < δ₀ := lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_left _ _))
    have hb1 : ‖hv‖ < 1 := lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_right _ _))
    have hbd1 : ‖hv‖ < δ₁ := lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_left _ _))
    have hbr : ‖hv‖ < ρ / (C₀ + 1) :=
      lt_of_lt_of_le hy ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hbt : ‖hv‖ < 2 * ε / (3 * (|c| + 1) * C₁ * (C₀ + ‖D‖ + 1)) :=
      lt_of_lt_of_le hy ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hnn : (0:ℝ) ≤ ‖hv‖ := norm_nonneg _
    have hN2 : ‖hv‖ ^ 2 = ‖hv‖ * ‖hv‖ := by ring
    have hsq : ‖hv‖ * ‖hv‖ ≤ ‖hv‖ := mul_le_of_le_one_right hnn hb1.le
    have hR0' : |S - D hv - 1 / 2 * B hv hv| ≤ 1 * ‖hv‖ ^ 2 := hR0 y hb0
    have hRe' : |S - D hv - 1 / 2 * B hv hv| ≤ ε / (3 * (|t| + 1)) * ‖hv‖ ^ 2 := hRe y hbd1
    have hDh : |D hv| ≤ ‖D‖ * ‖hv‖ := by
      simpa [Real.norm_eq_abs] using D.le_opNorm hv
    have hBh : |B hv hv| ≤ ‖B‖ * ‖hv‖ * ‖hv‖ := by
      have h1 : ‖B hv hv‖ ≤ ‖B hv‖ * ‖hv‖ := (B hv).le_opNorm hv
      have h2 : ‖B hv‖ ≤ ‖B‖ * ‖hv‖ := B.le_opNorm hv
      have h3 : ‖B hv hv‖ ≤ ‖B‖ * ‖hv‖ * ‖hv‖ := h1.trans (mul_le_mul_of_nonneg_right h2 hnn)
      simpa [Real.norm_eq_abs] using h3
    have hBsq : ‖B‖ * (‖hv‖ * ‖hv‖) ≤ ‖B‖ * ‖hv‖ := mul_le_mul_of_nonneg_left hsq (norm_nonneg B)
    obtain ⟨hr1, hr2⟩ := abs_le.1 hR0'
    obtain ⟨hd1, hd2⟩ := abs_le.1 hDh
    obtain ⟨hbb1, hbb2⟩ := abs_le.1 hBh
    -- (3)
    have h3 : |S| ≤ C₀ * ‖hv‖ := by
      rw [hC₀, abs_le]
      rw [hN2] at hr1 hr2
      constructor <;> linarith only [hr1, hr2, hd1, hd2, hbb1, hbb2, hBsq, hsq]
    -- (4)
    have h4 : |S - D hv| ≤ C₁ * ‖hv‖ ^ 2 := by
      rw [hC₁, abs_le]
      rw [hN2] at hr1 hr2 ⊢
      constructor <;> linarith only [hr1, hr2, hbb1, hbb2]
    have h3' : |S + D hv| ≤ (C₀ + ‖D‖) * ‖hv‖ := by
      obtain ⟨hs1, hs2⟩ := abs_le.1 h3
      rw [abs_le]
      constructor <;> linarith only [hs1, hs2, hd1, hd2]
    -- `|S| < ρ`, so Step 1 applies at `s := S`
    have hSρ : |S| < ρ := by
      have e0 : ‖hv‖ * (C₀ + 1) < ρ := by
        rw [← lt_div_iff₀ hC01]; exact hbr
      linarith only [h3, e0, hnn]
    have hT1 := hstep1 S hSρ
    have hS2 : S ^ 2 ≤ C₀ ^ 2 * ‖hv‖ ^ 2 := by
      have hps := mul_self_le_mul_self (abs_nonneg S) h3
      rw [abs_mul_abs_self] at hps
      linarith only [hps]
    -- the three estimates
    have hT1b : |ψ (w x₀ + S) - ψ (w x₀) - t * S - 1 / 2 * c * S ^ 2| ≤ ε / 3 * ‖hv‖ ^ 2 := by
      have hd : (0:ℝ) < 3 * (C₀ ^ 2 + 1) := by positivity
      have hq : ε / (3 * (C₀ ^ 2 + 1)) * S ^ 2 ≤ ε / 3 * ‖hv‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hd]
        linarith only [mul_le_mul_of_nonneg_left hS2 hε.le, mul_nonneg hε.le (sq_nonneg ‖hv‖)]
      linarith only [hT1, hq]
    have hT2b : |t * (S - D hv - 1 / 2 * B hv hv)| ≤ ε / 3 * ‖hv‖ ^ 2 := by
      rw [abs_mul]
      have hd : (0:ℝ) < 3 * (|t| + 1) := by positivity
      have h1 : |t| * |S - D hv - 1 / 2 * B hv hv|
          ≤ |t| * (ε / (3 * (|t| + 1)) * ‖hv‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hRe' (abs_nonneg t)
      refine h1.trans ?_
      rw [div_mul_eq_mul_div, ← mul_div_assoc, div_le_iff₀ hd]
      linarith only [mul_nonneg hε.le (sq_nonneg ‖hv‖)]
    have hT3b : |1 / 2 * c * (S ^ 2 - D hv ^ 2)| ≤ ε / 3 * ‖hv‖ ^ 2 := by
      have hid : S ^ 2 - D hv ^ 2 = (S - D hv) * (S + D hv) := by ring
      rw [hid]
      have habs2 : |1 / 2 * c * ((S - D hv) * (S + D hv))|
          = 1 / 2 * |c| * (|S - D hv| * |S + D hv|) := by
        rw [abs_mul, abs_mul, abs_mul]
        norm_num
      rw [habs2]
      have hprod : |S - D hv| * |S + D hv| ≤ (C₁ * ‖hv‖ ^ 2) * ((C₀ + ‖D‖) * ‖hv‖) :=
        mul_le_mul h4 h3' (abs_nonneg _) (by positivity)
      have hstep : 1 / 2 * |c| * (|S - D hv| * |S + D hv|)
          ≤ 1 / 2 * |c| * ((C₁ * ‖hv‖ ^ 2) * ((C₀ + ‖D‖) * ‖hv‖)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      refine hstep.trans ?_
      have hbt' : ‖hv‖ * (3 * (|c| + 1) * C₁ * (C₀ + ‖D‖ + 1)) < 2 * ε := by
        rw [← lt_div_iff₀ hden]; exact hbt
      have hcube : ‖hv‖ ^ 2 * (‖hv‖ * (3 * (|c| + 1) * C₁ * (C₀ + ‖D‖ + 1)))
          ≤ ‖hv‖ ^ 2 * (2 * ε) := mul_le_mul_of_nonneg_left hbt'.le (sq_nonneg _)
      have hCD : (0:ℝ) ≤ C₀ + ‖D‖ := by linarith only [hC₀pos, norm_nonneg D]
      have hfac : |c| * C₁ * (C₀ + ‖D‖) ≤ (|c| + 1) * C₁ * (C₀ + ‖D‖ + 1) := by
        have e1 : |c| * C₁ * (C₀ + ‖D‖) ≤ (|c| + 1) * C₁ * (C₀ + ‖D‖) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith only [abs_nonneg c]) hC₁pos.le) hCD
        have e2 : (|c| + 1) * C₁ * (C₀ + ‖D‖) ≤ (|c| + 1) * C₁ * (C₀ + ‖D‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith only [])
            (mul_nonneg (by linarith only [abs_nonneg c]) hC₁pos.le)
        linarith only [e1, e2]
      have hmul := mul_le_mul_of_nonneg_right hfac (by positivity : (0:ℝ) ≤ ‖hv‖ ^ 3)
      linarith only [hcube, hmul]
    -- the algebraic split, and the conclusion
    have hψw : ψ (w x₀ + S) = ψ (w y) := by
      congr 1
      rw [hS]; ring
    have hsplit : ψ (w y) - ψ (w x₀) - (t • D) hv
          - 1 / 2 * (t • B + c • D.smulRight D) hv hv
        = (ψ (w x₀ + S) - ψ (w x₀) - t * S - 1 / 2 * c * S ^ 2)
          + t * (S - D hv - 1 / 2 * B hv hv)
          + 1 / 2 * c * (S ^ 2 - D hv ^ 2) := by
      rw [hDapp, hBapp, hψw, hS]
      ring
    show |ψ (w y) - ψ (w x₀) - (t • D) hv
        - 1 / 2 * (t • B + c • D.smulRight D) hv hv| ≤ ε * ‖hv‖ ^ 2
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    have htri := abs_add_le (ψ (w x₀ + S) - ψ (w x₀) - t * S - 1 / 2 * c * S ^ 2)
      (t * (S - D hv - 1 / 2 * B hv hv))
    linarith only [htri, hT1b, hT2b, hT3b]
  · rw [Lop, Lop, hgr, hhe, hN.A_homog t ξ₀ ht hg, hN.H_homog t ξ₀ ht hg,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, hXitr]
    field_simp
    ring
