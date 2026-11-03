import CompND.TwiceDiffAt

/-- Descent of a second-order jet through the relabelling `ψ_λ(s) = s + λ e^s`: wherever the
relabelled function `ψ_λ ∘ u` has a second-order jet `(D_j, B_j)` at `z`, the function `u`
itself has the second-order jet `(t⁻¹ D_j, t⁻¹(B_j - c D_u ⊗ D_u))`, where
`t = ψ_λ'(u z) = 1 + λ e^{u z}` and `c = ψ_λ''(u z) = λ e^{u z}`. No inverse function
`ψ_λ⁻¹` and no separate first-order chain rule are needed: the first-order expansion of `u`
is bootstrapped out of the second-order estimate itself. -/
theorem ExpRelabellingJetDescent {N : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (u : EuclideanSpace ℝ (Fin N) → ℝ) (zz : EuclideanSpace ℝ (Fin N)) (t c : ℝ)
    (Dj : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (Bj : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (Du : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (Bu : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hteq : t = 1 + lam * Real.exp (u zz)) (hceq : c = lam * Real.exp (u zz))
    (hDuapp : ∀ h, Du h = t⁻¹ * Dj h)
    (hBuapp : ∀ h h', Bu h h' = t⁻¹ * (Bj h h' - c * (Du h * Du h')))
    (hBusymm : ∀ a b, Bu a b = Bu b a)
    (hjet : TwiceDiffAt (fun y => u y + lam * Real.exp (u y)) zz Dj Bj) :
    TwiceDiffAt u zz Du Bu := by
  -- name the relabelling `ψ_λ(s) = s + λ e^s`, so that the hypothesis reads as a jet of
  -- `ψ_λ ∘ u` and `hpsidef` serves as the unfolding lemma below
  obtain ⟨psi, hpsidef⟩ : ∃ psi : ℝ → ℝ, ∀ s, psi s = s + lam * Real.exp s :=
    ⟨fun s => s + lam * Real.exp s, fun _ => rfl⟩
  have hjet' : TwiceDiffAt (fun y => psi (u y)) zz Dj Bj := by
    have hfe : (fun y => psi (u y)) = fun y => u y + lam * Real.exp (u y) :=
      funext fun y => hpsidef (u y)
    rw [hfe]
    exact hjet
  -- `ψ_λ` is expanding, which converts the jet estimate for `ψ_λ ∘ u` into the crude
  -- Lipschitz bound `|u y - u z| ≤ L ‖y - z‖` used throughout
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
  -- the explicit cubic Taylor bound for the exponential, from `Real.exp_bound` at `n = 3`
  have hexpcube : ∀ s : ℝ, |s| ≤ 1 →
      |Real.exp s - (1 + s + s ^ 2 / 2)| ≤ |s| ^ 3 := by
    intro s hs
    have h := Real.exp_bound hs (n := 3) (by norm_num)
    have hsum : ∑ i ∈ Finset.range 3, s ^ i / (Nat.factorial i) = 1 + s + s ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at h
    refine h.trans ?_
    have h0 : (0:ℝ) ≤ |s| ^ 3 := by positivity
    have hcoef : ((Nat.succ 3 : ℝ) / (Nat.factorial 3 * 3)) ≤ 1 := by
      norm_num [Nat.factorial]
    calc |s| ^ 3 * ((Nat.succ 3 : ℝ) / (Nat.factorial 3 * 3)) ≤ |s| ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hcoef h0
      _ = |s| ^ 3 := by ring
  -- the second-order Taylor expansion of `ψ_λ` with an EXACT cubic remainder.  `ψ_λ` is an
  -- exponential, so Taylor's theorem with Peano remainder is not needed, and the cubic
  -- remainder is what turns the backward jet below into an `O(‖h‖³)` computation rather
  -- than a nested ε-δ argument.
  have hpsiTaylor : ∀ a s : ℝ, |s| ≤ 1 →
      |psi (a + s) - psi a - (1 + lam * Real.exp a) * s
          - 1 / 2 * (lam * Real.exp a) * s ^ 2|
        ≤ lam * Real.exp a * |s| ^ 3 := by
    intro a s hs
    have hid : psi (a + s) - psi a - (1 + lam * Real.exp a) * s
          - 1 / 2 * (lam * Real.exp a) * s ^ 2
        = lam * Real.exp a * (Real.exp s - (1 + s + s ^ 2 / 2)) := by
      simp only [hpsidef, Real.exp_add]
      ring
    rw [hid, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam * Real.exp a)]
    exact mul_le_mul_of_nonneg_left (hexpcube s hs) (by positivity)
  have hc0 : (0:ℝ) < c := by rw [hceq]; positivity
  have ht1 : (1:ℝ) ≤ t := by rw [hteq, ← hceq]; linarith only [hc0]
  have htpos : (0:ℝ) < t := by linarith only [ht1]
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have htinv0 : (0:ℝ) < t⁻¹ := by positivity
  have htinv1 : t⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left ht1 htinv0.le
    rw [inv_mul_cancel₀ ht0] at h
    linarith only [h]
  refine ⟨hBusymm, fun ε hε => ?_⟩
  obtain ⟨δ₁, hδ₁, hb₁⟩ := hjet'.2 1 one_pos
  obtain ⟨δ₂, hδ₂, hb₂⟩ := hjet'.2 (ε / 4) (by positivity)
  obtain ⟨L, hL1, hLb⟩ : ∃ L : ℝ, 1 ≤ L ∧ 1 + ‖Dj‖ + ‖Bj‖ ≤ L :=
    ⟨1 + ‖Dj‖ + ‖Bj‖, by linarith only [norm_nonneg Dj, norm_nonneg Bj], le_rfl⟩
  have hL0 : (0:ℝ) ≤ L := by linarith only [hL1]
  have hLpos : (0:ℝ) < L := by linarith only [hL1]
  have hcL3 : (0:ℝ) ≤ c * L ^ 3 := mul_nonneg hc0.le (pow_nonneg hL0 3)
  have hcL2 : (0:ℝ) ≤ c * L ^ 2 := mul_nonneg hc0.le (pow_nonneg hL0 2)
  obtain ⟨Q, hQ0, hQb⟩ : ∃ Q : ℝ, 0 ≤ Q ∧
      1 + c * L ^ 3 + c * L ^ 2 / 2 + ‖Bj‖ / 2 ≤ Q :=
    ⟨1 + c * L ^ 3 + c * L ^ 2 / 2 + ‖Bj‖ / 2,
      by linarith only [hcL3, hcL2, norm_nonneg Bj], le_rfl⟩
  obtain ⟨S, hS0, hSb⟩ : ∃ S : ℝ, 0 ≤ S ∧ c * L ^ 3 + c * Q * L ≤ S :=
    ⟨c * L ^ 3 + c * Q * L,
      by linarith only [hcL3, mul_nonneg (mul_nonneg hc0.le hQ0) hL0], le_rfl⟩
  have hSpos : (0:ℝ) < 2 * (S + 1) := by linarith only [hS0]
  refine ⟨min 1 (min δ₁ (min δ₂ (min (1 / L) (ε / (2 * (S + 1)))))),
    lt_min one_pos (lt_min hδ₁ (lt_min hδ₂
      (lt_min (div_pos one_pos hLpos) (div_pos hε hSpos)))),
    fun y hy => ?_⟩
  -- unpack the five radius constraints
  have hN1 : ‖y - zz‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hy (min_le_left _ _))
  have hNδ₁ : ‖y - zz‖ < δ₁ :=
    lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_left _ _))
  have hNδ₂ : ‖y - zz‖ < δ₂ :=
    lt_of_lt_of_le hy ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hNL : ‖y - zz‖ < 1 / L :=
    lt_of_lt_of_le hy ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hNS : ‖y - zz‖ < ε / (2 * (S + 1)) :=
    lt_of_lt_of_le hy ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hN0 : (0:ℝ) ≤ ‖y - zz‖ := norm_nonneg _
  have hNsq : ‖y - zz‖ ^ 2 ≤ ‖y - zz‖ := by nlinarith only [hN1, hN0]
  have hNcube : ‖y - zz‖ ^ 3 ≤ ‖y - zz‖ ^ 2 := by nlinarith only [hN1, hN0]
  -- the two operator-norm bounds
  have hDjb : |Dj (y - zz)| ≤ ‖Dj‖ * ‖y - zz‖ := by
    simpa [Real.norm_eq_abs] using Dj.le_opNorm (y - zz)
  have hBjb : |Bj (y - zz) (y - zz)| ≤ ‖Bj‖ * ‖y - zz‖ * ‖y - zz‖ := by
    have ha := (Bj (y - zz)).le_opNorm (y - zz)
    have hbb := Bj.le_opNorm (y - zz)
    rw [Real.norm_eq_abs] at ha
    exact ha.trans (mul_le_mul_of_nonneg_right hbb (norm_nonneg _))
  -- the crude bound `|u y - u z| ≤ L ‖y - z‖`, from `ψ_λ` expanding
  have hj1 := hb₁ y hNδ₁
  have hj2 := hb₂ y hNδ₂
  have habs3 : ∀ x1 x2 x3 : ℝ, |x1 + x2 + x3| ≤ |x1| + |x2| + |x3| := by
    intro x1 x2 x3
    linarith only [abs_add_le (x1 + x2) x3, abs_add_le x1 x2]
  have habs12 : |1 / 2 * (Bj (y - zz) (y - zz) : ℝ)|
      = 1 / 2 * |(Bj (y - zz) (y - zz) : ℝ)| := by
    rw [abs_mul]
    norm_num
  have hpsidiff : |psi (u y) - psi (u zz)|
      ≤ 1 * ‖y - zz‖ ^ 2 + |Dj (y - zz)| + |1 / 2 * (Bj (y - zz) (y - zz) : ℝ)| := by
    have h3 := habs3
      (psi (u y) - psi (u zz) - Dj (y - zz)
        - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
      (Dj (y - zz)) (1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
    rw [show psi (u y) - psi (u zz)
        = psi (u y) - psi (u zz) - Dj (y - zz)
            - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ)
          + Dj (y - zz) + 1 / 2 * (Bj (y - zz) (y - zz) : ℝ) from by ring]
    linarith only [h3, hj1]
  have hBjle : ‖Bj‖ * ‖y - zz‖ * ‖y - zz‖ ≤ ‖Bj‖ * ‖y - zz‖ := by
    have h := mul_le_mul_of_nonneg_left hN1 (mul_nonneg (norm_nonneg Bj) hN0)
    linarith only [h]
  have hDjL : ‖Dj‖ * ‖y - zz‖ ≤ L * ‖y - zz‖ := by
    have h := mul_le_mul_of_nonneg_right
      (by linarith only [hLb, norm_nonneg Bj] : ‖Dj‖ ≤ L) hN0
    linarith only [h]
  have hcrude : |u y - u zz| ≤ L * ‖y - zz‖ := by
    have he := hexpand (u y) (u zz)
    have hsum : 1 * ‖y - zz‖ ^ 2 + |Dj (y - zz)|
          + |1 / 2 * (Bj (y - zz) (y - zz) : ℝ)|
        ≤ L * ‖y - zz‖ := by
      rw [habs12]
      have hD : ‖Dj‖ * ‖y - zz‖ + ‖Bj‖ * ‖y - zz‖ + ‖y - zz‖ ≤ L * ‖y - zz‖ := by
        have h := mul_le_mul_of_nonneg_right hLb hN0
        linarith only [h]
      linarith only [hDjb, hBjb, hBjle, hNsq, hD,
        mul_nonneg (norm_nonneg Bj) hN0]
    linarith only [he, hpsidiff, hsum]
  have hs1 : |u y - u zz| ≤ 1 := by
    have h1 : L * ‖y - zz‖ < L * (1 / L) := mul_lt_mul_of_pos_left hNL hLpos
    rw [mul_one_div, div_self (ne_of_gt hLpos)] at h1
    linarith only [hcrude, h1]
  -- the Taylor expansion of `ψ_λ` at `u z`, in the variables `t` and `c`
  have htay := hpsiTaylor (u zz) (u y - u zz) hs1
  rw [show u zz + (u y - u zz) = u y from by ring, ← hteq, ← hceq] at htay
  have hcube : |u y - u zz| ^ 3 ≤ L ^ 3 * ‖y - zz‖ ^ 3 := by
    have ha : (0:ℝ) ≤ |u y - u zz| := abs_nonneg _
    have hb : (0:ℝ) ≤ L * ‖y - zz‖ := mul_nonneg hL0 hN0
    calc |u y - u zz| ^ 3 = |u y - u zz| * |u y - u zz| * |u y - u zz| := by ring
      _ ≤ L * ‖y - zz‖ * (L * ‖y - zz‖) * (L * ‖y - zz‖) :=
          mul_le_mul (mul_le_mul hcrude hcrude ha hb) hcrude ha
            (mul_nonneg hb hb)
      _ = L ^ 3 * ‖y - zz‖ ^ 3 := by ring
  have htaycube : |psi (u y) - psi (u zz) - t * (u y - u zz)
        - 1 / 2 * c * (u y - u zz) ^ 2|
      ≤ c * L ^ 3 * ‖y - zz‖ ^ 3 := by
    refine htay.trans ?_
    have h := mul_le_mul_of_nonneg_left hcube hc0.le
    linarith only [h]
  -- the central combination: `|t s + ½ c s² - Dⱼh - ½ Bⱼ(h,h)|`
  have hidkey : t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2
        - Dj (y - zz) - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ)
      = -(psi (u y) - psi (u zz) - t * (u y - u zz)
            - 1 / 2 * c * (u y - u zz) ^ 2)
        + (psi (u y) - psi (u zz) - Dj (y - zz)
            - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ)) := by ring
  have hkey1 : |t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2
        - Dj (y - zz) - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ)|
      ≤ (1 + c * L ^ 3) * ‖y - zz‖ ^ 2 := by
    rw [hidkey]
    have h := abs_add_le
      (-(psi (u y) - psi (u zz) - t * (u y - u zz)
          - 1 / 2 * c * (u y - u zz) ^ 2))
      (psi (u y) - psi (u zz) - Dj (y - zz)
        - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
    rw [abs_neg] at h
    have hcc := mul_le_mul_of_nonneg_left hNcube hcL3
    linarith only [h, htaycube, hj1, hcc]
  have hkey2 : |t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2
        - Dj (y - zz) - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ)|
      ≤ ε / 4 * ‖y - zz‖ ^ 2 + c * L ^ 3 * ‖y - zz‖ ^ 3 := by
    rw [hidkey]
    have h := abs_add_le
      (-(psi (u y) - psi (u zz) - t * (u y - u zz)
          - 1 / 2 * c * (u y - u zz) ^ 2))
      (psi (u y) - psi (u zz) - Dj (y - zz)
        - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
    rw [abs_neg] at h
    linarith only [h, htaycube, hj2]
  -- the bootstrap: `|s - Dᵘ h| ≤ Q ‖h‖²`
  have hssq : (u y - u zz) ^ 2 ≤ L ^ 2 * ‖y - zz‖ ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (u y - u zz)) hcrude
    rw [abs_mul_abs_self] at h
    linarith only [h]
  have hboot : |(u y - u zz) - t⁻¹ * Dj (y - zz)| ≤ Q * ‖y - zz‖ ^ 2 := by
    have hA : |t * (u y - u zz) - Dj (y - zz)|
        ≤ (1 + c * L ^ 3 + c * L ^ 2 / 2 + ‖Bj‖ / 2) * ‖y - zz‖ ^ 2 := by
      have h := habs3 (t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2
            - Dj (y - zz) - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
        (-(1 / 2 * c * (u y - u zz) ^ 2)) (1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
      rw [show t * (u y - u zz) - Dj (y - zz)
          = t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2 - Dj (y - zz)
              - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ)
            + -(1 / 2 * c * (u y - u zz) ^ 2)
            + 1 / 2 * (Bj (y - zz) (y - zz) : ℝ) from by ring]
      have habsc : |-(1 / 2 * c * (u y - u zz) ^ 2)| = 1 / 2 * c * (u y - u zz) ^ 2 := by
        rw [abs_neg, abs_of_nonneg (by positivity)]
      have hcs := mul_le_mul_of_nonneg_left hssq (by linarith only [hc0] : (0:ℝ) ≤ c / 2)
      linarith only [h, hkey1, habsc, habs12, hBjb, hBjle, hcs]
    have hrw : (u y - u zz) - t⁻¹ * Dj (y - zz)
        = t⁻¹ * (t * (u y - u zz) - Dj (y - zz)) := by
      field_simp
    rw [hrw, abs_mul, abs_of_pos htinv0]
    have h1 : t⁻¹ * |t * (u y - u zz) - Dj (y - zz)|
        ≤ 1 * |t * (u y - u zz) - Dj (y - zz)| :=
      mul_le_mul_of_nonneg_right htinv1 (abs_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right hQb (sq_nonneg ‖y - zz‖)
    linarith only [h1, hA, h2]
  -- `|(Dᵘ h)² - s²| ≤ 2 Q L ‖h‖³`
  have hDub : |t⁻¹ * Dj (y - zz)| ≤ L * ‖y - zz‖ := by
    rw [abs_mul, abs_of_pos htinv0]
    have h1 : t⁻¹ * |Dj (y - zz)| ≤ 1 * |Dj (y - zz)| :=
      mul_le_mul_of_nonneg_right htinv1 (abs_nonneg _)
    linarith only [h1, hDjb, hDjL]
  have hsqdiff : |(t⁻¹ * Dj (y - zz)) ^ 2 - (u y - u zz) ^ 2|
      ≤ 2 * Q * L * ‖y - zz‖ ^ 3 := by
    have hid : (t⁻¹ * Dj (y - zz)) ^ 2 - (u y - u zz) ^ 2
        = -(((u y - u zz) - t⁻¹ * Dj (y - zz))
            * ((u y - u zz) + t⁻¹ * Dj (y - zz))) := by ring
    rw [hid, abs_neg, abs_mul]
    have hsum : |(u y - u zz) + t⁻¹ * Dj (y - zz)| ≤ 2 * L * ‖y - zz‖ := by
      have h := abs_add_le (u y - u zz) (t⁻¹ * Dj (y - zz))
      linarith only [h, hcrude, hDub]
    have hfin : |(u y - u zz) - t⁻¹ * Dj (y - zz)|
          * |(u y - u zz) + t⁻¹ * Dj (y - zz)|
        ≤ Q * ‖y - zz‖ ^ 2 * (2 * L * ‖y - zz‖) :=
      mul_le_mul hboot hsum (abs_nonneg _)
        (mul_nonneg hQ0 (sq_nonneg ‖y - zz‖))
    calc |(u y - u zz) - t⁻¹ * Dj (y - zz)| * |(u y - u zz) + t⁻¹ * Dj (y - zz)|
        ≤ Q * ‖y - zz‖ ^ 2 * (2 * L * ‖y - zz‖) := hfin
      _ = 2 * Q * L * ‖y - zz‖ ^ 3 := by ring
  -- assemble
  rw [hBuapp, hDuapp]
  have hidfin : ∀ dj bj : ℝ,
      u y - u zz - t⁻¹ * dj - 1 / 2 * (t⁻¹ * (bj - c * (t⁻¹ * dj * (t⁻¹ * dj))))
        = t⁻¹ * ((t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2 - dj - 1 / 2 * bj)
            + 1 / 2 * c * ((t⁻¹ * dj) ^ 2 - (u y - u zz) ^ 2)) := by
    intro dj bj
    field_simp
    ring
  rw [hidfin, abs_mul, abs_of_pos htinv0]
  have hbr : |(t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2
          - Dj (y - zz) - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
        + 1 / 2 * c * ((t⁻¹ * Dj (y - zz)) ^ 2 - (u y - u zz) ^ 2)|
      ≤ ε / 4 * ‖y - zz‖ ^ 2 + (c * L ^ 3 + c * Q * L) * ‖y - zz‖ ^ 3 := by
    have h := abs_add_le
      (t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2
        - Dj (y - zz) - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
      (1 / 2 * c * ((t⁻¹ * Dj (y - zz)) ^ 2 - (u y - u zz) ^ 2))
    have h2 : |1 / 2 * c * ((t⁻¹ * Dj (y - zz)) ^ 2 - (u y - u zz) ^ 2)|
        = 1 / 2 * c * |(t⁻¹ * Dj (y - zz)) ^ 2 - (u y - u zz) ^ 2| := by
      rw [abs_mul, abs_of_nonneg (by linarith only [hc0] : (0:ℝ) ≤ 1 / 2 * c)]
    have h3 := mul_le_mul_of_nonneg_left hsqdiff
      (by linarith only [hc0] : (0:ℝ) ≤ 1 / 2 * c)
    linarith only [h, hkey2, h2, h3]
  have hSN : (c * L ^ 3 + c * Q * L) * ‖y - zz‖ ^ 3 ≤ ε / 2 * ‖y - zz‖ ^ 2 := by
    have hSL : (c * L ^ 3 + c * Q * L) * ‖y - zz‖ ^ 3 ≤ S * ‖y - zz‖ ^ 3 :=
      mul_le_mul_of_nonneg_right hSb (pow_nonneg hN0 3)
    have hSn : S * ‖y - zz‖ ≤ ε / 2 := by
      have h1 : S * ‖y - zz‖ ≤ S * (ε / (2 * (S + 1))) :=
        mul_le_mul_of_nonneg_left hNS.le hS0
      have h2 : S * (ε / (2 * (S + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ hSpos (by norm_num : (0:ℝ) < 2)]
        nlinarith only [hS0, hε.le]
      linarith only [h1, h2]
    have h3 : S * ‖y - zz‖ * ‖y - zz‖ ^ 2 ≤ ε / 2 * ‖y - zz‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hSn (sq_nonneg ‖y - zz‖)
    calc (c * L ^ 3 + c * Q * L) * ‖y - zz‖ ^ 3 ≤ S * ‖y - zz‖ ^ 3 := hSL
      _ = S * ‖y - zz‖ * ‖y - zz‖ ^ 2 := by ring
      _ ≤ ε / 2 * ‖y - zz‖ ^ 2 := h3
  have hlast : t⁻¹ * |(t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2
          - Dj (y - zz) - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
        + 1 / 2 * c * ((t⁻¹ * Dj (y - zz)) ^ 2 - (u y - u zz) ^ 2)|
      ≤ 1 * |(t * (u y - u zz) + 1 / 2 * c * (u y - u zz) ^ 2
          - Dj (y - zz) - 1 / 2 * (Bj (y - zz) (y - zz) : ℝ))
        + 1 / 2 * c * ((t⁻¹ * Dj (y - zz)) ^ 2 - (u y - u zz) ^ 2)| :=
    mul_le_mul_of_nonneg_right htinv1 (abs_nonneg _)
  linarith only [hlast, hbr, hSN, mul_nonneg hε.le (sq_nonneg ‖y - zz‖)]
