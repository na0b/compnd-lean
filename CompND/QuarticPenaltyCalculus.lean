import CompND.SecondOrderJetCalculus

/-- The calculus of the quartic penalty `P_{μ,c}(x) = μ‖x - c‖⁴` on `ℝᴺ`, for the penalty
and the two candidate differentials given by the formulas of its hypotheses: the second
differential is symmetric; the operator norms of the differentials are bounded by
`4μ‖x-c‖³` and `12μ‖x-c‖²`; the pair is a second-order jet of the penalty at every point;
the penalty vanishes at `c` and is positive elsewhere when `μ > 0`; the squared norm obeys
the parallelogram identity along a convex combination; and the convexity defect of the
penalty on a set where `‖x-c‖ ≤ R` is at most `6μR² t(1-t)‖x-y‖²`. -/
theorem QuarticPenaltyCalculus {N : ℕ}
    (Pf : ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) → ℝ)
    (DPf : ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →
      (EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ))
    (D2Pf : ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →
      (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ))
    (Bi : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hPf : ∀ (mu : ℝ) (c x : EuclideanSpace ℝ (Fin N)), Pf mu c x = mu * ‖x - c‖ ^ 4)
    (hDPf : ∀ (mu : ℝ) (c x : EuclideanSpace ℝ (Fin N)),
      DPf mu c x = (4 * mu * ‖x - c‖ ^ 2) • innerSL ℝ (x - c))
    (hBi : ∀ a b : EuclideanSpace ℝ (Fin N), Bi a b = (inner ℝ a b : ℝ))
    (hD2Pf : ∀ (mu : ℝ) (c x : EuclideanSpace ℝ (Fin N)),
      D2Pf mu c x = (4 * mu * ‖x - c‖ ^ 2) • Bi
        + (8 * mu) • ((innerSL ℝ (x - c)).smulRight (innerSL ℝ (x - c)))) :
    (∀ (mu : ℝ) (c x a b : EuclideanSpace ℝ (Fin N)),
      D2Pf mu c x a b = D2Pf mu c x b a) ∧
    (∀ mu : ℝ, 0 ≤ mu → ∀ c x : EuclideanSpace ℝ (Fin N),
      ‖DPf mu c x‖ ≤ 4 * mu * ‖x - c‖ ^ 3) ∧
    (∀ mu : ℝ, 0 ≤ mu → ∀ c x : EuclideanSpace ℝ (Fin N),
      ‖D2Pf mu c x‖ ≤ 12 * mu * ‖x - c‖ ^ 2) ∧
    (∀ mu : ℝ, 0 ≤ mu → ∀ c z : EuclideanSpace ℝ (Fin N),
      TwiceDiffAt (Pf mu c) z (DPf mu c z) (D2Pf mu c z)) ∧
    (∀ (mu : ℝ) (c : EuclideanSpace ℝ (Fin N)), Pf mu c c = 0) ∧
    (∀ mu : ℝ, 0 < mu → ∀ c x : EuclideanSpace ℝ (Fin N), x ≠ c → 0 < Pf mu c x) ∧
    (∀ (a b : EuclideanSpace ℝ (Fin N)) (t : ℝ),
      ‖t • a + (1 - t) • b‖ ^ 2
        = t * ‖a‖ ^ 2 + (1 - t) * ‖b‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2) ∧
    (∀ mu : ℝ, 0 ≤ mu → ∀ (c : EuclideanSpace ℝ (Fin N)) (R : ℝ), 0 ≤ R →
      ∀ x y : EuclideanSpace ℝ (Fin N), ‖x - c‖ ≤ R → ‖y - c‖ ≤ R →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * Pf mu c x + (1 - t) * Pf mu c y - Pf mu c (t • x + (1 - t) • y)
        ≤ 6 * mu * R ^ 2 * (t * (1 - t) * ‖x - y‖ ^ 2)) := by
  obtain ⟨jetOfCubicBound, -, -, -, -⟩ := SecondOrderJetCalculus (N := N)
  have hDPfapp : ∀ (mu : ℝ) (c x h : EuclideanSpace ℝ (Fin N)),
      DPf mu c x h = 4 * mu * ‖x - c‖ ^ 2 * (inner ℝ (x - c) h) := by
    intro mu c x h
    simp only [hDPf, smul_apply, smul_eq_mul, innerSL_apply_apply]
  have hD2Pfapp : ∀ (mu : ℝ) (c x h k : EuclideanSpace ℝ (Fin N)),
      D2Pf mu c x h k = 4 * mu * ‖x - c‖ ^ 2 * (inner ℝ h k)
        + 8 * mu * ((inner ℝ (x - c) h) * (inner ℝ (x - c) k)) := by
    intro mu c x h k
    simp only [hD2Pf, add_apply, smul_apply,
      smul_eq_mul, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hBi]
  have hD2Pfsymm : ∀ (mu : ℝ) (c x a b : EuclideanSpace ℝ (Fin N)),
      D2Pf mu c x a b = D2Pf mu c x b a := by
    intro mu c x a b
    rw [hD2Pfapp, hD2Pfapp, real_inner_comm a b]
    ring
  -- display (6): the two norm bounds, in the operator norm as the `.tex` requires
  have hDPfbound : ∀ mu : ℝ, 0 ≤ mu → ∀ c x : EuclideanSpace ℝ (Fin N),
      ‖DPf mu c x‖ ≤ 4 * mu * ‖x - c‖ ^ 3 := by
    intro mu hmu c x
    have hq : (0:ℝ) ≤ 4 * mu * ‖x - c‖ ^ 2 :=
      mul_nonneg (by linarith only [hmu]) (sq_nonneg _)
    refine (DPf mu c x).opNorm_le_bound
      (mul_nonneg (by linarith only [hmu]) (pow_nonneg (norm_nonneg _) 3)) fun h => ?_
    rw [Real.norm_eq_abs, hDPfapp, abs_mul, abs_of_nonneg hq]
    calc 4 * mu * ‖x - c‖ ^ 2 * |(inner ℝ (x - c) h : ℝ)|
        ≤ 4 * mu * ‖x - c‖ ^ 2 * (‖x - c‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hq
      _ = 4 * mu * ‖x - c‖ ^ 3 * ‖h‖ := by ring
  have hD2Pfbound : ∀ mu : ℝ, 0 ≤ mu → ∀ c x : EuclideanSpace ℝ (Fin N),
      ‖D2Pf mu c x‖ ≤ 12 * mu * ‖x - c‖ ^ 2 := by
    intro mu hmu c x
    have hq : (0:ℝ) ≤ 12 * mu * ‖x - c‖ ^ 2 :=
      mul_nonneg (by linarith only [hmu]) (sq_nonneg _)
    refine (D2Pf mu c x).opNorm_le_bound hq fun h => ?_
    refine (D2Pf mu c x h).opNorm_le_bound (mul_nonneg hq (norm_nonneg h)) fun k => ?_
    rw [Real.norm_eq_abs, hD2Pfapp]
    have h1 : |(inner ℝ h k : ℝ)| ≤ ‖h‖ * ‖k‖ := abs_real_inner_le_norm _ _
    have h2 : |(inner ℝ (x - c) h : ℝ)| ≤ ‖x - c‖ * ‖h‖ := abs_real_inner_le_norm _ _
    have h3 : |(inner ℝ (x - c) k : ℝ)| ≤ ‖x - c‖ * ‖k‖ := abs_real_inner_le_norm _ _
    have e1 : |4 * mu * ‖x - c‖ ^ 2 * (inner ℝ h k : ℝ)|
        ≤ 4 * mu * ‖x - c‖ ^ 2 * (‖h‖ * ‖k‖) := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by linarith only [hmu]) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left h1
        (mul_nonneg (by linarith only [hmu]) (sq_nonneg _))
    have e2 : |8 * mu * ((inner ℝ (x - c) h : ℝ) * (inner ℝ (x - c) k : ℝ))|
        ≤ 8 * mu * ((‖x - c‖ * ‖h‖) * (‖x - c‖ * ‖k‖)) := by
      rw [abs_mul, abs_of_nonneg (by linarith only [hmu] : (0:ℝ) ≤ 8 * mu), abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hmu])
      exact mul_le_mul h2 h3 (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    refine (abs_add_le _ _).trans ?_
    have hring : 4 * mu * ‖x - c‖ ^ 2 * (‖h‖ * ‖k‖)
        + 8 * mu * ((‖x - c‖ * ‖h‖) * (‖x - c‖ * ‖k‖))
        = 12 * mu * ‖x - c‖ ^ 2 * ‖h‖ * ‖k‖ := by ring
    linarith only [e1, e2, hring]
  -- the cubic remainder of `P`, hence its jet by (J1)
  have hPfrem : ∀ mu : ℝ, 0 ≤ mu → ∀ c z y : EuclideanSpace ℝ (Fin N), ‖y - z‖ ≤ 1 →
      |Pf mu c y - Pf mu c z - DPf mu c z (y - z)
          - 1 / 2 * D2Pf mu c z (y - z) (y - z)|
        ≤ (4 * mu * ‖z - c‖ + mu) * ‖y - z‖ ^ 3 := by
    intro mu hmu c z y hle
    have hN : (0:ℝ) ≤ ‖y - z‖ := norm_nonneg _
    have hsq : ‖y - c‖ ^ 2
        = ‖z - c‖ ^ 2 + 2 * (inner ℝ (z - c) (y - z)) + ‖y - z‖ ^ 2 := by
      rw [show y - c = (z - c) + (y - z) from by abel]
      exact norm_add_sq_real _ _
    have hrem : Pf mu c y - Pf mu c z - DPf mu c z (y - z)
          - 1 / 2 * D2Pf mu c z (y - z) (y - z)
        = mu * (4 * (inner ℝ (z - c) (y - z)) * ‖y - z‖ ^ 2 + ‖y - z‖ ^ 4) := by
      simp only [hPf]
      rw [hDPfapp, hD2Pfapp, real_inner_self_eq_norm_sq,
        show ‖y - c‖ ^ 4 = (‖y - c‖ ^ 2) ^ 2 from by ring, hsq]
      ring
    rw [hrem, abs_mul, abs_of_nonneg hmu]
    have h4 : ‖y - z‖ ^ 4 ≤ ‖y - z‖ ^ 3 := by
      nlinarith only [hle, hN, pow_nonneg hN 3]
    have e1 : |4 * (inner ℝ (z - c) (y - z) : ℝ) * ‖y - z‖ ^ 2|
        ≤ 4 * ‖z - c‖ * ‖y - z‖ ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
        abs_of_nonneg (sq_nonneg ‖y - z‖)]
      calc 4 * |(inner ℝ (z - c) (y - z) : ℝ)| * ‖y - z‖ ^ 2
          ≤ 4 * (‖z - c‖ * ‖y - z‖) * ‖y - z‖ ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _)
                (by norm_num : (0:ℝ) ≤ 4)) (sq_nonneg _)
        _ = 4 * ‖z - c‖ * ‖y - z‖ ^ 3 := by ring
    have hin : |4 * (inner ℝ (z - c) (y - z) : ℝ) * ‖y - z‖ ^ 2 + ‖y - z‖ ^ 4|
        ≤ 4 * ‖z - c‖ * ‖y - z‖ ^ 3 + ‖y - z‖ ^ 3 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖y - z‖ ^ 4)]
      linarith only [e1, h4]
    calc mu * |4 * (inner ℝ (z - c) (y - z) : ℝ) * ‖y - z‖ ^ 2 + ‖y - z‖ ^ 4|
        ≤ mu * (4 * ‖z - c‖ * ‖y - z‖ ^ 3 + ‖y - z‖ ^ 3) :=
          mul_le_mul_of_nonneg_left hin hmu
      _ = (4 * mu * ‖z - c‖ + mu) * ‖y - z‖ ^ 3 := by ring
  have hPfjet : ∀ mu : ℝ, 0 ≤ mu → ∀ c z : EuclideanSpace ℝ (Fin N),
      TwiceDiffAt (Pf mu c) z (DPf mu c z) (D2Pf mu c z) := fun mu hmu c z =>
    jetOfCubicBound (Pf mu c) z (DPf mu c z) (D2Pf mu c z) (4 * mu * ‖z - c‖ + mu)
      (hD2Pfsymm mu c z)
      (by
        have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hmu) (norm_nonneg (z - c))
        linarith only [this, hmu])
      (hPfrem mu hmu c z)
  have hPfzero : ∀ (mu : ℝ) (c : EuclideanSpace ℝ (Fin N)), Pf mu c c = 0 := by
    intro mu c; simp [hPf]
  have hPfpos : ∀ mu : ℝ, 0 < mu → ∀ c x : EuclideanSpace ℝ (Fin N), x ≠ c →
      0 < Pf mu c x := by
    intro mu hmu c x hne
    simp only [hPf]
    have : 0 < ‖x - c‖ := norm_pos_iff.2 (sub_ne_zero_of_ne hne)
    positivity
  -- (0b): a convexity-defect bound for `P` in chord form, which is what semi-convexity
  -- of `-P` needs.  The parallelogram identity for a convex combination.
  have hpara : ∀ (a b : EuclideanSpace ℝ (Fin N)) (t : ℝ),
      ‖t • a + (1 - t) • b‖ ^ 2
        = t * ‖a‖ ^ 2 + (1 - t) * ‖b‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2 := by
    intro a b t
    rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
      sq_abs, sq_abs]
    ring
  have hqchord : ∀ (c x y : EuclideanSpace ℝ (Fin N)) (t : ℝ),
      ‖t • x + (1 - t) • y - c‖ ^ 2
        = t * ‖x - c‖ ^ 2 + (1 - t) * ‖y - c‖ ^ 2 - t * (1 - t) * ‖x - y‖ ^ 2 := by
    intro c x y t
    rw [show t • x + (1 - t) • y - c = t • (x - c) + (1 - t) • (y - c) from by module,
      hpara, show x - c - (y - c) = x - y from by abel]
  -- the convexity defect of `P` on a set where `|x - c| ≤ R` is at most
  -- `6 μ R² t(1-t)|x-y|²`, i.e. `-P` is semi-convex there with constant `Λ = 12 μ R²`.
  have hPfdefect : ∀ mu : ℝ, 0 ≤ mu → ∀ (c : EuclideanSpace ℝ (Fin N)) (R : ℝ), 0 ≤ R →
      ∀ x y : EuclideanSpace ℝ (Fin N), ‖x - c‖ ≤ R → ‖y - c‖ ≤ R →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * Pf mu c x + (1 - t) * Pf mu c y - Pf mu c (t • x + (1 - t) • y)
        ≤ 6 * mu * R ^ 2 * (t * (1 - t) * ‖x - y‖ ^ 2) := by
    intro mu hmu c R hR x y hx hy t ht0 ht1
    have htt : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith only [ht1])
    have hd0 : 0 ≤ t * (1 - t) * ‖x - y‖ ^ 2 := mul_nonneg htt (sq_nonneg _)
    have haR : ‖x - c‖ ^ 2 ≤ R ^ 2 := by
      have h := norm_nonneg (x - c)
      nlinarith only [hx, h, hR]
    have hbR : ‖y - c‖ ^ 2 ≤ R ^ 2 := by
      have h := norm_nonneg (y - c)
      nlinarith only [hy, h, hR]
    have habs : |‖x - c‖ ^ 2 - ‖y - c‖ ^ 2| ≤ 2 * R * ‖x - y‖ := by
      have h1 : |‖x - c‖ - ‖y - c‖| ≤ ‖x - y‖ := by
        have h := abs_norm_sub_norm_le (x - c) (y - c)
        rwa [show x - c - (y - c) = x - y from by abel] at h
      have h2 : ‖x - c‖ + ‖y - c‖ ≤ 2 * R := by linarith only [hx, hy]
      have h3 : |‖x - c‖ ^ 2 - ‖y - c‖ ^ 2|
          = |‖x - c‖ - ‖y - c‖| * (‖x - c‖ + ‖y - c‖) := by
        rw [← abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖x - c‖ + ‖y - c‖), ← abs_mul]
        congr 1
        ring
      rw [h3]
      calc |‖x - c‖ - ‖y - c‖| * (‖x - c‖ + ‖y - c‖)
          ≤ ‖x - y‖ * (2 * R) :=
            mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
        _ = 2 * R * ‖x - y‖ := by ring
    have hsqd : (‖x - c‖ ^ 2 - ‖y - c‖ ^ 2) ^ 2 ≤ 4 * R ^ 2 * ‖x - y‖ ^ 2 := by
      have h5 := mul_self_le_mul_self (abs_nonneg (‖x - c‖ ^ 2 - ‖y - c‖ ^ 2)) habs
      rw [abs_mul_abs_self] at h5
      linarith only [h5]
    have hsle : t * ‖x - c‖ ^ 2 + (1 - t) * ‖y - c‖ ^ 2 ≤ R ^ 2 := by
      have e1 : t * ‖x - c‖ ^ 2 ≤ t * R ^ 2 := mul_le_mul_of_nonneg_left haR ht0
      have e2 : (1 - t) * ‖y - c‖ ^ 2 ≤ (1 - t) * R ^ 2 :=
        mul_le_mul_of_nonneg_left hbR (by linarith only [ht1])
      linarith only [e1, e2]
    have hterm1 : t * (1 - t) * (‖x - c‖ ^ 2 - ‖y - c‖ ^ 2) ^ 2
        ≤ 4 * R ^ 2 * (t * (1 - t) * ‖x - y‖ ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hsqd htt
      linarith only [h]
    have hterm2 : 2 * (t * ‖x - c‖ ^ 2 + (1 - t) * ‖y - c‖ ^ 2)
          * (t * (1 - t) * ‖x - y‖ ^ 2)
        ≤ 2 * R ^ 2 * (t * (1 - t) * ‖x - y‖ ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hsle hd0
      linarith only [h]
    have hterm3 : (0:ℝ) ≤ (t * (1 - t) * ‖x - y‖ ^ 2) ^ 2 := sq_nonneg _
    have hbig : t * (‖x - c‖ ^ 2) ^ 2 + (1 - t) * (‖y - c‖ ^ 2) ^ 2
        - (t * ‖x - c‖ ^ 2 + (1 - t) * ‖y - c‖ ^ 2 - t * (1 - t) * ‖x - y‖ ^ 2) ^ 2
        ≤ 6 * R ^ 2 * (t * (1 - t) * ‖x - y‖ ^ 2) := by
      have hid : t * (‖x - c‖ ^ 2) ^ 2 + (1 - t) * (‖y - c‖ ^ 2) ^ 2
          - (t * ‖x - c‖ ^ 2 + (1 - t) * ‖y - c‖ ^ 2 - t * (1 - t) * ‖x - y‖ ^ 2) ^ 2
          = t * (1 - t) * (‖x - c‖ ^ 2 - ‖y - c‖ ^ 2) ^ 2
            + 2 * (t * ‖x - c‖ ^ 2 + (1 - t) * ‖y - c‖ ^ 2)
              * (t * (1 - t) * ‖x - y‖ ^ 2)
            - (t * (1 - t) * ‖x - y‖ ^ 2) ^ 2 := by ring
      rw [hid]
      linarith only [hterm1, hterm2, hterm3]
    have hPx : Pf mu c x = mu * (‖x - c‖ ^ 2) ^ 2 := by simp only [hPf]; ring
    have hPy : Pf mu c y = mu * (‖y - c‖ ^ 2) ^ 2 := by simp only [hPf]; ring
    have hPz : Pf mu c (t • x + (1 - t) • y)
        = mu * (t * ‖x - c‖ ^ 2 + (1 - t) * ‖y - c‖ ^ 2
            - t * (1 - t) * ‖x - y‖ ^ 2) ^ 2 := by
      simp only [hPf]
      rw [show ‖t • x + (1 - t) • y - c‖ ^ 4
            = (‖t • x + (1 - t) • y - c‖ ^ 2) ^ 2 from by ring, hqchord]
    rw [hPx, hPy, hPz]
    have hfin := mul_le_mul_of_nonneg_left hbig hmu
    nlinarith only [hfin]
  exact ⟨hD2Pfsymm, hDPfbound, hD2Pfbound, hPfjet, hPfzero, hPfpos, hpara,
    hPfdefect⟩
