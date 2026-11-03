import CompND.SecondOrderJetCalculus

/-- A lower bound on the quadratic form of a second-order jet, from convexity. If
`y ↦ w y + Λ/2‖y‖²` is convex on a ball `B(x_c, r)` and `(D, B)` is a second-order jet of
`w` at a point `z` of that ball, then `B h h ≥ -Λ‖h‖²` for every `h`. This is the
pointwise-jet substitute for "a semi-convex function has Hessian bounded below", which
Mathlib does not carry in multidimensional form; it runs from midpoint convexity along
`z ± t h` together with the Peano estimate of `TwiceDiffAt`. -/
theorem JetHessianLowerBoundOfConvex {N : ℕ} (w : EuclideanSpace ℝ (Fin N) → ℝ) (Lam : ℝ)
    (xc : EuclideanSpace ℝ (Fin N)) (r : ℝ)
    (hconv : ConvexOn ℝ (Metric.ball xc r) (fun y => w y + Lam / 2 * ‖y‖ ^ 2))
    (zz : EuclideanSpace ℝ (Fin N)) (hzmem : zz ∈ Metric.ball xc r)
    (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hjet : TwiceDiffAt w zz D B) :
    ∀ h : EuclideanSpace ℝ (Fin N), -(Lam * ‖h‖ ^ 2) ≤ B h h := by
  obtain ⟨jetOfCubicBound, jetAdd, -, -, -⟩ := SecondOrderJetCalculus (N := N)
  -- the inner product as a continuous bilinear form; the type ascription is needed because
  -- bare `innerSL ℝ` elaborates as a conjugate-linear map and will not add to `B`
  obtain ⟨Bi, hBiapp⟩ : ∃ Bi : EuclideanSpace ℝ (Fin N) →L[ℝ]
      EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ, ∀ a b, Bi a b = (inner ℝ a b : ℝ) :=
    ⟨innerSL ℝ, fun _ _ => rfl⟩
  -- two scalar-extraction lemmas for `smul` on continuous linear and bilinear maps
  have hsmD : ∀ (c : ℝ) (T : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (a : EuclideanSpace ℝ (Fin N)), (c • T) a = c * T a := by
    intro c T a
    simp
  have hsmB : ∀ (c : ℝ) (Q : EuclideanSpace ℝ (Fin N) →L[ℝ]
        EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) (a b : EuclideanSpace ℝ (Fin N)),
      (c • Q) a b = c * Q a b := by
    intro c Q a b
    simp
  -- the cubic-remainder criterion applied to the quadratic `y ↦ Λ/2‖y‖²`, with `C = 0`
  -- because the second-order remainder of a quadratic vanishes identically
  have jetQuad : TwiceDiffAt (fun y => Lam / 2 * ‖y‖ ^ 2) zz (Lam • innerSL ℝ zz)
      (Lam • Bi) := by
    refine jetOfCubicBound _ zz (Lam • innerSL ℝ zz) (Lam • Bi) 0 (fun a b => ?_) le_rfl
      (fun y _ => ?_)
    · rw [hsmB, hsmB, hBiapp, hBiapp, real_inner_comm a b]
    · have hz : ‖y‖ ^ 2 = ‖zz‖ ^ 2 + 2 * (inner ℝ zz (y - zz) : ℝ) + ‖y - zz‖ ^ 2 := by
        have h1 := norm_add_sq_real zz (y - zz)
        rw [show zz + (y - zz) = y from by abel] at h1
        exact h1
      have hid : Lam / 2 * ‖y‖ ^ 2 - Lam / 2 * ‖zz‖ ^ 2
            - (Lam • innerSL ℝ zz) (y - zz)
            - 1 / 2 * (Lam • Bi) (y - zz) (y - zz) = 0 := by
        simp only [hsmD, hsmB, hBiapp, innerSL_apply_apply,
          real_inner_self_eq_norm_sq]
        rw [hz]
        ring
      show |Lam / 2 * ‖y‖ ^ 2 - Lam / 2 * ‖zz‖ ^ 2 - (Lam • innerSL ℝ zz) (y - zz)
          - 1 / 2 * (Lam • Bi) (y - zz) (y - zz)| ≤ 0 * ‖y - zz‖ ^ 3
      rw [hid]
      simp
  intro h
  have hjetg : TwiceDiffAt (fun y => w y + Lam / 2 * ‖y‖ ^ 2) zz
      (D + Lam • innerSL ℝ zz) (B + Lam • Bi) :=
    jetAdd w (fun y => Lam / 2 * ‖y‖ ^ 2) zz D (Lam • innerSL ℝ zz) B (Lam • Bi)
      hjet (jetQuad)
  have hBgapp : ∀ a b : EuclideanSpace ℝ (Fin N),
      (B + Lam • Bi) a b = B a b + Lam * (inner ℝ a b : ℝ) := by
    intro a b
    simp only [add_apply, hsmB, hBiapp]
  have hDl : ∀ s : ℝ, (D + Lam • innerSL ℝ zz) (s • h)
      = s * ((D + Lam • innerSL ℝ zz) h) := by
    intro s
    rw [map_smul, smul_eq_mul]
  have hBl : ∀ s : ℝ, (B + Lam • Bi) (s • h) (s • h)
      = s ^ 2 * ((B + Lam • Bi) h h) := by
    intro s
    have h1 : (B + Lam • Bi) (s • h) = s • ((B + Lam • Bi) h) := map_smul _ _ _
    rw [h1, smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hntsq : ∀ s : ℝ, ‖s • h‖ ^ 2 = s ^ 2 * ‖h‖ ^ 2 := by
    intro s
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have main : ∀ ε : ℝ, 0 < ε → 0 ≤ B h h + Lam * ‖h‖ ^ 2 + 2 * ε * ‖h‖ ^ 2 := by
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hjetg.2 ε hε
    have hzc : dist zz xc < r := Metric.mem_ball.1 hzmem
    have hh0 : (0:ℝ) < ‖h‖ + 1 := by positivity
    obtain ⟨t, htpos, htδ, htr⟩ : ∃ t : ℝ, 0 < t ∧ t * (‖h‖ + 1) < δ
        ∧ t * (‖h‖ + 1) < r - dist zz xc := by
      refine ⟨min (δ / (2 * (‖h‖ + 1))) ((r - dist zz xc) / (2 * (‖h‖ + 1))),
        lt_min (by positivity) (div_pos (by linarith only [hzc]) (by positivity)),
        ?_, ?_⟩
      · have h1 : min (δ / (2 * (‖h‖ + 1))) ((r - dist zz xc) / (2 * (‖h‖ + 1)))
            ≤ δ / (2 * (‖h‖ + 1)) := min_le_left _ _
        have h2 := mul_le_mul_of_nonneg_right h1 hh0.le
        have h3 : δ / (2 * (‖h‖ + 1)) * (‖h‖ + 1) = δ / 2 := by
          field_simp
        rw [h3] at h2
        linarith only [h2, hδ]
      · have h1 : min (δ / (2 * (‖h‖ + 1))) ((r - dist zz xc) / (2 * (‖h‖ + 1)))
            ≤ (r - dist zz xc) / (2 * (‖h‖ + 1)) := min_le_right _ _
        have h2 := mul_le_mul_of_nonneg_right h1 hh0.le
        have h3 : (r - dist zz xc) / (2 * (‖h‖ + 1)) * (‖h‖ + 1)
            = (r - dist zz xc) / 2 := by
          field_simp
        rw [h3] at h2
        linarith only [h2, hzc]
    have hnt : ‖t • h‖ = t * ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hth : t * ‖h‖ ≤ t * (‖h‖ + 1) := by
      have hx := mul_le_mul_of_nonneg_left (by linarith only [] : ‖h‖ ≤ ‖h‖ + 1) htpos.le
      linarith only [hx]
    have hmem1 : zz + t • h ∈ Metric.ball xc r := by
      rw [Metric.mem_ball]
      have h1 : dist (zz + t • h) xc ≤ dist (zz + t • h) zz + dist zz xc :=
        dist_triangle _ _ _
      have h2 : dist (zz + t • h) zz = t * ‖h‖ := by
        rw [dist_eq_norm, show zz + t • h - zz = t • h from by abel, hnt]
      linarith only [h1, h2, hth, htr]
    have hmem2 : zz - t • h ∈ Metric.ball xc r := by
      rw [Metric.mem_ball]
      have h1 : dist (zz - t • h) xc ≤ dist (zz - t • h) zz + dist zz xc :=
        dist_triangle _ _ _
      have h2 : dist (zz - t • h) zz = t * ‖h‖ := by
        rw [dist_eq_norm, show zz - t • h - zz = -(t • h) from by abel, norm_neg, hnt]
      linarith only [h1, h2, hth, htr]
    have hmid := hconv.2 hmem1 hmem2 (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
    rw [show (1 / 2 : ℝ) • (zz + t • h) + (1 / 2 : ℝ) • (zz - t • h) = zz from by
      module] at hmid
    have hmid' : w zz + Lam / 2 * ‖zz‖ ^ 2
        ≤ 1 / 2 * (w (zz + t • h) + Lam / 2 * ‖zz + t • h‖ ^ 2)
          + 1 / 2 * (w (zz - t • h) + Lam / 2 * ‖zz - t • h‖ ^ 2) := by
      simpa only [smul_eq_mul] using hmid
    have hy1 : ‖zz + t • h - zz‖ < δ := by
      rw [show zz + t • h - zz = t • h from by abel, hnt]
      linarith only [hth, htδ]
    have hy2 : ‖zz - t • h - zz‖ < δ := by
      rw [show zz - t • h - zz = -(t • h) from by abel, norm_neg, hnt]
      linarith only [hth, htδ]
    have hb1 := hb (zz + t • h) hy1
    have hb2 := hb (zz - t • h) hy2
    rw [show zz + t • h - zz = t • h from by module, hDl, hBl, hntsq] at hb1
    rw [show zz - t • h - zz = (-t) • h from by module, hDl, hBl, hntsq] at hb2
    have hb1' : |w (zz + t • h) + Lam / 2 * ‖zz + t • h‖ ^ 2
          - (w zz + Lam / 2 * ‖zz‖ ^ 2)
          - t * ((D + Lam • innerSL ℝ zz) h)
          - 1 / 2 * (t ^ 2 * ((B + Lam • Bi) h h))|
        ≤ ε * (t ^ 2 * ‖h‖ ^ 2) := hb1
    have hb2' : |w (zz - t • h) + Lam / 2 * ‖zz - t • h‖ ^ 2
          - (w zz + Lam / 2 * ‖zz‖ ^ 2)
          - -t * ((D + Lam • innerSL ℝ zz) h)
          - 1 / 2 * ((-t) ^ 2 * ((B + Lam • Bi) h h))|
        ≤ ε * ((-t) ^ 2 * ‖h‖ ^ 2) := hb2
    have ht2 : (0:ℝ) < t ^ 2 := by positivity
    have hA1 := abs_le.1 hb1'
    have hA2 := abs_le.1 hb2'
    have hfinal : 0 ≤ t ^ 2 * ((B + Lam • Bi) h h + 2 * ε * ‖h‖ ^ 2) := by
      linarith only [hmid', hA1.1, hA1.2, hA2.1, hA2.2]
    have hX : 0 ≤ (B + Lam • Bi) h h + 2 * ε * ‖h‖ ^ 2 := by
      by_contra hc
      push Not at hc
      nlinarith only [hfinal, hc, ht2]
    rw [hBgapp, real_inner_self_eq_norm_sq] at hX
    linarith only [hX]
  -- let `ε = 1/(n+1) → 0⁺` along the natural numbers
  have hlim : Filter.Tendsto
      (fun n : ℕ => -(Lam * ‖h‖ ^ 2) - 2 * (1 / (n + 1 : ℝ)) * ‖h‖ ^ 2)
      Filter.atTop (nhds (-(Lam * ‖h‖ ^ 2))) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using ((h0.const_mul (2:ℝ)).mul_const (‖h‖ ^ 2)).const_sub
      (-(Lam * ‖h‖ ^ 2))
  refine le_of_tendsto hlim ?_
  filter_upwards with n
  have hmn := main (1 / (n + 1 : ℝ)) (by positivity)
  linarith only [hmn]
