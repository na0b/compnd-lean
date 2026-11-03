import CompND.MaxTranslate
import CompND.hgrad

/-- lem:envelope: at a point `h ∈ B_δ(0)` at which `M_δ` is Pansu differentiable with
horizontal differential `ξ`, every maximal point `x` of `u_h - v` over `Ω_δ` satisfies
`𝔛u(x * h) = ξ`; in particular all maximal points share the same horizontal gradient. -/
theorem EnvelopeIdentity (G : CarnotSetting)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (δ : ℝ) (hδ : 0 < δ)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hattain : ∀ g : EuclideanSpace ℝ (Fin G.n), G.hnorm g < δ →
      ∃ z ∈ TranslatedDomain G Ω δ,
        IsMaxOn (fun y => u (G.mul y g) - v y) (TranslatedDomain G Ω δ) z ∧
        MaxTranslate G Ω δ u v g = u (G.mul z g) - v z)
    (h : EuclideanSpace ℝ (Fin G.n)) (hh : G.hnorm h < δ)
    (ξ : EuclideanSpace ℝ (Fin G.m))
    (hpansu : HasPansuGradAt G.mul G.pi1 G.hnorm (MaxTranslate G Ω δ u v) h ξ)
    (x : EuclideanSpace ℝ (Fin G.n)) (hx : x ∈ TranslatedDomain G Ω δ)
    (hxmax : IsMaxOn (fun y => u (G.mul y h) - v y) (TranslatedDomain G Ω δ) x)
    (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ) (hD : HasFDerivAt u D (G.mul x h)) :
    hgrad G.sig (G.mul x h) D = ξ := by
  set ξ₀ : EuclideanSpace ℝ (Fin G.m) := hgrad G.sig (G.mul x h) D with hξ₀def
  -- "`|A| ≤ 2 ε c` for every `ε > 0` forces `A = 0`" (the end of Step 4)
  have hzero : ∀ A c : ℝ, 0 < c → (∀ ε : ℝ, 0 < ε → |A| ≤ 2 * ε * c) → A = 0 := by
    intro A c hc hb
    by_contra hA
    have hpos : 0 < |A| := abs_pos.2 hA
    have hcne : c ≠ 0 := ne_of_gt hc
    have hstep := hb (|A| / (4 * c)) (div_pos hpos (by linarith))
    have heq : 2 * (|A| / (4 * c)) * c = |A| / 2 := by
      field_simp
      ring
    rw [heq] at hstep
    linarith
  -- ===== Step 0: `M_δ(h) = u (x * h) - v x` =====
  obtain ⟨z, hz, hzmax, hzeq⟩ := hattain h hh
  have hM0 : MaxTranslate G Ω δ u v h = u (G.mul x h) - v x := by
    rw [hzeq]
    exact le_antisymm (isMaxOn_iff.1 hxmax z hz) (isMaxOn_iff.1 hzmax x hx)
  -- the Pansu expansion of `u` at `x * h`, from eq:taylor2
  have Pu : HasPansuGradAt G.mul G.pi1 G.hnorm u (G.mul x h) ξ₀ := by
    rw [hξ₀def]
    exact G.taylor2 u (G.mul x h) D hD
  -- `hexp 0 = 0`
  have hexp0 : G.hexp (0 : EuclideanSpace ℝ (Fin G.m)) = 0 := by
    refine (G.hnorm_eq_zero _).1 ?_
    rw [G.hnorm_hexp, norm_zero]
  -- ===== Steps 1-4: the horizontal differentials pair identically against every `ζ` =====
  have hkey : ∀ ζ : EuclideanSpace ℝ (Fin G.m), (∑ i, (ξ₀ i - ξ i) * ζ i) = 0 := by
    intro ζ
    rcases eq_or_ne ζ 0 with hζ0 | hζne
    · -- the trivial case `ζ = 0`, noted in Step 1
      subst hζ0
      refine Finset.sum_eq_zero fun i _ => ?_
      have hzi : ((0 : EuclideanSpace ℝ (Fin G.m)) i) = 0 := rfl
      rw [hzi, mul_zero]
    have hnζ : 0 < ‖ζ‖ := norm_pos_iff.mpr hζne
    have hζnn : ‖ζ‖ ≠ 0 := ne_of_gt hnζ
    -- Step 1: display (2).  Continuity only; no quasi-triangle inequality.
    have hcont : Continuous fun t : ℝ => G.hnorm (G.mul h (G.hexp (t • ζ))) := by
      have hc1 : Continuous fun t : ℝ => t • ζ := continuous_id.smul continuous_const
      have hc2 : Continuous fun t : ℝ => G.hexp (t • ζ) := G.hexp_cont.comp hc1
      have hc3 : Continuous fun t : ℝ => G.mul h (G.hexp (t • ζ)) :=
        G.mul_smooth.continuous.comp (continuous_const.prodMk hc2)
      exact G.hnorm_cont.comp hc3
    have hval0 : G.hnorm (G.mul h (G.hexp ((0 : ℝ) • ζ))) = G.hnorm h := by
      rw [zero_smul, hexp0, G.mul_zero]
    obtain ⟨t₁, ht₁, hball⟩ :=
      Metric.isOpen_iff.1 (isOpen_lt hcont continuous_const) 0
        (show G.hnorm (G.mul h (G.hexp ((0 : ℝ) • ζ))) < δ by rw [hval0]; exact hh)
    have hδball : ∀ t : ℝ, |t| < t₁ → G.hnorm (G.mul h (G.hexp (t • ζ))) < δ := by
      intro t ht
      refine hball ?_
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact ht
    -- Steps 2-4, at a fixed `ε`
    refine hzero _ _ hnζ ?_
    intro ε hε
    -- (3) and (4)
    obtain ⟨du, hdu, hu⟩ := Pu ε hε
    obtain ⟨dM, hdM, hM⟩ := hpansu ε hε
    obtain ⟨t₂, ht₂, ht₂a, ht₂b, ht₂c⟩ : ∃ t₂ : ℝ, 0 < t₂ ∧ t₂ ≤ t₁ ∧
        t₂ ≤ du / (2 * ‖ζ‖) ∧ t₂ ≤ dM / (2 * ‖ζ‖) :=
      ⟨min t₁ (min (du / (2 * ‖ζ‖)) (dM / (2 * ‖ζ‖))),
        lt_min ht₁ (lt_min (by positivity) (by positivity)),
        min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
        le_trans (min_le_right _ _) (min_le_right _ _)⟩
    -- display (8)
    have hstep8 : ∀ t : ℝ, |t| < t₂ →
        t * (∑ i, (ξ₀ i - ξ i) * ζ i) ≤ 2 * ε * (|t| * ‖ζ‖) := by
      intro t htlt
      have hng : G.hnorm (G.hexp (t • ζ)) = |t| * ‖ζ‖ := by
        rw [G.hnorm_hexp, norm_smul, Real.norm_eq_abs]
      have hpi : G.pi1 (G.hexp (t • ζ)) = t • ζ := G.pi1_hexp _
      have habs : 0 ≤ |t| := abs_nonneg t
      have hdiv : ∀ c : ℝ, 0 < c → t₂ ≤ c / (2 * ‖ζ‖) → G.hnorm (G.hexp (t • ζ)) < c := by
        intro c hc hle
        rw [hng]
        have h1 : |t| * ‖ζ‖ < c / (2 * ‖ζ‖) * ‖ζ‖ :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le htlt hle) hnζ
        have h2 : c / (2 * ‖ζ‖) * ‖ζ‖ = c / 2 := by
          field_simp
        rw [h2] at h1
        linarith
      have hgtdu : G.hnorm (G.hexp (t • ζ)) < du := hdiv du hdu ht₂b
      have hgtdM : G.hnorm (G.hexp (t • ζ)) < dM := hdiv dM hdM ht₂c
      have hhgt : G.hnorm (G.mul h (G.hexp (t • ζ))) < δ :=
        hδball t (lt_of_lt_of_le htlt ht₂a)
      -- display (5)
      obtain ⟨zt, hzt, hztmax, hzteq⟩ := hattain (G.mul h (G.hexp (t • ζ))) hhgt
      have h5 : u (G.mul (G.mul x h) (G.hexp (t • ζ))) - v x
          ≤ MaxTranslate G Ω δ u v (G.mul h (G.hexp (t • ζ))) := by
        rw [hzteq]
        have hmx := isMaxOn_iff.1 hztmax x hx
        rw [← G.mul_assoc x h (G.hexp (t • ζ))] at hmx
        exact hmx
      -- (3) at `g := g_t` and (4) at `g := g_t`
      have h3 := hu (G.hexp (t • ζ)) hgtdu
      have h4 := hM (G.hexp (t • ζ)) hgtdM
      rw [hng, hpi] at h3 h4
      rw [hM0] at h4
      obtain ⟨a1, -⟩ := abs_le.1 h3
      obtain ⟨-, b2⟩ := abs_le.1 h4
      -- the bridge from the two inner products to `t ⟪ξ₀ - ξ, ζ⟫`
      have hsumd : (∑ i, ξ₀ i * ((t • ζ : EuclideanSpace ℝ (Fin G.m)) i))
          - (∑ i, ξ i * ((t • ζ : EuclideanSpace ℝ (Fin G.m)) i))
          = t * (∑ i, (ξ₀ i - ξ i) * ζ i) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hsm : ((t • ζ : EuclideanSpace ℝ (Fin G.m)) i) = t * ζ i := rfl
        rw [hsm]
        ring
      -- (6) and (7)
      linarith
    -- Step 4: both signs of `t`
    have ht2h : 0 < t₂ / 2 := by linarith
    have habs2 : |t₂ / 2| = t₂ / 2 := abs_of_pos ht2h
    have hp := hstep8 (t₂ / 2) (by rw [habs2]; linarith)
    have hn := hstep8 (-(t₂ / 2)) (by rw [abs_neg, habs2]; linarith)
    rw [habs2] at hp
    rw [abs_neg, habs2] at hn
    have hp2 : (t₂ / 2) * (∑ i, (ξ₀ i - ξ i) * ζ i) ≤ (t₂ / 2) * (2 * ε * ‖ζ‖) := by
      refine le_trans hp (le_of_eq ?_)
      ring
    have hn2 : (t₂ / 2) * (-(∑ i, (ξ₀ i - ξ i) * ζ i)) ≤ (t₂ / 2) * (2 * ε * ‖ζ‖) := by
      refine le_trans (le_of_eq ?_) (le_trans hn (le_of_eq ?_))
      · ring
      · ring
    have hpS := le_of_mul_le_mul_left hp2 ht2h
    have hnS := le_of_mul_le_mul_left hn2 ht2h
    exact abs_le.2 ⟨by linarith, hpS⟩
  -- ===== Step 5: conclusion =====
  have hfin := hkey (ξ₀ - ξ)
  have hnormsq : ‖ξ₀ - ξ‖ ^ 2 = ∑ i, (ξ₀ i - ξ i) * ((ξ₀ - ξ : EuclideanSpace ℝ (Fin G.m)) i) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsub : ((ξ₀ - ξ : EuclideanSpace ℝ (Fin G.m)) i) = ξ₀ i - ξ i := rfl
    rw [Real.norm_eq_abs, sq_abs, hsub]
    ring
  have hsq : ‖ξ₀ - ξ‖ ^ 2 = 0 := by rw [hnormsq, hfin]
  have hn0 : ‖ξ₀ - ξ‖ = 0 := by
    have hnn := norm_nonneg (ξ₀ - ξ)
    nlinarith [hsq, hnn]
  exact eq_of_sub_eq_zero (norm_eq_zero.1 hn0)
