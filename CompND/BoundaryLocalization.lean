import CompND.InnerDomainProperties
import CompND.MaxTranslate

/-- lem:bdry, with the quasi-triangle constant of eq:trinangle carried explicitly: under the
standing assumptions eq:bdtau-eq:rho0 there is `c' ≥ 1` such that, with
`ρ₁ = ρ₀/(2c')` and `ρ₂ = δ₁ = ρ₀/(4c'²)`, (a) `E ⊆ K_{ρ₀}` with `M_δ(0) = M₀` and
`A_δ(0) = E`, (b) `u_h - v ≤ -τ/2` on `Ω_δ \ K_{ρ₁}`, and (c) `M_δ(h) ≥ M₀ - τ/4`, the
supremum is attained, and `A_δ(h) ⊆ K_{ρ₁}` with `A_δ(h) * h ⊆ K_{ρ₂}`. -/
theorem BoundaryLocalization (G : CarnotSetting)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (ωu ωv : ℝ → ℝ)
    (hωumono : ∀ s t : ℝ, s ≤ t → ωu s ≤ ωu t)
    (hωvmono : ∀ s t : ℝ, s ≤ t → ωv s ≤ ωv t)
    (hωu : ∀ a ∈ closure Ω, ∀ b ∈ closure Ω, |u a - u b| ≤ ωu (G.hnorm (G.mul (-b) a)))
    (hωv : ∀ a ∈ closure Ω, ∀ b ∈ closure Ω, |v a - v b| ≤ ωv (G.hnorm (G.mul (-b) a)))
    (τ : ℝ) (hτ : 0 < τ)
    (hbdry : ∀ z ∈ frontier Ω, u z - v z ≤ -τ)
    (xM : EuclideanSpace ℝ (Fin G.n)) (hxM : xM ∈ closure Ω)
    (hxMmax : IsMaxOn (fun y => u y - v y) (closure Ω) xM)
    (hM0 : τ ≤ u xM - v xM)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (hmod : ωu ρ₀ + ωv ρ₀ ≤ τ / 4) :
    ∃ c' : ℝ, 1 ≤ c' ∧
      ∀ ρ₁ ρ₂ δ₁ : ℝ, ρ₁ = ρ₀ / (2 * c') → ρ₂ = ρ₀ / (4 * c' ^ 2) →
        δ₁ = ρ₀ / (4 * c' ^ 2) →
      ({y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} ⊆ BoundaryCore G Ω ρ₀) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
        MaxTranslate G Ω δ u v 0 = u xM - v xM ∧
        {x ∈ TranslatedDomain G Ω δ |
            IsMaxOn (fun y => u (G.mul y 0) - v y) (TranslatedDomain G Ω δ) x}
          = {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} ∧
        (∀ x ∈ BoundaryCore G Ω ρ₁, ∀ g : EuclideanSpace ℝ (Fin G.n),
          G.hnorm g < δ → G.mul x g ∈ BoundaryCore G Ω ρ₂) ∧
        ∀ h : EuclideanSpace ℝ (Fin G.n), G.hnorm h < δ →
          (∀ x ∈ TranslatedDomain G Ω δ, x ∉ BoundaryCore G Ω ρ₁ →
            u (G.mul x h) - v x ≤ -(τ / 2)) ∧
          (u xM - v xM - τ / 4 ≤ MaxTranslate G Ω δ u v h) ∧
          (∃ x ∈ TranslatedDomain G Ω δ,
            IsMaxOn (fun y => u (G.mul y h) - v y) (TranslatedDomain G Ω δ) x ∧
            MaxTranslate G Ω δ u v h = u (G.mul x h) - v x) ∧
          (∀ x ∈ TranslatedDomain G Ω δ,
            IsMaxOn (fun y => u (G.mul y h) - v y) (TranslatedDomain G Ω δ) x →
              x ∈ BoundaryCore G Ω ρ₁ ∧ G.mul x h ∈ BoundaryCore G Ω ρ₂)) := by
  -- ===== Step 0: preliminaries =====
  have hΩcl : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩbdd.closure
  have hclne : (closure Ω).Nonempty := ⟨xM, hxM⟩
  have hfr : frontier Ω = closure Ω \ Ω := hΩopen.frontier_eq
  have hd0 : ∀ x : EuclideanSpace ℝ (Fin G.n), G.hnorm (G.mul (-x) x) = 0 := by
    intro x
    rw [G.neg_mul]
    exact (G.hnorm_eq_zero 0).2 rfl
  have hωu0 : 0 ≤ ωu 0 := by
    have h := hωu xM hxM xM hxM
    rw [hd0 xM] at h
    exact le_trans (abs_nonneg _) h
  have hωv0 : 0 ≤ ωv 0 := by
    have h := hωv xM hxM xM hxM
    rw [hd0 xM] at h
    exact le_trans (abs_nonneg _) h
  have hωunn : ∀ s : ℝ, 0 ≤ s → 0 ≤ ωu s := fun s hs => le_trans hωu0 (hωumono 0 s hs)
  have hωvnn : ∀ s : ℝ, 0 ≤ s → 0 ≤ ωv s := fun s hs => le_trans hωv0 (hωvmono 0 s hs)
  -- (1)
  have hωv4 : ∀ s : ℝ, 0 ≤ s → s ≤ ρ₀ → ωv s ≤ τ / 4 := by
    intro s _ hsle
    have h1 := hωvmono s ρ₀ hsle
    have h2 := hωunn ρ₀ hρ₀.le
    linarith
  have hsum4 : ∀ s : ℝ, s ≤ ρ₀ → ωu s + ωv s ≤ τ / 4 := by
    intro s hsle
    have h1 := hωumono s ρ₀ hsle
    have h2 := hωvmono s ρ₀ hsle
    linarith
  have hub : ∀ z ∈ closure Ω, u z - v z ≤ u xM - v xM := fun z hz => isMaxOn_iff.1 hxMmax z hz
  have hxMΩ : xM ∈ Ω := by
    by_contra hc
    have hf : xM ∈ frontier Ω := by rw [hfr]; exact ⟨hxM, hc⟩
    have := hbdry xM hf
    linarith
  -- (2): the maximal set `E` described by the value of `u - v`
  have hEmem : ∀ y : EuclideanSpace ℝ (Fin G.n),
      y ∈ ({y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} :
        Set (EuclideanSpace ℝ (Fin G.n))) ↔ (y ∈ Ω ∧ u y - v y = u xM - v xM) := by
    intro y
    constructor
    · intro hy
      exact ⟨hy.1, le_antisymm (hub y (subset_closure hy.1)) (isMaxOn_iff.1 hy.2 xM hxM)⟩
    · intro hy
      refine ⟨hy.1, isMaxOn_iff.2 ?_⟩
      intro z hz
      show u z - v z ≤ u y - v y
      rw [hy.2]
      exact hub z hz
  have hxME : xM ∈ ({y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} :
      Set (EuclideanSpace ℝ (Fin G.n))) := (hEmem xM).2 ⟨hxMΩ, rfl⟩
  -- ===== Step 2: the boundary estimate (5) =====
  have hstep2 : ∀ z ∈ closure Ω, ∀ y ∈ frontier Ω,
      G.hnorm (G.mul (-y) z) ≤ ρ₀ → u z - v z ≤ -(3 * τ / 4) := by
    intro z hz y hy hdle
    have hyc : y ∈ closure Ω := by rw [hfr] at hy; exact hy.1
    have h1 : u z - u y ≤ ωu (G.hnorm (G.mul (-y) z)) :=
      le_trans (le_abs_self _) (hωu z hz y hyc)
    have h2 : -(ωv (G.hnorm (G.mul (-y) z))) ≤ v z - v y := (abs_le.1 (hωv z hz y hyc)).1
    have h3 := hbdry y hy
    have h4 := hsum4 _ hdle
    linarith
  -- the geometry of the inner domains
  obtain ⟨hidp1, hidp2, -, hidp4, hidp5, hidp6, hidp7⟩ :=
    InnerDomainProperties G Ω hΩopen hΩbdd
  -- ===== Step 3, first half: part (a), `E ⊆ K_{ρ₀}`.  No triangle inequality is used. =====
  have hEK : ({y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} :
      Set (EuclideanSpace ℝ (Fin G.n))) ⊆ BoundaryCore G Ω ρ₀ := by
    intro y hy
    obtain ⟨hyΩ, hyval⟩ := (hEmem y).1 hy
    refine ⟨hyΩ, ?_⟩
    intro y' hy'
    by_contra hcon
    push Not at hcon
    have := hstep2 y (subset_closure hyΩ) y' hy' hcon.le
    linarith
  -- eq:righttrans, kept inline by pm-0012
  have hrt : ∀ x g : EuclideanSpace ℝ (Fin G.n),
      G.hnorm (G.mul (-x) (G.mul x g)) = G.hnorm g := by
    intro x g
    rw [← G.mul_assoc, G.neg_mul, G.zero_mul]
  have hcanc : ∀ y h : EuclideanSpace ℝ (Fin G.n), G.mul (G.mul y (-h)) h = y := by
    intro y h
    rw [G.mul_assoc, G.neg_mul, G.mul_zero]
  have hcanc2 : ∀ x h : EuclideanSpace ℝ (Fin G.n), G.mul (G.mul x h) (-h) = x := by
    intro x h
    rw [G.mul_assoc, G.mul_neg, G.mul_zero]
  -- (4′)
  have htrans4 : ∀ δ : ℝ, 0 < δ → ∀ x ∈ TranslatedDomain G Ω δ,
      ∀ g : EuclideanSpace ℝ (Fin G.n), G.hnorm g < δ → G.mul x g ∈ Ω := by
    intro δ hδ x hx g hg
    refine hidp6 δ hδ x hx ?_
    show G.hnorm (G.mul (-x) (G.mul x g)) < δ
    rw [hrt]
    exact hg
  -- ===== Step 1: the scale `ν` and the constant `c'` =====
  have hdjoint : Continuous (Function.uncurry
      fun (x y : EuclideanSpace ℝ (Fin G.n)) => G.hnorm (G.mul (-y) x)) := by
    apply G.hnorm_cont.comp
    exact G.mul_smooth.continuous.comp (continuous_snd.neg.prodMk continuous_fst)
  obtain ⟨c', hc'1, nu, hρ₀ν, hdν, htri⟩ :
      ∃ c' : ℝ, 1 ≤ c' ∧ ∃ nu : ℝ, ρ₀ < nu ∧
        (∀ z ∈ closure Ω, ∀ w ∈ closure Ω, G.hnorm (G.mul (-w) z) < nu) ∧
        (∀ a b : EuclideanSpace ℝ (Fin G.n), G.hnorm a < nu → G.hnorm b < nu →
          G.hnorm (G.mul a b) ≤ c' * (G.hnorm a + G.hnorm b)) := by
    obtain ⟨p, -, hpmax⟩ :=
      (hΩcl.prod hΩcl).exists_isMaxOn (hclne.prod hclne) hdjoint.continuousOn
    obtain ⟨Δ, hΔdef⟩ : ∃ D : ℝ, D = G.hnorm (G.mul (-p.2) p.1) := ⟨_, rfl⟩
    have hΔnn : 0 ≤ Δ := by rw [hΔdef]; exact G.hnorm_nonneg _
    have hΔmax : ∀ z ∈ closure Ω, ∀ w ∈ closure Ω, G.hnorm (G.mul (-w) z) ≤ Δ := by
      intro z hz w hw
      have h := isMaxOn_iff.1 hpmax (z, w) (Set.mk_mem_prod hz hw)
      rw [hΔdef]
      exact h
    have hnupos : (0:ℝ) < Δ + ρ₀ + 1 := by linarith
    obtain ⟨cG, -, hcG⟩ := G.hnorm_mul_le (Δ + ρ₀ + 1) hnupos
    refine ⟨max cG 1, le_max_right _ _, Δ + ρ₀ + 1, by linarith, ?_, ?_⟩
    · intro z hz w hw
      have := hΔmax z hz w hw
      linarith
    · -- display (3)
      intro a b ha hb
      refine le_trans (hcG a b ha hb) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (add_nonneg (G.hnorm_nonneg _) (G.hnorm_nonneg _))
  -- display (4): the arithmetic spine
  have hc'pos : (0:ℝ) < c' := lt_of_lt_of_le one_pos hc'1
  have h2cpos : (0:ℝ) < 2 * c' := by linarith
  have hcsq : c' ≤ c' ^ 2 := by nlinarith [mul_nonneg hc'pos.le (sub_nonneg.2 hc'1)]
  have h4cpos : (0:ℝ) < 4 * c' ^ 2 := by linarith
  have hρ₁pos : 0 < ρ₀ / (2 * c') := div_pos hρ₀ h2cpos
  have hρ₂pos : 0 < ρ₀ / (4 * c' ^ 2) := div_pos hρ₀ h4cpos
  have hρ₁le : ρ₀ / (2 * c') ≤ ρ₀ / 2 :=
    div_le_div_of_nonneg_left hρ₀.le (by norm_num) (by linarith)
  have hρ₂ltρ₁ : ρ₀ / (4 * c' ^ 2) < ρ₀ / (2 * c') :=
    div_lt_div_of_pos_left hρ₀ h2cpos (by linarith)
  have hρ₁ltρ₀ : ρ₀ / (2 * c') < ρ₀ := by linarith
  have hρ₂ltρ₀ : ρ₀ / (4 * c' ^ 2) < ρ₀ := lt_trans hρ₂ltρ₁ hρ₁ltρ₀
  -- display (9)
  have harith9 : ∀ a b : ℝ, a < ρ₀ / (2 * c') → b < ρ₀ / (4 * c' ^ 2) →
      c' * (a + b) < ρ₀ := by
    intro a b ha hb
    have h1 : c' * (a + b) < c' * (ρ₀ / (2 * c') + ρ₀ / (4 * c' ^ 2)) :=
      mul_lt_mul_of_pos_left (by linarith) hc'pos
    have h2 : c' * (ρ₀ / (2 * c') + ρ₀ / (4 * c' ^ 2)) = ρ₀ / 2 + ρ₀ / (4 * c') := by
      field_simp
    have h3 : ρ₀ / (4 * c') ≤ ρ₀ / 4 :=
      div_le_div_of_nonneg_left hρ₀.le (by norm_num) (by linarith)
    rw [h2] at h1
    linarith
  -- the arithmetic of Step 5
  have harith5 : ∀ D b : ℝ, b < ρ₀ / (4 * c' ^ 2) → ρ₀ ≤ c' * (D + b) →
      ρ₀ / (4 * c' ^ 2) < D := by
    intro D b hb hle
    by_contra hcon
    push Not at hcon
    have hs : ρ₀ / (4 * c' ^ 2) * (4 * c' ^ 2) = ρ₀ := by field_simp
    have h1 : D + b < 2 * (ρ₀ / (4 * c' ^ 2)) := by linarith
    have h2 : c' * (D + b) < c' * (2 * (ρ₀ / (4 * c' ^ 2))) :=
      mul_lt_mul_of_pos_left h1 hc'pos
    nlinarith [mul_nonneg (sub_nonneg.2 hc'1) hρ₂pos.le,
      mul_nonneg (mul_nonneg (sub_nonneg.2 hc'1) hc'pos.le) hρ₂pos.le]
  -- the arithmetic of Step 7
  have harith7 : ∀ D b : ℝ, b < ρ₀ / (4 * c' ^ 2) →
      ρ₀ / (2 * c') ≤ c' * (D + b) → ρ₀ / (4 * c' ^ 2) ≤ D := by
    intro D b hb hle
    have hs : ρ₀ / (2 * c') = 2 * c' * (ρ₀ / (4 * c' ^ 2)) := by
      field_simp
      ring
    rw [hs] at hle
    have h1 : c' * (D + b) < c' * (D + ρ₀ / (4 * c' ^ 2)) :=
      mul_lt_mul_of_pos_left (by linarith) hc'pos
    have h2 : c' * (ρ₀ / (4 * c' ^ 2)) < c' * D := by nlinarith
    exact (lt_of_mul_lt_mul_left h2 hc'pos.le).le
  -- ===== Step 4: part (b) =====
  have hpb : ∀ δ : ℝ, 0 < δ → δ ≤ ρ₀ / (4 * c' ^ 2) →
      ∀ h : EuclideanSpace ℝ (Fin G.n), G.hnorm h < δ →
      ∀ x ∈ TranslatedDomain G Ω δ, x ∉ BoundaryCore G Ω (ρ₀ / (2 * c')) →
      u (G.mul x h) - v x ≤ -(τ / 2) := by
    intro δ hδ hδ1 h hh x hx hxK
    have hxΩ : x ∈ Ω := hidp1 δ hx
    have hhρ₂ : G.hnorm h < ρ₀ / (4 * c' ^ 2) := lt_of_lt_of_le hh hδ1
    -- (7)
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ frontier Ω, G.hnorm (G.mul (-y) x) < ρ₀ / (2 * c') := by
      by_contra hc
      push Not at hc
      exact hxK ⟨hxΩ, hc⟩
    -- (8)
    have hxhΩ : G.mul x h ∈ Ω := htrans4 δ hδ x hx h hh
    have hassoc : G.mul (-y) (G.mul x h) = G.mul (G.mul (-y) x) h := (G.mul_assoc _ _ _).symm
    -- (9)
    have h9 : G.hnorm (G.mul (-y) (G.mul x h)) < ρ₀ := by
      rw [hassoc]
      refine lt_of_le_of_lt (htri _ _ ?_ ?_) (harith9 _ _ hxy hhρ₂)
      · linarith
      · linarith
    -- (10)
    have h10 := hstep2 (G.mul x h) (subset_closure hxhΩ) y hy h9.le
    -- (11)
    have h11 : |v (G.mul x h) - v x| ≤ ωv (G.hnorm h) := by
      have hb := hωv (G.mul x h) (subset_closure hxhΩ) x (subset_closure hxΩ)
      rwa [hrt x h] at hb
    have h11b : ωv (G.hnorm h) ≤ τ / 4 := hωv4 _ (G.hnorm_nonneg _) (by linarith)
    have h11c := (abs_le.1 h11).2
    linarith
  -- ===== Step 5: the shifted maximiser `x_M * h⁻¹` =====
  have hxMK : xM ∈ BoundaryCore G Ω ρ₀ := hEK hxME
  have hstep5 : ∀ δ : ℝ, 0 < δ → δ ≤ ρ₀ / (4 * c' ^ 2) →
      ∀ h : EuclideanSpace ℝ (Fin G.n), G.hnorm h < δ →
      G.mul xM (-h) ∈ TranslatedDomain G Ω δ ∧
      u xM - v xM - τ / 4 ≤ u (G.mul (G.mul xM (-h)) h) - v (G.mul xM (-h)) := by
    intro δ hδ hδ1 h hh
    have hhρ₂ : G.hnorm h < ρ₀ / (4 * c' ^ 2) := lt_of_lt_of_le hh hδ1
    have hdxM : G.hnorm (G.mul (-xM) (G.mul xM (-h))) = G.hnorm h := by
      rw [hrt xM (-h), G.hnorm_neg]
    -- (12)
    have hyΩ : G.mul xM (-h) ∈ Ω := by
      refine hidp7 ρ₀ hρ₀ xM hxMK ?_
      show G.hnorm (G.mul (-xM) (G.mul xM (-h))) < ρ₀
      rw [hdxM]
      linarith
    refine ⟨⟨hyΩ, ?_⟩, ?_⟩
    · intro y' hy'
      have hy'c : y' ∈ closure Ω := by rw [hfr] at hy'; exact hy'.1
      have hDν : G.hnorm (G.mul (-y') (G.mul xM (-h))) < nu :=
        hdν _ (subset_closure hyΩ) _ hy'c
      have hkey : G.mul (-y') xM = G.mul (G.mul (-y') (G.mul xM (-h))) h := by
        rw [G.mul_assoc, hcanc]
      have hρ₀le : ρ₀ ≤ G.hnorm (G.mul (-y') xM) := hxMK.2 y' hy'
      rw [hkey] at hρ₀le
      have hbound := htri (G.mul (-y') (G.mul xM (-h))) h hDν (by linarith)
      have := harith5 _ _ hhρ₂ (le_trans hρ₀le hbound)
      linarith
    · -- (13)
      have hmodv : |v (G.mul xM (-h)) - v xM| ≤ ωv (G.hnorm h) := by
        have hb := hωv (G.mul xM (-h)) (subset_closure hyΩ) xM hxM
        rwa [hdxM] at hb
      have hmb : ωv (G.hnorm h) ≤ τ / 4 := hωv4 _ (G.hnorm_nonneg _) (by linarith)
      have hc2 := (abs_le.1 hmodv).2
      rw [hcanc xM h]
      linarith
  -- ===== Step 6: part (c), attainment =====
  have hmapcont : ∀ h : EuclideanSpace ℝ (Fin G.n),
      Continuous fun y : EuclideanSpace ℝ (Fin G.n) => G.mul y h :=
    fun h => G.mul_smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have hstep6 : ∀ δ : ℝ, 0 < δ → δ ≤ ρ₀ / (4 * c' ^ 2) →
      ∀ h : EuclideanSpace ℝ (Fin G.n), G.hnorm h < δ →
      ∃ x₀ ∈ TranslatedDomain G Ω δ,
        IsMaxOn (fun y => u (G.mul y h) - v y) (TranslatedDomain G Ω δ) x₀ ∧
        u xM - v xM - τ / 4 ≤ u (G.mul x₀ h) - v x₀ := by
    intro δ hδ hδ1 h hh
    have hδρ₁ : δ < ρ₀ / (2 * c') := lt_of_le_of_lt hδ1 hρ₂ltρ₁
    -- (14)
    have hK1sub : BoundaryCore G Ω (ρ₀ / (2 * c')) ⊆ TranslatedDomain G Ω δ :=
      hidp5 δ (ρ₀ / (2 * c')) hδρ₁
    have hK1cpt : IsCompact (BoundaryCore G Ω (ρ₀ / (2 * c'))) := hidp4 _ hρ₁pos
    have hmaps : Set.MapsTo (fun y : EuclideanSpace ℝ (Fin G.n) => G.mul y h)
        (BoundaryCore G Ω (ρ₀ / (2 * c'))) (closure Ω) :=
      fun z hz => subset_closure (htrans4 δ hδ z (hK1sub hz) h hh)
    have hcont : ContinuousOn (fun y => u (G.mul y h) - v y)
        (BoundaryCore G Ω (ρ₀ / (2 * c'))) := by
      have h1 : ContinuousOn (fun y => u (G.mul y h)) (BoundaryCore G Ω (ρ₀ / (2 * c'))) :=
        hucont.comp (hmapcont h).continuousOn hmaps
      have h2 : ContinuousOn v (BoundaryCore G Ω (ρ₀ / (2 * c'))) :=
        hvcont.mono fun z hz => subset_closure (hidp2 _ hz)
      exact h1.sub h2
    obtain ⟨hy5, hy5val⟩ := hstep5 δ hδ hδ1 h hh
    have hy5K : G.mul xM (-h) ∈ BoundaryCore G Ω (ρ₀ / (2 * c')) := by
      by_contra hc
      have := hpb δ hδ hδ1 h hh _ hy5 hc
      linarith
    obtain ⟨x₀, hx₀K, hx₀max⟩ := hK1cpt.exists_isMaxOn ⟨_, hy5K⟩ hcont
    have hx₀ge : u (G.mul (G.mul xM (-h)) h) - v (G.mul xM (-h)) ≤ u (G.mul x₀ h) - v x₀ :=
      isMaxOn_iff.1 hx₀max _ hy5K
    have hx₀val : u xM - v xM - τ / 4 ≤ u (G.mul x₀ h) - v x₀ := le_trans hy5val hx₀ge
    refine ⟨x₀, hK1sub hx₀K, isMaxOn_iff.2 ?_, hx₀val⟩
    intro x hx
    by_cases hxK : x ∈ BoundaryCore G Ω (ρ₀ / (2 * c'))
    · exact isMaxOn_iff.1 hx₀max x hxK
    · have h1 := hpb δ hδ hδ1 h hh x hx hxK
      show u (G.mul x h) - v x ≤ u (G.mul x₀ h) - v x₀
      linarith
  -- ===== Step 7: part (a′) =====
  have hstep7 : ∀ δ : ℝ, 0 < δ → δ ≤ ρ₀ / (4 * c' ^ 2) →
      ∀ x ∈ BoundaryCore G Ω (ρ₀ / (2 * c')), ∀ g : EuclideanSpace ℝ (Fin G.n),
      G.hnorm g < δ → G.mul x g ∈ BoundaryCore G Ω (ρ₀ / (4 * c' ^ 2)) := by
    intro δ hδ hδ1 x hx g hg
    have hgρ₂ : G.hnorm g < ρ₀ / (4 * c' ^ 2) := lt_of_lt_of_le hg hδ1
    have hδρ₁ : δ < ρ₀ / (2 * c') := lt_of_le_of_lt hδ1 hρ₂ltρ₁
    have hxδ : x ∈ TranslatedDomain G Ω δ := hidp5 δ (ρ₀ / (2 * c')) hδρ₁ hx
    have hxgΩ : G.mul x g ∈ Ω := htrans4 δ hδ x hxδ g hg
    refine ⟨hxgΩ, ?_⟩
    intro y' hy'
    have hy'c : y' ∈ closure Ω := by rw [hfr] at hy'; exact hy'.1
    have hDν : G.hnorm (G.mul (-y') (G.mul x g)) < nu := hdν _ (subset_closure hxgΩ) _ hy'c
    have hkey : G.mul (-y') x = G.mul (G.mul (-y') (G.mul x g)) (-g) := by
      rw [G.mul_assoc, hcanc2]
    have hρ₁le' : ρ₀ / (2 * c') ≤ G.hnorm (G.mul (-y') x) := hx.2 y' hy'
    rw [hkey] at hρ₁le'
    have hbound := htri (G.mul (-y') (G.mul x g)) (-g) hDν
      (by rw [G.hnorm_neg]; linarith)
    rw [G.hnorm_neg] at hbound
    exact harith7 _ _ hgρ₂ (le_trans hρ₁le' hbound)
  -- ===== Step 3, second half: `M_δ(0) = M₀` and `A_δ(0) = E` =====
  have hstep3 : ∀ δ : ℝ, 0 < δ → δ ≤ ρ₀ / (4 * c' ^ 2) →
      MaxTranslate G Ω δ u v 0 = u xM - v xM ∧
      {x ∈ TranslatedDomain G Ω δ |
          IsMaxOn (fun y => u (G.mul y 0) - v y) (TranslatedDomain G Ω δ) x}
        = {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} := by
    intro δ _ hδ1
    have hδρ₀ : δ < ρ₀ := lt_of_le_of_lt hδ1 hρ₂ltρ₀
    -- (6)
    have hEsub : ({y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} :
        Set (EuclideanSpace ℝ (Fin G.n))) ⊆ TranslatedDomain G Ω δ :=
      fun y hy => hidp5 δ ρ₀ hδρ₀ (hEK hy)
    have hnesub : Nonempty {x : EuclideanSpace ℝ (Fin G.n) // x ∈ TranslatedDomain G Ω δ} :=
      ⟨⟨xM, hEsub hxME⟩⟩
    have hbd : ∀ x : {x : EuclideanSpace ℝ (Fin G.n) // x ∈ TranslatedDomain G Ω δ},
        u x.1 - v x.1 ≤ u xM - v xM :=
      fun x => hub x.1 (subset_closure (hidp1 δ x.2))
    have hbdd : BddAbove (Set.range
        fun x : {x : EuclideanSpace ℝ (Fin G.n) // x ∈ TranslatedDomain G Ω δ} =>
          u x.1 - v x.1) := by
      refine ⟨u xM - v xM, ?_⟩
      rintro r ⟨x, rfl⟩
      exact hbd x
    refine ⟨?_, ?_⟩
    · show (⨆ x : {x : EuclideanSpace ℝ (Fin G.n) // x ∈ TranslatedDomain G Ω δ},
          (u (G.mul x.1 0) - v x.1)) = u xM - v xM
      simp only [G.mul_zero]
      exact le_antisymm (ciSup_le hbd) (le_ciSup hbdd ⟨xM, hEsub hxME⟩)
    · refine Set.Subset.antisymm ?_ ?_
      · intro x hx
        have hxΩ : x ∈ Ω := hidp1 δ hx.1
        refine (hEmem x).2 ⟨hxΩ, le_antisymm (hub x (subset_closure hxΩ)) ?_⟩
        have hle := isMaxOn_iff.1 hx.2 xM (hEsub hxME)
        rw [G.mul_zero, G.mul_zero] at hle
        exact hle
      · intro y hy
        obtain ⟨hyΩ, hyval⟩ := (hEmem y).1 hy
        refine ⟨hEsub hy, isMaxOn_iff.2 ?_⟩
        intro z hz
        show u (G.mul z 0) - v z ≤ u (G.mul y 0) - v y
        rw [G.mul_zero, G.mul_zero, hyval]
        exact hub z (subset_closure (hidp1 δ hz))
  -- ===== assembling the statement =====
  refine ⟨c', hc'1, ?_⟩
  intro ρ₁ ρ₂ δ₁ hr1 hr2 hd1
  subst hr1
  subst hr2
  subst hd1
  refine ⟨hEK, ?_⟩
  intro δ hδ hδ1
  obtain ⟨hm0, hA0⟩ := hstep3 δ hδ hδ1
  refine ⟨hm0, hA0, fun x hx g hg => hstep7 δ hδ hδ1 x hx g hg, ?_⟩
  intro h hh
  obtain ⟨x₀, hx₀δ, hx₀max, hx₀val⟩ := hstep6 δ hδ hδ1 h hh
  -- (15)
  have hMeq : MaxTranslate G Ω δ u v h = u (G.mul x₀ h) - v x₀ := by
    have hnesub : Nonempty {x : EuclideanSpace ℝ (Fin G.n) // x ∈ TranslatedDomain G Ω δ} :=
      ⟨⟨x₀, hx₀δ⟩⟩
    have hbd : ∀ x : {x : EuclideanSpace ℝ (Fin G.n) // x ∈ TranslatedDomain G Ω δ},
        u (G.mul x.1 h) - v x.1 ≤ u (G.mul x₀ h) - v x₀ :=
      fun x => isMaxOn_iff.1 hx₀max x.1 x.2
    have hbdd : BddAbove (Set.range
        fun x : {x : EuclideanSpace ℝ (Fin G.n) // x ∈ TranslatedDomain G Ω δ} =>
          u (G.mul x.1 h) - v x.1) := by
      refine ⟨u (G.mul x₀ h) - v x₀, ?_⟩
      rintro r ⟨x, rfl⟩
      exact hbd x
    show (⨆ x : {x : EuclideanSpace ℝ (Fin G.n) // x ∈ TranslatedDomain G Ω δ},
        (u (G.mul x.1 h) - v x.1)) = u (G.mul x₀ h) - v x₀
    exact le_antisymm (ciSup_le hbd) (le_ciSup hbdd ⟨x₀, hx₀δ⟩)
  refine ⟨fun x hx hxK => hpb δ hδ hδ1 h hh x hx hxK, ?_, ⟨x₀, hx₀δ, hx₀max, hMeq⟩, ?_⟩
  · rw [hMeq]
    exact hx₀val
  · -- Step 8
    intro x hx hxmax
    have hval : u xM - v xM - τ / 4 ≤ u (G.mul x h) - v x := by
      have hge := isMaxOn_iff.1 hxmax x₀ hx₀δ
      show u xM - v xM - τ / 4 ≤ u (G.mul x h) - v x
      linarith
    have hxK : x ∈ BoundaryCore G Ω (ρ₀ / (2 * c')) := by
      by_contra hc
      have := hpb δ hδ hδ1 h hh x hx hc
      linarith
    exact ⟨hxK, hstep7 δ hδ hδ1 x hxK h hh⟩
