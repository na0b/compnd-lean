import CompND.BoundaryLocalization
import CompND.ComparisonNondegenerateSemiconvex
import CompND.LeftTranslateHgrad
import CompND.LeftTranslateSubsol
import CompND.NondegeneracyAtEveryScale
import CompND.TranslatedPairDifferentiable

/-- The first paragraph of thm:uncond(iii): in an abelian setting no semi-convex/semi-concave
pair can satisfy the standing assumptions eq:bdtau-eq:rho0. Commutativity is what makes the
right translate `u_h` a sub-solution and what transports the non-vanishing horizontal
gradient from `x * h` to `x`, so that prop:comp0 applies on `Ω_δ` and contradicts
`M_δ(h) ≥ M₀ - τ/4 > 0`. -/
theorem AbelianNoStandingPair (G : CarnotSetting) (hc : CitedResults G)
    (hab : ∀ x y : EuclideanSpace ℝ (Fin G.n), G.mul x y = G.mul y x)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (hAH : StructureConditionsES G.m A H) (hN : NormalizedAH G.m A H)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hΩne : ∃ y : EuclideanSpace ℝ (Fin G.n), y ∉ Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (husc : LocallySemiConvexOn Ω u) (hvsc : LocallySemiConvexOn Ω (fun y => -v y))
    (hsub : IsViscSubsol G A H Ω u) (hsup : IsViscSupersol G A H Ω v)
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
    False := by
  -- ===== Step 1: the two thresholds and the scale `δ` =====
  have hΩcl : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩbdd.closure
  obtain ⟨c', hc'1, hBL⟩ := BoundaryLocalization G Ω hΩopen hΩbdd u v hucont hvcont ωu ωv
    hωumono hωvmono hωu hωv τ hτ hbdry xM hxM hxMmax hM0 ρ₀ hρ₀ hmod
  obtain ⟨-, hBLδ⟩ := hBL (ρ₀ / (2 * c')) (ρ₀ / (4 * c' ^ 2)) (ρ₀ / (4 * c' ^ 2)) rfl rfl rfl
  have hc'pos : (0:ℝ) < c' := lt_of_lt_of_le one_pos hc'1
  have hcsq : c' ≤ c' ^ 2 := by nlinarith [mul_nonneg hc'pos.le (sub_nonneg.2 hc'1)]
  have h2cpos : (0:ℝ) < 2 * c' := by linarith
  have h4cpos : (0:ℝ) < 4 * c' ^ 2 := by linarith
  have hδ₁pos : 0 < ρ₀ / (4 * c' ^ 2) := div_pos hρ₀ h4cpos
  have hρ₁pos : 0 < ρ₀ / (2 * c') := div_pos hρ₀ h2cpos
  -- display (1)/(2): `δ₁ < ρ₁`, because `ρ₁ = 2c' δ₁` and `c' ≥ 1`
  have hδ₁ltρ₁ : ρ₀ / (4 * c' ^ 2) < ρ₀ / (2 * c') :=
    div_lt_div_of_pos_left hρ₀ h2cpos (by linarith)
  obtain ⟨δ₁', hδ₁'pos, hND⟩ := NondegeneracyAtEveryScale G hc A H hAH Ω hΩopen hΩbdd hΩne
    u v hucont hvcont husc hsub hsup ωu ωv hωumono hωvmono hωu hωv τ hτ hbdry xM hxM hxMmax
    hM0 ρ₀ hρ₀ hmod
  obtain ⟨δ, hδpos, hδ1, hδ1', hδρ₁⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ₀ / (4 * c' ^ 2) ∧ δ ≤ δ₁' ∧
      δ < ρ₀ / (2 * c') :=
    ⟨min (ρ₀ / (4 * c' ^ 2)) δ₁', lt_min hδ₁pos hδ₁'pos, min_le_left _ _, min_le_right _ _,
      lt_of_le_of_lt (min_le_left _ _) hδ₁ltρ₁⟩
  -- the geometry of the inner domains (reached through `BoundaryLocalization`)
  obtain ⟨hidp1, -, hidp3, hidp4, -, -, -⟩ := InnerDomainProperties G Ω hΩopen hΩbdd
  obtain ⟨-, -, -, hBLh⟩ := hBLδ δ hδpos hδ1
  -- ===== Step 2: the translation `h` =====
  obtain ⟨h, hhδ, hnd3⟩ := hND δ hδpos hδ1' δ hδpos le_rfl
  obtain ⟨hTP1, hTP2, hTP3, hTP4⟩ :=
    TranslatedPairDifferentiable G Ω hΩopen hΩbdd u v husc hvsc δ hδpos h hhδ
  -- ===== Step 3: `u_h` is a viscosity sub-solution in `Ω_δ` (first use of commutativity) =====
  -- display (5): the right and left translates are the same function
  have hufun : (fun y : EuclideanSpace ℝ (Fin G.n) => u (G.mul y h))
      = fun y : EuclideanSpace ℝ (Fin G.n) => u (G.mul h y) :=
    funext fun y => by rw [hab y h]
  have hLsub : IsViscSubsol G A H ((fun x => G.mul h x) ⁻¹' Ω) (fun x => u (G.mul h x)) :=
    (LeftTranslateSubsol G A H Ω u h).1 hsub
  obtain ⟨pu, -, hpumax⟩ := hΩcl.exists_isMaxOn ⟨xM, hxM⟩ hucont
  obtain ⟨pv, -, hpvmin⟩ := hΩcl.exists_isMinOn ⟨xM, hxM⟩ hvcont
  have hbnd1 : ∃ Mu : ℝ, ∀ y ∈ ((fun x => G.mul h x) ⁻¹' Ω), u (G.mul h y) ≤ Mu := by
    refine ⟨u pu, fun y hy => ?_⟩
    have hy' : G.mul h y ∈ Ω := hy
    exact isMaxOn_iff.1 hpumax _ (subset_closure hy')
  have hsubpre : TranslatedDomain G Ω δ ⊆ (fun x => G.mul h x) ⁻¹' Ω := by
    intro x hx
    show G.mul h x ∈ Ω
    rw [hab h x]
    exact hTP1 x hx
  have hsubL : IsViscSubsol G A H (TranslatedDomain G Ω δ) (fun x => u (G.mul h x)) :=
    ((ViscTestLocalization G A H ((fun x => G.mul h x) ⁻¹' Ω)
      (fun x => u (G.mul h x))).1 hbnd1 hLsub).2 _ (hidp3 δ) hsubpre
  have hsubΩδ : IsViscSubsol G A H (TranslatedDomain G Ω δ) (fun y => u (G.mul y h)) := by
    rw [hufun]
    exact hsubL
  -- ===== Step 4: `v` is a viscosity super-solution in `Ω_δ` =====
  have hbnd2 : ∃ mv : ℝ, ∀ y ∈ Ω, mv ≤ v y := by
    refine ⟨v pv, fun y hy => ?_⟩
    exact isMinOn_iff.1 hpvmin y (subset_closure hy)
  have hsupΩδ : IsViscSupersol G A H (TranslatedDomain G Ω δ) v :=
    ((ViscTestLocalization G A H Ω v).2 hbnd2 hsup).2 _ (hidp3 δ) (hidp1 δ)
  -- ===== Step 6: the non-degeneracy hypothesis on `Ω_δ` (second use of commutativity) =====
  have hnd6 : ∀ x ∈ TranslatedDomain G Ω δ,
      IsMaxOn (fun y => u (G.mul y h) - v y) (TranslatedDomain G Ω δ) x →
      ∀ D' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
        HasFDerivAt (fun y => u (G.mul y h)) D' x → hgrad G.sig x D' ≠ 0 := by
    intro x hx hxmax D' hD'
    obtain ⟨-, D, hD⟩ := hTP4 x hx hxmax
    have hD'left : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin G.n) => u (G.mul h y)) D' x := by
      rw [← hufun]
      exact hD'
    have hDleft : HasFDerivAt u D (G.mul h x) := by
      rw [hab h x]
      exact hD
    have hkey := LeftTranslateHgrad G u h x D D' hDleft hD'left
    rw [hkey, hab h x]
    exact hnd3 x hx hxmax D hD
  -- ===== Step 7: `closure Ω_δ * h ⊆ closure Ω`, and continuity up to `∂Ω_δ` =====
  have hclsub : closure (TranslatedDomain G Ω δ) ⊆ closure Ω := closure_mono (hidp1 δ)
  have hmapcont : Continuous fun y : EuclideanSpace ℝ (Fin G.n) => G.mul y h :=
    G.mul_smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have h7 : ∀ z ∈ closure (TranslatedDomain G Ω δ), G.mul z h ∈ closure Ω := by
    intro z hz
    have h1 : G.mul z h
        ∈ closure ((fun y : EuclideanSpace ℝ (Fin G.n) => G.mul y h) ''
            TranslatedDomain G Ω δ) :=
      image_closure_subset_closure_image hmapcont ⟨z, hz, rfl⟩
    refine closure_mono ?_ h1
    rintro w ⟨x, hx, rfl⟩
    exact hTP1 x hx
  have hucontδ : ContinuousOn (fun y => u (G.mul y h))
      (closure (TranslatedDomain G Ω δ)) := hucont.comp hmapcont.continuousOn h7
  have hvcontδ : ContinuousOn v (closure (TranslatedDomain G Ω δ)) := hvcont.mono hclsub
  -- ===== Step 8: the boundary inequality on `∂Ω_δ` =====
  have hdcont : ∀ y : EuclideanSpace ℝ (Fin G.n),
      Continuous fun w : EuclideanSpace ℝ (Fin G.n) => G.hnorm (G.mul (-y) w) := by
    intro y
    have hc1 : Continuous fun w : EuclideanSpace ℝ (Fin G.n) => G.mul (-y) w :=
      G.mul_smooth.continuous.comp (continuous_const.prodMk continuous_id)
    exact G.hnorm_cont.comp hc1
  have hbdry8 : ∀ z ∈ frontier (TranslatedDomain G Ω δ), u (G.mul z h) ≤ v z := by
    intro z hz
    rw [(hidp3 δ).frontier_eq] at hz
    obtain ⟨hzcl, hznot⟩ := hz
    have hnb : (nhdsWithin z (TranslatedDomain G Ω δ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hzcl
    -- (8a), display (8)
    have h8 : ∀ y ∈ frontier Ω, δ ≤ G.hnorm (G.mul (-y) z) := by
      intro y hy
      have ht : Filter.Tendsto (fun w => G.hnorm (G.mul (-y) w))
          (nhdsWithin z (TranslatedDomain G Ω δ)) (nhds (G.hnorm (G.mul (-y) z))) :=
        (hdcont y).continuousWithinAt
      refine ge_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (hw.2 y hy).le
    have hzΩ : z ∈ Ω := by
      by_contra hzn
      have hzfr : z ∈ frontier Ω := by
        rw [hΩopen.frontier_eq]
        exact ⟨hclsub hzcl, hzn⟩
      have hd0 := h8 z hzfr
      rw [G.neg_mul, (G.hnorm_eq_zero 0).2 rfl] at hd0
      linarith
    have hzK : z ∉ BoundaryCore G Ω (ρ₀ / (2 * c')) := by
      intro hzK
      obtain ⟨y₀, hy₀, hle⟩ : ∃ y₀ ∈ frontier Ω, G.hnorm (G.mul (-y₀) z) ≤ δ := by
        by_contra hc2
        push Not at hc2
        exact hznot ⟨hzΩ, hc2⟩
      have := hzK.2 y₀ hy₀
      linarith
    -- (8b)
    have hK1cl : IsClosed (BoundaryCore G Ω (ρ₀ / (2 * c'))) := (hidp4 _ hρ₁pos).isClosed
    have hnbh : (BoundaryCore G Ω (ρ₀ / (2 * c')))ᶜ ∈ nhds z :=
      hK1cl.isOpen_compl.mem_nhds hzK
    -- (8c)
    have htlim : Filter.Tendsto (fun w => u (G.mul w h) - v w)
        (nhdsWithin z (TranslatedDomain G Ω δ)) (nhds (u (G.mul z h) - v z)) :=
      ((hucontδ.sub hvcontδ) z hzcl).mono subset_closure
    have hfin : u (G.mul z h) - v z ≤ -(τ / 2) := by
      refine le_of_tendsto htlim ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnbh] with w hw1 hw2
      exact (hBLh h hhδ).1 w hw1 hw2
    linarith
  -- ===== Step 9: prop:comp0 on `Ω_δ` =====
  have hΩδbdd : Bornology.IsBounded (TranslatedDomain G Ω δ) := hΩbdd.subset (hidp1 δ)
  have h10 := ComparisonNondegenerateSemiconvex G hc A H hAH hN (TranslatedDomain G Ω δ)
    (hidp3 δ) hΩδbdd (fun y => u (G.mul y h)) v hucontδ hvcontδ hTP2 hTP3 hbdry8
    hsubΩδ hsupΩδ hnd6
  -- ===== Step 10: the contradiction =====
  obtain ⟨-, hMlow, ⟨xs, hxs, -, hxseq⟩, -⟩ := hBLh h hhδ
  have h1 := h10 xs hxs
  rw [hxseq] at hMlow
  have h1' : u (G.mul xs h) ≤ v xs := h1
  linarith
