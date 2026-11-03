import CompND.AddConstPreservesSubsol
import CompND.BoundaryLocalization
import CompND.CitedResults
import CompND.EnvelopeIdentity
import CompND.MaxValueLipschitz
import CompND.SemiConvexLocLipschitz
import CompND.ViscTestLocalization

/-- lem:case1, the vanishing-gradient mechanism and the only place the strong maximum
principle enters: under the standing assumptions eq:bdtau-eq:rho0 there is `δ₁ > 0` such
that for every `δ ∈ (0, δ₁]` and every `η ∈ (0, δ]` some `h ∈ B_η(0)` has
`𝔛u(x * h) ≠ 0` at every `x ∈ A_δ(h)`. -/
theorem NondegeneracyAtEveryScale (G : CarnotSetting) (hc : CitedResults G)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (hAH : StructureConditionsES G.m A H)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hΩne : ∃ y : EuclideanSpace ℝ (Fin G.n), y ∉ Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (husc : LocallySemiConvexOn Ω u)
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
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ η : ℝ, 0 < η → η ≤ δ →
      ∃ h : EuclideanSpace ℝ (Fin G.n), G.hnorm h < η ∧
        ∀ x ∈ TranslatedDomain G Ω δ,
          IsMaxOn (fun y => u (G.mul y h) - v y) (TranslatedDomain G Ω δ) x →
          ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
            HasFDerivAt u D (G.mul x h) → hgrad G.sig (G.mul x h) D ≠ 0 := by
  -- ===== Step 0: the constants, and the facts of lem:bdry =====
  have hΩcl : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩbdd.closure
  have hfr : frontier Ω = closure Ω \ Ω := hΩopen.frontier_eq
  have hub : ∀ z ∈ closure Ω, u z - v z ≤ u xM - v xM := fun z hz => isMaxOn_iff.1 hxMmax z hz
  have hM0pos : 0 < u xM - v xM := lt_of_lt_of_le hτ hM0
  have hxMΩ : xM ∈ Ω := by
    by_contra hcm
    have hf : xM ∈ frontier Ω := by rw [hfr]; exact ⟨hxM, hcm⟩
    have := hbdry xM hf
    linarith
  -- the maximal set `E`, used only through this characterisation
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
  obtain ⟨c', hc'1, hBL⟩ := BoundaryLocalization G Ω hΩopen hΩbdd u v hucont hvcont ωu ωv
    hωumono hωvmono hωu hωv τ hτ hbdry xM hxM hxMmax hM0 ρ₀ hρ₀ hmod
  obtain ⟨hEK, hBLδ⟩ := hBL (ρ₀ / (2 * c')) (ρ₀ / (4 * c' ^ 2)) (ρ₀ / (4 * c' ^ 2)) rfl rfl rfl
  have hc'pos : (0:ℝ) < c' := lt_of_lt_of_le one_pos hc'1
  have hcsq : c' ≤ c' ^ 2 := by nlinarith [mul_nonneg hc'pos.le (sub_nonneg.2 hc'1)]
  have h4cpos : (0:ℝ) < 4 * c' ^ 2 := by linarith
  have hδ₁pos : 0 < ρ₀ / (4 * c' ^ 2) := div_pos hρ₀ h4cpos
  have hδ₁le : ρ₀ / (4 * c' ^ 2) ≤ ρ₀ / 4 :=
    div_le_div_of_nonneg_left hρ₀.le (by norm_num) (by linarith)
  have hδ₁ltρ₀ : ρ₀ / (4 * c' ^ 2) < ρ₀ := by linarith
  -- the geometry of the inner domains
  obtain ⟨-, hidp2, -, hidp4, hidp5, -, hidp7⟩ := InnerDomainProperties G Ω hΩopen hΩbdd
  have hhn0 : G.hnorm 0 = 0 := (G.hnorm_eq_zero 0).2 rfl
  -- ===== Step 1: `u` is `d`-Lipschitz on `K_{ρ₂}` =====
  have hK2cpt : IsCompact (BoundaryCore G Ω (ρ₀ / (4 * c' ^ 2))) := hidp4 _ hδ₁pos
  have hK2sub : BoundaryCore G Ω (ρ₀ / (4 * c' ^ 2)) ⊆ Ω := hidp2 _
  obtain ⟨C, hC0, hCLip⟩ := (SemiConvexLocLipschitz Ω u husc).2.2.1 _ hK2sub hK2cpt
  obtain ⟨pn, -, hpnmax⟩ := hΩcl.exists_isMaxOn ⟨xM, hxM⟩ continuous_norm.continuousOn
  obtain ⟨ν', hν'pos, hν'⟩ : ∃ ν' : ℝ, 0 < ν' ∧ ∀ z ∈ closure Ω, ‖z‖ ≤ ν' :=
    ⟨‖pn‖ + 1, by positivity, fun z hz => by linarith [isMaxOn_iff.1 hpnmax z hz]⟩
  obtain ⟨c₀, hc₀pos, hc₀⟩ := G.holder_equiv ν' hν'pos
  have hLu : (0:ℝ) ≤ C * c₀ := mul_nonneg hC0 hc₀pos.le
  have hLip : ∀ a ∈ BoundaryCore G Ω (ρ₀ / (4 * c' ^ 2)),
      ∀ b ∈ BoundaryCore G Ω (ρ₀ / (4 * c' ^ 2)),
      |u a - u b| ≤ C * c₀ * G.hnorm (G.mul (-b) a) := by
    intro a ha b hb
    have haΩ : a ∈ closure Ω := subset_closure (hK2sub ha)
    have hbΩ : b ∈ closure Ω := subset_closure (hK2sub hb)
    have h2 := (hc₀ a b (hν' a haΩ) (hν' b hbΩ)).1
    have h3 : ‖a - b‖ ≤ c₀ * G.hnorm (G.mul (-b) a) := by
      have h4 := mul_le_mul_of_nonneg_left h2 hc₀pos.le
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc₀pos), one_mul] at h4
      exact h4
    calc |u a - u b| ≤ C * ‖a - b‖ := hCLip a ha b hb
      _ ≤ C * (c₀ * G.hnorm (G.mul (-b) a)) := mul_le_mul_of_nonneg_left h3 hC0
      _ = C * c₀ * G.hnorm (G.mul (-b) a) := by ring
  -- the two global bounds needed by `ViscTestLocalization` in Step 8
  obtain ⟨pu, -, hpumax⟩ := hΩcl.exists_isMaxOn ⟨xM, hxM⟩ hucont
  have hMu : ∀ z ∈ Ω, u z ≤ u pu := fun z hz => isMaxOn_iff.1 hpumax z (subset_closure hz)
  obtain ⟨pv, -, hpvmin⟩ := hΩcl.exists_isMinOn ⟨xM, hxM⟩ hvcont
  have hmv : ∀ z ∈ Ω, v pv ≤ v z := fun z hz => isMinOn_iff.1 hpvmin z (subset_closure hz)
  -- ===== the statement's `δ₁` is the `δ₁` of Step 0 =====
  refine ⟨ρ₀ / (4 * c' ^ 2), hδ₁pos, ?_⟩
  intro δ hδ hδ1 η hη hηδ
  have hδρ₀ : δ < ρ₀ := lt_of_le_of_lt hδ1 hδ₁ltρ₀
  have hηρ₀ : η < ρ₀ := lt_of_le_of_lt hηδ hδρ₀
  obtain ⟨hM0eq, -, htrans, hBLh⟩ := hBLδ δ hδ hδ1
  have hattain : ∀ g : EuclideanSpace ℝ (Fin G.n), G.hnorm g < δ →
      ∃ x ∈ TranslatedDomain G Ω δ,
        IsMaxOn (fun y => u (G.mul y g) - v y) (TranslatedDomain G Ω δ) x ∧
        MaxTranslate G Ω δ u v g = u (G.mul x g) - v x :=
    fun g hg => (hBLh g hg).2.2.1
  have hAcore : ∀ g : EuclideanSpace ℝ (Fin G.n), G.hnorm g < δ →
      ∀ x ∈ TranslatedDomain G Ω δ,
        IsMaxOn (fun y => u (G.mul y g) - v y) (TranslatedDomain G Ω δ) x →
          x ∈ BoundaryCore G Ω (ρ₀ / (2 * c')) :=
    fun g hg x hx hm => ((hBLh g hg).2.2.2 x hx hm).1
  -- ===== Step 2: `M_δ` is `d`-Lipschitz on `B_δ(0)` =====
  have hMlip := MaxValueLipschitz G Ω δ (ρ₀ / (2 * c')) (ρ₀ / (4 * c' ^ 2)) hδ u v (C * c₀)
    hLu hLip hattain hAcore htrans
  -- ===== Step 3: the ball `B_η(0)` =====
  have hmul0 : ∀ z : EuclideanSpace ℝ (Fin G.n), G.mul (-0) z = z := by
    intro z
    rw [neg_zero, G.zero_mul]
  have hball0 : {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-0) z) < η}
      = {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm z < η} := by
    simp only [hmul0]
  have hB0open : IsOpen {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm z < η} :=
    isOpen_lt G.hnorm_cont continuous_const
  have hB0conn : IsConnected {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm z < η} := by
    rw [← hball0]
    exact G.ball_connected 0 η hη
  have h0mem : (0 : EuclideanSpace ℝ (Fin G.n))
      ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm z < η} := by
    show G.hnorm 0 < η
    rw [hhn0]
    exact hη
  have hLipball : ∀ a ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm z < η},
      ∀ b ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm z < η},
      |MaxTranslate G Ω δ u v a - MaxTranslate G Ω δ u v b|
        ≤ C * c₀ * G.hnorm (G.mul (-b) a) := by
    intro a ha b hb
    have ha' : G.hnorm a < η := ha
    have hb' : G.hnorm b < η := hb
    exact hMlip a b (lt_of_lt_of_le ha' hηδ) (lt_of_lt_of_le hb' hηδ)
  -- ===== Step 4: the contradiction hypothesis (6) =====
  by_contra hcon
  push Not at hcon
  -- ===== Step 5: the horizontal differential of `M_δ` vanishes a.e. on `B_η(0)` =====
  have h7 : ∀ᵐ hh ∂(MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin G.n))),
      hh ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm z < η} →
        HasPansuGradAt G.mul G.pi1 G.hnorm (MaxTranslate G Ω δ u v) hh 0 := by
    filter_upwards [hc.pansuDiff {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm z < η} hB0open
      (MaxTranslate G Ω δ u v) (C * c₀) hLipball] with hh hhae
    intro hhB
    obtain ⟨ξ, hξ⟩ := hhae hhB
    have hhη : G.hnorm hh < η := hhB
    obtain ⟨xh, hxh, hxhmax, Dh, hDh, hgz⟩ := hcon hh hhη
    have heq := EnvelopeIdentity G Ω δ hδ u v hattain hh (lt_of_lt_of_le hhη hηδ) ξ hξ
      xh hxh hxhmax Dh hDh
    have hξ0 : ξ = 0 := heq.symm.trans hgz
    rw [hξ0] at hξ
    exact hξ
  -- ===== Step 6: `M_δ ≡ M₀` on `B_η(0)`, display (8) =====
  have h8 : ∀ g : EuclideanSpace ℝ (Fin G.n), G.hnorm g < η →
      MaxTranslate G Ω δ u v g = u xM - v xM := by
    intro g hg
    have hcst := hc.pansuConst {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm z < η} hB0open
      hB0conn (MaxTranslate G Ω δ u v) (C * c₀) hLipball h7
    rw [hcst g hg 0 h0mem]
    exact hM0eq
  -- ===== Steps 7 and 8: `B_η(y) ⊆ E` for every `y ∈ E` =====
  have hstep78 : ∀ y : EuclideanSpace ℝ (Fin G.n), y ∈ Ω → u y - v y = u xM - v xM →
      ∃ t : Set (EuclideanSpace ℝ (Fin G.n)),
        t ⊆ {z : EuclideanSpace ℝ (Fin G.n) | z ∈ Ω ∧ u z - v z = u xM - v xM} ∧
        IsOpen t ∧ y ∈ t := by
    intro y hyΩ hyval
    have hyK : y ∈ BoundaryCore G Ω ρ₀ := hEK ((hEmem y).2 ⟨hyΩ, hyval⟩)
    have hyδ : y ∈ TranslatedDomain G Ω δ := hidp5 δ ρ₀ hδρ₀ hyK
    -- (9): the ball lies in `Ω`
    have hBysub : {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η} ⊆ Ω := by
      intro z hz
      refine hidp7 ρ₀ hρ₀ y hyK ?_
      have hz' : G.hnorm (G.mul (-y) z) < η := hz
      show G.hnorm (G.mul (-y) z) < ρ₀
      linarith
    have hBycont : Continuous
        fun z : EuclideanSpace ℝ (Fin G.n) => G.hnorm (G.mul (-y) z) := by
      have hc1 : Continuous fun z : EuclideanSpace ℝ (Fin G.n) => G.mul (-y) z :=
        G.mul_smooth.continuous.comp (continuous_const.prodMk continuous_id)
      exact G.hnorm_cont.comp hc1
    have hByopen : IsOpen {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η} :=
      isOpen_lt hBycont continuous_const
    have hByconn : IsConnected {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η} :=
      G.ball_connected y η hη
    have hyBy : y ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η} := by
      show G.hnorm (G.mul (-y) y) < η
      rw [G.neg_mul, hhn0]
      exact hη
    -- (10): `B_η(y) = y * B_η(0)`, eq:righttrans kept inline by pm-0012
    have hBywrite : ∀ z ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η},
        ∃ g : EuclideanSpace ℝ (Fin G.n), G.hnorm g < η ∧ z = G.mul y g := by
      intro z hz
      refine ⟨G.mul (-y) z, hz, ?_⟩
      rw [← G.mul_assoc, G.mul_neg, G.zero_mul]
    -- (11)
    have hule : ∀ z ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η},
        u z ≤ u y := by
      intro z hz
      obtain ⟨g, hg, rfl⟩ := hBywrite z hz
      obtain ⟨zg, hzg, hzgmax, hzgeq⟩ := hattain g (lt_of_lt_of_le hg hηδ)
      have h1 := isMaxOn_iff.1 hzgmax y hyδ
      have h1' : u (G.mul y g) - v y ≤ u (G.mul zg g) - v zg := h1
      rw [← hzgeq, h8 g hg] at h1'
      linarith
    -- Step 8, the sub-solution half: `u ≡ u y` on `B_η(y)`
    have hsubt : IsViscSubsol G A H Ω (fun z => u z + -(u y)) :=
      (AddConstPreservesSubsol G A H Ω u (-(u y))).1 hsub
    have hbnd1 : ∃ Mu : ℝ, ∀ z ∈ Ω, u z + -(u y) ≤ Mu :=
      ⟨u pu + -(u y), fun z hz => by linarith [hMu z hz]⟩
    have hsubV : IsViscSubsol G A H {z : EuclideanSpace ℝ (Fin G.n) |
        G.hnorm (G.mul (-y) z) < η} (fun z => u z + -(u y)) :=
      ((ViscTestLocalization G A H Ω (fun z => u z + -(u y))).1 hbnd1 hsubt).2 _
        hByopen hBysub
    have hmaxV : IsMaxOn (fun z => u z + -(u y))
        {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η} y :=
      isMaxOn_iff.2 fun z hz => by
        have hz1 := hule z hz
        show u z + -(u y) ≤ u y + -(u y)
        linarith
    have hval1 : (0:ℝ) ≤ u y + -(u y) := by linarith
    have h12 := hc.strongMax A H hAH {z : EuclideanSpace ℝ (Fin G.n) |
      G.hnorm (G.mul (-y) z) < η} hByopen hByconn (fun z => u z + -(u y)) hsubV y hyBy
      hmaxV hval1
    have hueq : ∀ z ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η},
        u z = u y := by
      intro z hz
      have h := h12 z hz
      have h' : u z + -(u y) = u y + -(u y) := h
      linarith
    -- Step 8, the super-solution half: `v ≡ v y` on `B_η(y)`
    have hvge : ∀ z ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η},
        v y ≤ v z := by
      intro z hz
      have hzΩ : z ∈ Ω := hBysub hz
      have h1 := hub z (subset_closure hzΩ)
      have h3 := hueq z hz
      linarith
    have hsupt : IsViscSupersol G A H Ω (fun z => v z + -(v y)) :=
      (AddConstPreservesSubsol G A H Ω v (-(v y))).2 hsup
    have hbnd2 : ∃ mv : ℝ, ∀ z ∈ Ω, mv ≤ v z + -(v y) :=
      ⟨v pv + -(v y), fun z hz => by linarith [hmv z hz]⟩
    have hsupV : IsViscSupersol G A H {z : EuclideanSpace ℝ (Fin G.n) |
        G.hnorm (G.mul (-y) z) < η} (fun z => v z + -(v y)) :=
      ((ViscTestLocalization G A H Ω (fun z => v z + -(v y))).2 hbnd2 hsupt).2 _
        hByopen hBysub
    have hminV : IsMinOn (fun z => v z + -(v y))
        {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η} y :=
      isMinOn_iff.2 fun z hz => by
        have hz1 := hvge z hz
        show v y + -(v y) ≤ v z + -(v y)
        linarith
    have hval2 : v y + -(v y) ≤ (0:ℝ) := by linarith
    have h13 := hc.strongMin A H hAH {z : EuclideanSpace ℝ (Fin G.n) |
      G.hnorm (G.mul (-y) z) < η} hByopen hByconn (fun z => v z + -(v y)) hsupV y hyBy
      hminV hval2
    have hveq : ∀ z ∈ {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η},
        v z = v y := by
      intro z hz
      have h := h13 z hz
      have h' : v z + -(v y) = v y + -(v y) := h
      linarith
    -- (14)
    refine ⟨{z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-y) z) < η}, ?_, hByopen, hyBy⟩
    intro z hz
    refine ⟨hBysub hz, ?_⟩
    rw [hueq z hz, hveq z hz]
    exact hyval
  -- ===== Step 9: `E` contains a connected component of `Ω`, and the contradiction =====
  have hEopen : IsOpen {z : EuclideanSpace ℝ (Fin G.n) | z ∈ Ω ∧ u z - v z = u xM - v xM} :=
    isOpen_iff_forall_mem_open.2 fun y hy => hstep78 y hy.1 hy.2
  have hdiffCA : ∀ z ∈ Ω, ContinuousAt (fun w => u w - v w) z := by
    intro z hz
    exact (hucont.sub hvcont).continuousAt (mem_nhds_iff.2 ⟨Ω, subset_closure, hΩopen, hz⟩)
  have hU2open : IsOpen {z : EuclideanSpace ℝ (Fin G.n) | z ∈ Ω ∧ u z - v z < u xM - v xM} := by
    refine isOpen_iff_forall_mem_open.2 ?_
    intro z hz
    have h1 : (fun w => u w - v w) ⁻¹' Set.Iio (u xM - v xM) ∈ nhds z :=
      (hdiffCA z hz.1) (Iio_mem_nhds hz.2)
    obtain ⟨t, hts, htopen, hzt⟩ := mem_nhds_iff.1 h1
    exact ⟨Ω ∩ t, fun w hw => ⟨hw.1, hts hw.2⟩, hΩopen.inter htopen, ⟨hz.1, hzt⟩⟩
  have hCopen : IsOpen (connectedComponentIn Ω xM) := hΩopen.connectedComponentIn
  have hCconn : IsConnected (connectedComponentIn Ω xM) :=
    isConnected_connectedComponentIn_iff.2 hxMΩ
  have hCsub : connectedComponentIn Ω xM ⊆ Ω := connectedComponentIn_subset Ω xM
  have hxMC : xM ∈ connectedComponentIn Ω xM := mem_connectedComponentIn hxMΩ
  -- (15)
  have hCE : ∀ z ∈ connectedComponentIn Ω xM, u z - v z = u xM - v xM := by
    intro z hz
    have hzΩ : z ∈ Ω := hCsub hz
    by_contra hne
    have hlt : u z - v z < u xM - v xM := lt_of_le_of_ne (hub z (subset_closure hzΩ)) hne
    have hcover : connectedComponentIn Ω xM ⊆
        {w : EuclideanSpace ℝ (Fin G.n) | w ∈ Ω ∧ u w - v w = u xM - v xM} ∪
        {w : EuclideanSpace ℝ (Fin G.n) | w ∈ Ω ∧ u w - v w < u xM - v xM} := by
      intro w hw
      have hwΩ : w ∈ Ω := hCsub hw
      rcases eq_or_lt_of_le (hub w (subset_closure hwΩ)) with he | hl
      · exact Or.inl ⟨hwΩ, he⟩
      · exact Or.inr ⟨hwΩ, hl⟩
    obtain ⟨w, -, hw1, hw2⟩ := hCconn.isPreconnected _ _ hEopen hU2open hcover
      ⟨xM, hxMC, hxMΩ, rfl⟩ ⟨z, hz, hzΩ, hlt⟩
    have e1 : u w - v w = u xM - v xM := hw1.2
    have e2 : u w - v w < u xM - v xM := hw2.2
    linarith
  -- `∂C ≠ ∅`: the only use of `hΩne`
  have hfrCne : (frontier (connectedComponentIn Ω xM)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    have hsubcl : closure (connectedComponentIn Ω xM) ⊆ connectedComponentIn Ω xM := by
      intro w hw
      by_contra hwC
      have hwfr : w ∈ frontier (connectedComponentIn Ω xM) := by
        rw [hCopen.frontier_eq]
        exact ⟨hw, hwC⟩
      rw [hemp] at hwfr
      exact hwfr
    have hclosed : IsClosed (connectedComponentIn Ω xM) :=
      closure_eq_iff_isClosed.1 (Set.Subset.antisymm hsubcl subset_closure)
    rcases isClopen_iff.1 (⟨hclosed, hCopen⟩ : IsClopen (connectedComponentIn Ω xM)) with h | h
    · rw [h] at hxMC
      exact hxMC
    · obtain ⟨p, hp⟩ := hΩne
      refine hp (hCsub ?_)
      rw [h]
      exact Set.mem_univ p
  -- `∂C ⊆ ∂Ω`
  have hfrsub : frontier (connectedComponentIn Ω xM) ⊆ frontier Ω := by
    intro z hz
    rw [hCopen.frontier_eq] at hz
    obtain ⟨hzcl, hzC⟩ := hz
    have hzΩcl : z ∈ closure Ω := closure_mono hCsub hzcl
    by_cases hzΩ : z ∈ Ω
    · exfalso
      have hC'open : IsOpen (connectedComponentIn Ω z) := hΩopen.connectedComponentIn
      have hzC' : z ∈ connectedComponentIn Ω z := mem_connectedComponentIn hzΩ
      obtain ⟨w, hwC', hwC⟩ := mem_closure_iff.1 hzcl (connectedComponentIn Ω z) hC'open hzC'
      have h1 : connectedComponentIn Ω z = connectedComponentIn Ω w :=
        connectedComponentIn_eq hwC'
      have h2 : connectedComponentIn Ω xM = connectedComponentIn Ω w :=
        connectedComponentIn_eq hwC
      refine hzC ?_
      rw [h2, ← h1]
      exact hzC'
    · rw [hfr]
      exact ⟨hzΩcl, hzΩ⟩
  -- the final contradiction
  obtain ⟨z, hzfr⟩ := hfrCne
  have hzΩfr : z ∈ frontier Ω := hfrsub hzfr
  rw [hCopen.frontier_eq] at hzfr
  have hzcl : z ∈ closure (connectedComponentIn Ω xM) := hzfr.1
  have hzΩcl : z ∈ closure Ω := closure_mono hCsub hzcl
  have hnb : (nhdsWithin z (connectedComponentIn Ω xM)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hzcl
  have ht1 : Filter.Tendsto (fun w => u w - v w)
      (nhdsWithin z (connectedComponentIn Ω xM)) (nhds (u z - v z)) :=
    ((hucont.sub hvcont) z hzΩcl).mono (hCsub.trans subset_closure)
  have ht2 : Filter.Tendsto (fun w => u w - v w)
      (nhdsWithin z (connectedComponentIn Ω xM)) (nhds (u xM - v xM)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hCE w hw).symm
  have hfinal : u z - v z = u xM - v xM := tendsto_nhds_unique ht1 ht2
  have hbd := hbdry z hzΩfr
  linarith
