import CompND.CitedResults
import CompND.ReducedDomainProperties
import CompND.SemiConvexLocLipschitz
import CompND.AddConstPreservesSubsol

/-- The common opening of the proofs of thm:comp, thm:uncond(i) and thm:uncond(iii), proved
once: with `τ = M₀/2` and `ṽ = v + τ`, for every small `ε` the regularized pair
`(u^ε, ṽ_ε)` satisfies on `Ω[ε]` the standing assumptions eq:bdtau with `τ/2` in place of
`τ`, and the interior maximum sets `E_ε` of eq:Eeps converge to `E = argmax_Ω(u - v)`. -/
theorem RegularizedPairStandingAssumptions (G : CarnotSetting) (hc : CitedResults G)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ) (hAH : StructureConditionsES G.m A H)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hΩne : ∃ y : EuclideanSpace ℝ (Fin G.n), y ∉ Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hu : ContinuousOn u (closure Ω)) (hv : ContinuousOn v (closure Ω))
    (hsub : IsViscSubsol G A H Ω u) (hsup : IsViscSupersol G A H Ω v)
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x)
    (R : ℝ) (hR : 0 ≤ R) (hRb : ∀ x ∈ closure Ω, |u x| ≤ R / 2 ∧ |v x| ≤ R / 2)
    (xM : EuclideanSpace ℝ (Fin G.n)) (hxM : xM ∈ closure Ω)
    (hxMmax : IsMaxOn (fun y => u y - v y) (closure Ω) xM)
    (hM0 : 0 < u xM - v xM) :
    ∀ τ : ℝ, τ = (u xM - v xM) / 2 →
    ∀ E : Set (EuclideanSpace ℝ (Fin G.n)),
      E = {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} →
      E.Nonempty ∧ IsCompact E ∧
      (∃ ε₁ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₁ →
        ∀ uE vE : EuclideanSpace ℝ (Fin G.n) → ℝ,
        uE = SupConv G Ω u ε → vE = (fun y => InfConv G Ω v ε y + τ) →
          E ⊆ ReducedDomain G Ω R ε ∧
          ContinuousOn uE (closure (ReducedDomain G Ω R ε)) ∧
          ContinuousOn vE (closure (ReducedDomain G Ω R ε)) ∧
          LocallySemiConvexOn (ReducedDomain G Ω R ε) uE ∧
          LocallySemiConvexOn (ReducedDomain G Ω R ε) (fun y => -(vE y)) ∧
          IsViscSubsol G A H (ReducedDomain G Ω R ε) uE ∧
          IsViscSupersol G A H (ReducedDomain G Ω R ε) vE ∧
          (∀ z ∈ frontier (ReducedDomain G Ω R ε), uE z - vE z ≤ -(τ / 2)) ∧
          (∃ xe ∈ ReducedDomain G Ω R ε,
            IsMaxOn (fun y => uE y - vE y) (closure (ReducedDomain G Ω R ε)) xe ∧
            τ ≤ uE xe - vE xe) ∧
          (∀ z ∈ closure (ReducedDomain G Ω R ε),
            IsMaxOn (fun y => uE y - vE y) (closure (ReducedDomain G Ω R ε)) z →
            z ∈ ReducedDomain G Ω R ε)) ∧
      (∀ η : ℝ, 0 < η → ∃ ε₂ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₂ →
        ∀ z ∈ ReducedDomain G Ω R ε,
          IsMaxOn (fun y => SupConv G Ω u ε y - (InfConv G Ω v ε y + τ))
            (closure (ReducedDomain G Ω R ε)) z →
          ∃ p ∈ E, G.hnorm (G.mul (-p) z) < η) := by
  -- `closure Ω` is compact, and `Ω` open gives `frontier Ω = closure Ω \ Ω`
  have hclcpt : IsCompact (closure Ω) := hΩbdd.isCompact_closure
  -- generic facts about local semi-convexity used in Step 6
  have scCongr : ∀ (f g : EuclideanSpace ℝ (Fin G.n) → ℝ)
      (V : Set (EuclideanSpace ℝ (Fin G.n))), (∀ y, f y = g y) →
      LocallySemiConvexOn V f → LocallySemiConvexOn V g := by
    intro f g V heq hf
    rw [show g = f from funext fun y => (heq y).symm]
    exact hf
  -- (6a) local semi-convexity RESTRICTS to open subsets: it is a pointwise-local notion.
  -- (Contrast pm-0009: the viscosity property does NOT restrict, which is why 2(d) comes
  -- from `wang3` on the reduced domain rather than from `hsub`.)
  have scRestrict : ∀ (f : EuclideanSpace ℝ (Fin G.n) → ℝ)
      (V : Set (EuclideanSpace ℝ (Fin G.n))), IsOpen V → V ⊆ Ω →
      LocallySemiConvexOn Ω f → LocallySemiConvexOn V f := by
    intro f V hVopen hVsub hf x hx
    obtain ⟨ρ, hρ, Λ, hΛ, hball, hcv⟩ := hf x (hVsub hx)
    obtain ⟨σ, hσ, hσball⟩ := Metric.isOpen_iff.1 hVopen x hx
    refine ⟨min ρ σ, lt_min hρ hσ, Λ, hΛ,
      (Metric.ball_subset_ball (min_le_right _ _)).trans hσball, ?_⟩
    exact hcv.subset (Metric.ball_subset_ball (min_le_left _ _)) (convex_ball x _)
  -- (6b) local semi-convexity is invariant under adding a constant
  have scAddConst : ∀ (f : EuclideanSpace ℝ (Fin G.n) → ℝ) (c : ℝ)
      (V : Set (EuclideanSpace ℝ (Fin G.n))),
      LocallySemiConvexOn V f → LocallySemiConvexOn V (fun y => f y + c) := by
    intro f c V hf x hx
    obtain ⟨ρ, hρ, Λ, hΛ, hball, hcv⟩ := hf x hx
    refine ⟨ρ, hρ, Λ, hΛ, hball, ⟨hcv.1, fun p hp q hq a b ha hb hab => ?_⟩⟩
    have h := hcv.2 hp hq ha hb hab
    have hab' : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    simp only [smul_eq_mul] at h ⊢
    linarith only [h, hab']
  -- the seven conjuncts of `ReducedDomainProperties`, named once
  obtain ⟨hrd1, hrd2, hrd3, hrd4, hrd5, hrd6, hrd7⟩ :=
    ReducedDomainProperties G Ω hΩopen hΩbdd hΩne R hR
  -- Step 1: `x_M ∈ Ω`
  have hxMΩ : xM ∈ Ω := by
    by_contra hcc
    have hfr : xM ∈ frontier Ω := by
      rw [hΩopen.frontier_eq]
      exact ⟨hxM, hcc⟩
    have h := hbdry xM hfr
    linarith only [h, hM0]
  intro τ hτ E hE
  have hτpos : 0 < τ := by
    rw [hτ]
    linarith only [hM0]
  have hM2 : u xM - v xM = 2 * τ := by
    rw [hτ]
    ring
  -- Step 2, display (2a): `E` is the super-level set of `u - v` at `M₀` in `closure Ω`
  have h2a : ∀ y : EuclideanSpace ℝ (Fin G.n),
      y ∈ E ↔ (y ∈ closure Ω ∧ u xM - v xM ≤ u y - v y) := by
    intro y
    rw [hE]
    refine ⟨fun hy => ⟨subset_closure hy.1, hy.2 hxM⟩, fun hy => ?_⟩
    obtain ⟨hycl, hyge⟩ := hy
    have hyle : u y - v y ≤ u xM - v xM := hxMmax hycl
    have hyeq : u y - v y = u xM - v xM := le_antisymm hyle hyge
    have hymax : IsMaxOn (fun z => u z - v z) (closure Ω) y := by
      intro w hw
      show u w - v w ≤ u y - v y
      rw [hyeq]
      exact hxMmax hw
    refine ⟨?_, hymax⟩
    by_contra hcc
    have hfr : y ∈ frontier Ω := by
      rw [hΩopen.frontier_eq]
      exact ⟨hycl, hcc⟩
    have h := hbdry y hfr
    linarith only [h, hyeq, hM0]
  have hEne : E.Nonempty := by
    refine ⟨xM, ?_⟩
    rw [hE]
    exact ⟨hxMΩ, hxMmax⟩
  have hEsubcl : E ⊆ closure Ω := fun y hy => ((h2a y).1 hy).1
  have hEval : ∀ y ∈ E, u y - v y = u xM - v xM := fun y hy =>
    le_antisymm (hxMmax ((h2a y).1 hy).1) ((h2a y).1 hy).2
  have hEcpt : IsCompact E := by
    have hcl : IsClosed E := by
      have hrw : E = closure Ω ∩ (fun y => u y - v y) ⁻¹' Set.Ici (u xM - v xM) := by
        ext y
        exact h2a y
      rw [hrw]
      exact (hu.sub hv).preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
    exact hclcpt.of_isClosed_subset hcl hEsubcl
  -- Step 3: uniform continuity of `u` and `v` on `closure Ω` for the quasi-distance `d`,
  -- obtained from Euclidean uniform continuity on the compact `closure Ω` and the LOWER
  -- Hölder bound of clause (6) of `CarnotNorm` (pm-0013: `d` is not a metric, so the
  -- comparison must come from that clause with its constant).
  have hunif : ∀ θ : ℝ, 0 < θ → ∃ ρ > 0, ∀ a ∈ closure Ω, ∀ b ∈ closure Ω,
      G.hnorm (G.mul (-b) a) < ρ → |u a - u b| + |v a - v b| < θ := by
    intro θ hθ
    have hucu := hclcpt.uniformContinuousOn_of_continuous hu
    have hvcu := hclcpt.uniformContinuousOn_of_continuous hv
    rw [Metric.uniformContinuousOn_iff] at hucu hvcu
    obtain ⟨σu, hσu, hbu⟩ := hucu (θ / 4) (by linarith only [hθ])
    obtain ⟨σv, hσv, hbv⟩ := hvcu (θ / 4) (by linarith only [hθ])
    obtain ⟨ν0, hν0⟩ := hclcpt.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin G.n))
    have hνnn : (0:ℝ) ≤ max ν0 0 := le_max_right _ _
    have hνpos : (0:ℝ) < max ν0 0 + 1 := by linarith only [hνnn]
    obtain ⟨c2, hc2pos, hc2⟩ := G.holder_equiv (max ν0 0 + 1) hνpos
    have hnorml : ∀ a ∈ closure Ω, ‖a‖ ≤ max ν0 0 + 1 := by
      intro a ha
      have h := hν0 ha
      rw [Metric.mem_closedBall, dist_zero_right] at h
      have h2 : ν0 ≤ max ν0 0 := le_max_left _ _
      linarith only [h, h2]
    refine ⟨min σu σv / c2, div_pos (lt_min hσu hσv) hc2pos, fun a ha b hb hd => ?_⟩
    obtain ⟨hlow, -⟩ := hc2 a b (hnorml a ha) (hnorml b hb)
    have hdist : ‖a - b‖ < min σu σv := by
      have h1 : ‖a - b‖ ≤ c2 * G.hnorm (G.mul (-b) a) := by
        have h := mul_le_mul_of_nonneg_left hlow hc2pos.le
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc2pos), one_mul] at h
        exact h
      have h2 : c2 * G.hnorm (G.mul (-b) a) < c2 * (min σu σv / c2) :=
        mul_lt_mul_of_pos_left hd hc2pos
      have heq : c2 * (min σu σv / c2) = min σu σv := by
        field_simp
      rw [heq] at h2
      linarith only [h1, h2]
    have h1 := hbu a ha b hb (by rw [dist_eq_norm]; exact lt_of_lt_of_le hdist (min_le_left _ _))
    have h2 := hbv a ha b hb (by rw [dist_eq_norm]; exact lt_of_lt_of_le hdist (min_le_right _ _))
    rw [Real.dist_eq] at h1 h2
    linarith only [h1, h2, hθ]
  -- Step 4: the quantitative boundary gap, display (4a), at `θ := τ/8`
  obtain ⟨ρ0, hρ0pos, h4a⟩ := hunif (τ / 8) (by linarith only [hτpos])
  -- Step 5(a): `E ⊆ Ω[ε]` for all small `ε`, by the exhaustion (clause 5) and compactness
  obtain ⟨εa, hεapos, h5a0⟩ : ∃ εa > 0, ∀ ε : ℝ, 0 < ε → ε < εa →
      E ⊆ ReducedDomain G Ω R ε := by
    have hcover : E ⊆ ⋃ k : ℕ, ReducedDomain G Ω R (1 / (k + 1 : ℝ)) := by
      intro x hx
      have hxΩ : x ∈ Ω := by
        rw [hE] at hx
        exact hx.1
      obtain ⟨ε0, hε0pos, hε0⟩ := hrd5 x hxΩ
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε0pos
      exact Set.mem_iUnion.2 ⟨k, hε0 _ (by positivity) hk⟩
    obtain ⟨tfin, htfin⟩ := hEcpt.elim_finite_subcover
      (fun k : ℕ => ReducedDomain G Ω R (1 / (k + 1 : ℝ)))
      (fun k => hrd4 _ (by positivity)) hcover
    obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, ∀ k ∈ tfin, k ≤ k0 :=
      ⟨tfin.sup id, fun k hk => Finset.le_sup (f := id) hk⟩
    refine ⟨1 / (k0 + 1 : ℝ), by positivity, fun ε hεpos hεlt => ?_⟩
    have hbig : E ⊆ ReducedDomain G Ω R (1 / (k0 + 1 : ℝ)) := by
      intro x hx
      obtain ⟨k, hkt, hxk⟩ := Set.mem_iUnion₂.1 (htfin hx)
      refine hrd3 (1 / (k + 1 : ℝ)) (1 / (k0 + 1 : ℝ)) ?_ hxk
      have hkle : (k : ℝ) ≤ (k0 : ℝ) := by
        have h := hk0 k hkt
        exact_mod_cast h
      exact one_div_le_one_div_of_le (by positivity) (by linarith only [hkle])
    exact fun x hx => hrd3 _ _ hεlt.le (hbig hx)
  -- Step 5(b): the regularizations are `τ/8`-close, by clause 3 of `wang2`
  obtain ⟨hw2u1, -, hw2u3⟩ := hc.wang2 Ω hΩopen hΩbdd u hu
  obtain ⟨hw2v1, -, hw2v3⟩ := hc.wang2 Ω hΩopen hΩbdd v hv
  obtain ⟨εu, hεupos, h5bu0⟩ := hw2u3 (τ / 8) (by linarith only [hτpos])
  obtain ⟨εv, hεvpos, h5bv0⟩ := hw2v3 (τ / 8) (by linarith only [hτpos])
  -- Step 5(c): `∂Ω[ε]` is `ρ₀`-close to `∂Ω` in the quasi-distance, by clause 7
  obtain ⟨εc, hεcpos, h5c0⟩ := hrd7 ρ0 hρ0pos
  -- `ε₁ := min` of the four thresholds
  obtain ⟨ε₁, hε₁pos, hε₁a, hε₁u, hε₁v, hε₁c⟩ : ∃ ε₁ > 0,
      ε₁ ≤ εa ∧ ε₁ ≤ εu ∧ ε₁ ≤ εv ∧ ε₁ ≤ εc :=
    ⟨min (min εa εu) (min εv εc),
      lt_min (lt_min hεapos hεupos) (lt_min hεvpos hεcpos),
      (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  have h5a : ∀ ε : ℝ, 0 < ε → ε < ε₁ → E ⊆ ReducedDomain G Ω R ε := fun ε hp hl =>
    h5a0 ε hp (lt_of_lt_of_le hl hε₁a)
  have h5bu : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ x ∈ closure Ω,
      |SupConv G Ω u ε x - u x| ≤ τ / 8 := fun ε hp hl x hx =>
    (h5bu0 ε hp (lt_of_lt_of_le hl hε₁u) x hx).1
  have h5bv : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ x ∈ closure Ω,
      |InfConv G Ω v ε x - v x| ≤ τ / 8 := fun ε hp hl x hx =>
    (h5bv0 ε hp (lt_of_lt_of_le hl hε₁v) x hx).2
  have h5c : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ z ∈ frontier (ReducedDomain G Ω R ε),
      ∃ w ∈ frontier Ω, G.hnorm (G.mul (-w) z) < ρ0 := fun ε hp hl =>
    h5c0 ε hp (lt_of_lt_of_le hl hε₁c)
  -- Step 8, hoisted: the boundary gap 2(e).  Needed by 2(g) and by Step 10.
  have hgapfr : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ z ∈ frontier (ReducedDomain G Ω R ε),
      SupConv G Ω u ε z - (InfConv G Ω v ε z + τ) ≤ -(τ / 2) := by
    intro ε hεpos hεlt z hz
    have hzclΩ : z ∈ closure Ω := subset_closure (hrd6 ε hεpos hz.1)
    obtain ⟨w, hwfr, hwd⟩ := h5c ε hεpos hεlt z hz
    have hwcl : w ∈ closure Ω := frontier_subset_closure hwfr
    have hgap := h4a z hzclΩ w hwcl hwd
    have hbw := hbdry w hwfr
    have hab1 := abs_le.1 (h5bu ε hεpos hεlt z hzclΩ)
    have hab2 := abs_le.1 (h5bv ε hεpos hεlt z hzclΩ)
    have h1 : u z - u w ≤ |u z - u w| := le_abs_self _
    have h2 : -(v z - v w) ≤ |v z - v w| := neg_le_abs _
    have h3 : (0:ℝ) ≤ |u z - u w| := abs_nonneg _
    have h4 : (0:ℝ) ≤ |v z - v w| := abs_nonneg _
    linarith only [hgap, hbw, hab1.1, hab1.2, hab2.1, hab2.2, h1, h2, h3, h4, hτpos]
  -- Step 9, hoisted: at any maximum point the gap is at least `τ`.  Needed by 2(f), 2(g)
  -- and Step 10.
  have hmaxge : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ z ∈ closure (ReducedDomain G Ω R ε),
      IsMaxOn (fun y => SupConv G Ω u ε y - (InfConv G Ω v ε y + τ))
        (closure (ReducedDomain G Ω R ε)) z →
      τ ≤ SupConv G Ω u ε z - (InfConv G Ω v ε z + τ) := by
    intro ε hεpos hεlt z hzcl hzmax
    obtain ⟨x, hxE⟩ := hEne
    have hxOe : x ∈ ReducedDomain G Ω R ε := h5a ε hεpos hεlt hxE
    have hxcl : x ∈ closure Ω := hEsubcl hxE
    have hval : u x - v x = u xM - v xM := hEval x hxE
    have hu1 := (hw2u1 ε hεpos x hxcl).1
    have hv1 := (hw2v1 ε hεpos x hxcl).2
    have hgex : τ ≤ SupConv G Ω u ε x - (InfConv G Ω v ε x + τ) := by
      linarith only [hu1, hv1, hval, hM2]
    have hle := hzmax (subset_closure hxOe)
    have hle' : SupConv G Ω u ε x - (InfConv G Ω v ε x + τ)
        ≤ SupConv G Ω u ε z - (InfConv G Ω v ε z + τ) := hle
    linarith only [hgex, hle']
  -- Step 9, 2(g), hoisted: every maximum point lies in the open `Ω[ε]`
  have hmaxin : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ z ∈ closure (ReducedDomain G Ω R ε),
      IsMaxOn (fun y => SupConv G Ω u ε y - (InfConv G Ω v ε y + τ))
        (closure (ReducedDomain G Ω R ε)) z → z ∈ ReducedDomain G Ω R ε := by
    intro ε hεpos hεlt z hzcl hzmax
    by_contra hcc
    have hzfr : z ∈ frontier (ReducedDomain G Ω R ε) := by
      rw [(hrd4 ε hεpos).frontier_eq]
      exact ⟨hzcl, hcc⟩
    have h1 := hgapfr ε hεpos hεlt z hzfr
    have h2 := hmaxge ε hεpos hεlt z hzcl hzmax
    linarith only [h1, h2, hτpos]
  refine ⟨hEne, hEcpt, ⟨ε₁, hε₁pos, ?_⟩, ?_⟩
  · -- the ε-block: clauses 2(a)-2(g)
    intro ε hεpos hεlt uE vE huE hvE
    have hOeopen : IsOpen (ReducedDomain G Ω R ε) := hrd4 ε hεpos
    have hOesubΩ : ReducedDomain G Ω R ε ⊆ Ω := hrd1 ε
    have hOeclsubΩ : closure (ReducedDomain G Ω R ε) ⊆ Ω := hrd6 ε hεpos
    have hw1u := (hc.wang1 Ω hΩopen hΩbdd u hu ε hεpos).1
    have hw1v := (hc.wang1 Ω hΩopen hΩbdd v hv ε hεpos).2
    have hw3 := hc.wang3 A H hAH Ω hΩopen hΩbdd u v hu hv R hRb hsub hsup ε hεpos
    have hcu : ContinuousOn (SupConv G Ω u ε) Ω :=
      (SemiConvexLocLipschitz Ω (SupConv G Ω u ε) hw1u).1
    have hcnv : ContinuousOn (fun x => -(InfConv G Ω v ε x)) Ω :=
      (SemiConvexLocLipschitz Ω (fun x => -(InfConv G Ω v ε x)) hw1v).1
    have hcv2 : ContinuousOn (InfConv G Ω v ε) Ω := by
      have h : ContinuousOn (fun x => -(-(InfConv G Ω v ε x))) Ω := hcnv.neg
      simpa only [neg_neg] using h
    refine ⟨h5a ε hεpos hεlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 2(b) for `uE`
      rw [huE]
      exact hcu.mono hOeclsubΩ
    · -- 2(b) for `vE`
      rw [hvE]
      exact (hcv2.add continuousOn_const).mono hOeclsubΩ
    · -- 2(c) for `uE`, by (6a)
      rw [huE]
      exact scRestrict _ _ hOeopen hOesubΩ hw1u
    · -- 2(c) for `-vE`, by (6a) then (6b)
      refine scCongr (fun y => -(InfConv G Ω v ε y) + -τ) (fun y => -(vE y)) _ ?_ ?_
      · intro y
        rw [hvE]
        ring
      · exact scAddConst _ (-τ) _ (scRestrict _ _ hOeopen hOesubΩ hw1v)
    · -- 2(d) sub-solution, from `wang3` on the REDUCED domain (pm-0009)
      rw [huE]
      exact hw3.1
    · -- 2(d) super-solution, `wang3` plus `AddConstPreservesSubsol`
      rw [hvE]
      exact (AddConstPreservesSubsol G A H (ReducedDomain G Ω R ε)
        (InfConv G Ω v ε) τ).2 hw3.2
    · -- 2(e)
      intro z hz
      rw [huE, hvE]
      exact hgapfr ε hεpos hεlt z hz
    · -- 2(f)
      have hcpt : IsCompact (closure (ReducedDomain G Ω R ε)) :=
        (hrd2 ε).isCompact_closure
      obtain ⟨x0, hx0E⟩ := hEne
      have hne : (closure (ReducedDomain G Ω R ε)).Nonempty :=
        ⟨x0, subset_closure (h5a ε hεpos hεlt hx0E)⟩
      have hcont : ContinuousOn (fun y => uE y - vE y)
          (closure (ReducedDomain G Ω R ε)) := by
        rw [huE, hvE]
        exact (hcu.mono hOeclsubΩ).sub ((hcv2.add continuousOn_const).mono hOeclsubΩ)
      obtain ⟨xe, hxecl, hxemax⟩ := hcpt.exists_isMaxOn hne hcont
      have hxemax' : IsMaxOn (fun y => SupConv G Ω u ε y - (InfConv G Ω v ε y + τ))
          (closure (ReducedDomain G Ω R ε)) xe := by
        rw [huE, hvE] at hxemax
        exact hxemax
      refine ⟨xe, hmaxin ε hεpos hεlt xe hxecl hxemax', hxemax, ?_⟩
      have h := hmaxge ε hεpos hεlt xe hxecl hxemax'
      rw [huE, hvE]
      exact h
    · -- 2(g)
      intro z hzcl hzmax
      refine hmaxin ε hεpos hεlt z hzcl ?_
      rw [huE, hvE] at hzmax
      exact hzmax
  · -- Step 10: part 3, the convergence `E_ε → E`
    intro η hη
    by_cases hKempty : ∀ y ∈ closure Ω, ∃ p ∈ E, G.hnorm (G.mul (-p) y) < η
    · refine ⟨ε₁, hε₁pos, fun ε hεpos hεlt z hz _ => ?_⟩
      exact hKempty z (subset_closure (hrd1 ε hz))
    · push Not at hKempty
      obtain ⟨y0, hy0cl, hy0⟩ := hKempty
      -- (10a) `K_η` is a non-empty compact subset of `closure Ω`, disjoint from `E`
      obtain ⟨K, hKdef⟩ : ∃ K : Set (EuclideanSpace ℝ (Fin G.n)),
          K = closure Ω ∩ ⋂ p ∈ E, {y : EuclideanSpace ℝ (Fin G.n) |
            η ≤ G.hnorm (G.mul (-p) y)} := ⟨_, rfl⟩
      have hKmem : ∀ y : EuclideanSpace ℝ (Fin G.n),
          y ∈ K ↔ (y ∈ closure Ω ∧ ∀ p ∈ E, η ≤ G.hnorm (G.mul (-p) y)) := by
        intro y
        rw [hKdef]
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      have hKne : K.Nonempty := ⟨y0, (hKmem y0).2 ⟨hy0cl, hy0⟩⟩
      have hKsubcl : K ⊆ closure Ω := fun y hy => ((hKmem y).1 hy).1
      have hKcpt : IsCompact K := by
        refine hclcpt.of_isClosed_subset ?_ hKsubcl
        rw [hKdef]
        refine isClosed_closure.inter (isClosed_biInter fun p _ => ?_)
        have hcp : Continuous fun y : EuclideanSpace ℝ (Fin G.n) => G.hnorm (G.mul (-p) y) :=
          G.hnorm_cont.comp (G.mul_smooth.continuous.comp
            (continuous_const.prodMk continuous_id))
        exact isClosed_le continuous_const hcp
      -- (10b) `β := max_{K_η} (u - v - τ) < τ`
      have hcontK : ContinuousOn (fun y => u y - v y - τ) K :=
        (((hu.sub hv).mono hKsubcl).sub continuousOn_const)
      obtain ⟨yb, hybK, hybmax⟩ := hKcpt.exists_isMaxOn hKne hcontK
      have hβlt : u yb - v yb - τ < τ := by
        have hybcl : yb ∈ closure Ω := hKsubcl hybK
        have hnotE : yb ∉ E := by
          intro hc
          have h := ((hKmem yb).1 hybK).2 yb hc
          rw [G.neg_mul, (G.hnorm_eq_zero 0).2 rfl] at h
          linarith only [h, hη]
        have hlt : u yb - v yb < u xM - v xM := by
          by_contra hcc
          rw [not_lt] at hcc
          exact hnotE ((h2a yb).2 ⟨hybcl, hcc⟩)
        linarith only [hlt, hM2]
      -- (10c) `θ := (τ - β)/3` and the final threshold
      obtain ⟨εu3, hεu3pos, hbu3⟩ := hw2u3 ((τ - (u yb - v yb - τ)) / 3)
        (by linarith only [hβlt])
      obtain ⟨εv3, hεv3pos, hbv3⟩ := hw2v3 ((τ - (u yb - v yb - τ)) / 3)
        (by linarith only [hβlt])
      refine ⟨min ε₁ (min εu3 εv3),
        lt_min hε₁pos (lt_min hεu3pos hεv3pos), fun ε hεpos hεlt z hz hzmax => ?_⟩
      have hεlt1 : ε < ε₁ := lt_of_lt_of_le hεlt (min_le_left _ _)
      have hεltu : ε < εu3 := lt_of_lt_of_le hεlt ((min_le_right _ _).trans (min_le_left _ _))
      have hεltv : ε < εv3 := lt_of_lt_of_le hεlt ((min_le_right _ _).trans (min_le_right _ _))
      have hzcl : z ∈ closure Ω := subset_closure (hrd1 ε hz)
      -- the gap at `z` is at least `τ`, so `z ∉ K_η` by (10d)
      have hzge := hmaxge ε hεpos hεlt1 z (subset_closure hz) hzmax
      have hznotK : z ∉ K := by
        intro hcc
        have hbz := hybmax hcc
        have hbz' : u z - v z - τ ≤ u yb - v yb - τ := hbz
        have hab1 := abs_le.1 ((hbu3 ε hεpos hεltu z hzcl).1)
        have hab2 := abs_le.1 ((hbv3 ε hεpos hεltv z hzcl).2)
        linarith only [hzge, hbz', hab1.1, hab1.2, hab2.1, hab2.2, hβlt]
      -- so the failing condition is the second one
      by_contra hcc
      push Not at hcc
      exact hznotK ((hKmem z).2 ⟨hzcl, hcc⟩)
