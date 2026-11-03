import CompND.ComparisonAbelian
import CompND.EuclidFirstLayerComparison
import CompND.FirstLayerEuclideanSubsol

/-- thm:uncond(iii), both disjuncts as printed: comparison holds when the step is `r = 1`,
and more generally when `u = F ∘ π₁` and `v = Gf ∘ π₁` depend only on the first layer. The
descent to `ℝᵐ` applies the cited results inside the Euclidean setting on `ℝᵐ`, so they are
assumed there too, as the second hypothesis `hcE`, alongside the cited results at `G`. -/
theorem UncondCaseFirstLayer (G : CarnotSetting) (hc : CitedResults G)
    (hcE : CitedResults (EuclidSetting G.m))
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (hAH : StructureConditionsES G.m A H)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hΩne : ∃ y : EuclideanSpace ℝ (Fin G.n), y ∉ Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (hsub : IsViscSubsol G A H Ω u) (hsup : IsViscSupersol G A H Ω v)
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x)
    (R : ℝ) (hR : 0 ≤ R)
    (hRb : ∀ x ∈ closure Ω, |u x| ≤ R / 2 ∧ |v x| ≤ R / 2) :
    (G.r = 1 → ∀ x ∈ Ω, u x ≤ v x) ∧
    ((∃ F Gf : EuclideanSpace ℝ (Fin G.m) → ℝ,
        ContinuousOn F (G.pi1 '' closure Ω) ∧
        ContinuousOn Gf (G.pi1 '' closure Ω) ∧
        u = (fun x => F (G.pi1 x)) ∧ v = (fun x => Gf (G.pi1 x))) →
      ∀ x ∈ Ω, u x ≤ v x) := by
  -- ===== (2a): if the first layer is trivial then the whole space is a point, so `Ω = ∅` =====
  -- `LieHull` is an `⋂₀` over families containing each frame field and closed under the
  -- bracket; with `Fin G.m` empty both conditions hold for `S := ∅`, so `∅` is in the
  -- indexing family and `LieHull G.sig = ∅`.  Hörmander's condition then reads `⊥ = ⊤`.
  have hmzero : G.m = 0 → ∀ x : EuclideanSpace ℝ (Fin G.n), x ∉ Ω := by
    intro hm0
    have hLie : LieHull G.sig
        = (∅ : Set (EuclideanSpace ℝ (Fin G.n) → EuclideanSpace ℝ (Fin G.n))) := by
      refine Set.eq_empty_of_subset_empty ?_
      refine Set.sInter_subset_of_mem ?_
      exact ⟨fun i => absurd i.isLt (by omega), fun V hV W _ => absurd hV (Set.notMem_empty V)⟩
    have hspan := G.hormander (0 : EuclideanSpace ℝ (Fin G.n))
    rw [hLie, Set.image_empty, Submodule.span_empty] at hspan
    have hall : ∀ z : EuclideanSpace ℝ (Fin G.n), z = 0 := by
      intro z
      have hz : z ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin G.n))) := by
        rw [hspan]
        exact Submodule.mem_top
      exact (Submodule.mem_bot ℝ).1 hz
    obtain ⟨y, hy⟩ := hΩne
    intro x hx
    refine hy ?_
    rw [hall y, ← hall x]
    exact hx
  refine ⟨?_, ?_⟩
  · -- ===== Part (1): the step-one case, straight to the abelian engine at `G` =====
    intro hr
    exact ComparisonAbelian G hc (G.abelian_of_step_one hr) A H hAH Ω hΩopen hΩbdd hΩne
      u v hucont hvcont hsub hsup hbdry R hR hRb
  · -- ===== Part (2): the first-layer case, via the descent to `ℝᵐ` =====
    rintro ⟨F, Gf, hFcont, hGfcont, huF, hvG⟩
    subst huF
    subst hvG
    rcases Nat.eq_zero_or_pos G.m with hm0 | hmpos
    · -- `Ω` is empty, so there is nothing to prove
      exact fun x hx => absurd hx (hmzero hm0 x)
    -- (2b): the operator transfer to `Ω' = π₁(Ω)`
    obtain ⟨hO1, hO2, hO3, -, hO5, hO6, hO7, hO8, hO9⟩ :=
      FirstLayerEuclideanSubsol G A H Ω hΩopen hΩbdd F Gf hFcont hGfcont hsub hsup hbdry
    -- (2c): `ℝᵐ` is unbounded for `m ≥ 1`, so the bounded `Ω'` is not all of it
    have hne' : ∃ ζ : EuclideanSpace ℝ (Fin G.m), ζ ∉ G.pi1 '' Ω := by
      obtain ⟨Cb, hCb⟩ := hO2.subset_closedBall (0 : EuclideanSpace ℝ (Fin G.m))
      have hns : ‖EuclideanSpace.single (⟨0, hmpos⟩ : Fin G.m) (1 : ℝ)‖ = 1 := by simp
      refine ⟨(max Cb 0 + 1) • EuclideanSpace.single (⟨0, hmpos⟩ : Fin G.m) (1 : ℝ),
        fun hmem => ?_⟩
      have h := hCb hmem
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, hns, mul_one,
        abs_of_pos (by positivity : (0:ℝ) < max Cb 0 + 1)] at h
      have h2 : Cb ≤ max Cb 0 := le_max_left _ _
      linarith
    -- (2d): the `R/2` bounds descend through conjunct (3)
    have hRb' : ∀ ζ ∈ closure (G.pi1 '' Ω), |F ζ| ≤ R / 2 ∧ |Gf ζ| ≤ R / 2 := by
      intro ζ hζ
      obtain ⟨x₀, hx₀, hx₀pt⟩ := hO3 hζ
      have h : |F (G.pi1 x₀)| ≤ R / 2 ∧ |Gf (G.pi1 x₀)| ≤ R / 2 := hRb x₀ hx₀
      rw [hx₀pt] at h
      exact h
    -- (2e): the Euclidean comparison on `Ω'`, with the cited results AT `EuclidSetting G.m`
    have hcmp := EuclidFirstLayerComparison G.m hcE A H hAH (G.pi1 '' Ω) hO1 hO2 hne'
      F Gf hO6 hO7 hO5 R hR hRb' hO8 hO9
    -- (2f): the descent
    intro x hx
    exact hcmp (G.pi1 x) ⟨x, hx, rfl⟩
