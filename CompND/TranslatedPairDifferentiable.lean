import CompND.InnerDomainProperties
import CompND.SemiConvexCompose
import CompND.SemiConvexDiffAtMax

/-- The sentence following eq:MAl: for `‖h‖ < δ` the right translate `u_h = u (· * h)` is
locally semi-convex on the inner domain `Ω_δ`, so at every point of `A_δ(h)` both `u_h` and
`v` are differentiable with the same derivative, and `u` itself is differentiable at
`x * h`. -/
theorem TranslatedPairDifferentiable (G : CarnotSetting)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (husc : LocallySemiConvexOn Ω u) (hvsc : LocallySemiConvexOn Ω (fun y => -v y))
    (δ : ℝ) (hδ : 0 < δ) (h : EuclideanSpace ℝ (Fin G.n)) (hh : G.hnorm h < δ) :
    (∀ x ∈ TranslatedDomain G Ω δ, G.mul x h ∈ Ω) ∧
    LocallySemiConvexOn (TranslatedDomain G Ω δ) (fun y => u (G.mul y h)) ∧
    LocallySemiConvexOn (TranslatedDomain G Ω δ) (fun y => -v y) ∧
    (∀ x ∈ TranslatedDomain G Ω δ,
      IsMaxOn (fun y => u (G.mul y h) - v y) (TranslatedDomain G Ω δ) x →
        (∃ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
          HasFDerivAt (fun y => u (G.mul y h)) D x ∧ HasFDerivAt v D x) ∧
        (∃ D' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ, HasFDerivAt u D' (G.mul x h))) := by
  -- ===== Step 0: local semi-convexity restricts to open subsets.  The ambient set is a
  -- parameter, because this is used below at `T := Θ⁻¹(Ω)` and at `T := Ω`. =====
  have scRestrict : ∀ (f : EuclideanSpace ℝ (Fin G.n) → ℝ)
      (T V : Set (EuclideanSpace ℝ (Fin G.n))), IsOpen V → V ⊆ T →
      LocallySemiConvexOn T f → LocallySemiConvexOn V f := by
    intro f T V hVopen hVsub hf x hx
    obtain ⟨ρ, hρ, Λ, hΛ, hball, hcv⟩ := hf x (hVsub hx)
    obtain ⟨σ, hσ, hσball⟩ := Metric.isOpen_iff.1 hVopen x hx
    refine ⟨min ρ σ, lt_min hρ hσ, Λ, hΛ,
      (Metric.ball_subset_ball (min_le_right _ _)).trans hσball, ?_⟩
    exact hcv.subset (Metric.ball_subset_ball (min_le_left _ _)) (convex_ball x _)
  obtain ⟨hidp1, -, hidp3, -, -, hidp6, -⟩ := InnerDomainProperties G Ω hΩopen hΩbdd
  -- ===== Step 1: part (1).  eq:righttrans (pm-0012) plus item (6). =====
  have hstep1 : ∀ x ∈ TranslatedDomain G Ω δ, G.mul x h ∈ Ω := by
    intro x hx
    refine hidp6 δ hδ x hx ?_
    show G.hnorm (G.mul (-x) (G.mul x h)) < δ
    rw [← G.mul_assoc, G.neg_mul, G.zero_mul]
    exact hh
  -- ===== Step 2: part (2).  `SemiConvexCompose` clause 2, then Step 0. =====
  have hΘsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin G.n) => G.mul y h) :=
    G.mul_smooth.comp (contDiff_id.prodMk contDiff_const)
  have hΘ2 : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin G.n) => G.mul y h) :=
    hΘsmooth.of_le (WithTop.coe_le_coe.2 (OrderTop.le_top _))
  have hpre : LocallySemiConvexOn
      ((fun y : EuclideanSpace ℝ (Fin G.n) => G.mul y h) ⁻¹' Ω)
      (fun y => u (G.mul y h)) := (SemiConvexCompose Ω u husc).2 _ hΘ2
  have hstep2 : LocallySemiConvexOn (TranslatedDomain G Ω δ) (fun y => u (G.mul y h)) :=
    scRestrict _ _ _ (hidp3 δ) (fun x hx => hstep1 x hx) hpre
  -- ===== Step 3: part (3).  Step 0 again, with `T := Ω`. =====
  have hstep3 : LocallySemiConvexOn (TranslatedDomain G Ω δ) (fun y => -v y) :=
    scRestrict _ _ _ (hidp3 δ) (hidp1 δ) hvsc
  refine ⟨hstep1, hstep2, hstep3, ?_⟩
  intro x hx hxmax
  -- ===== Step 4: part (4), the common derivative.  `SemiConvexDiffAtMax` clause 2, with
  -- the maximum taken over exactly the set carrying the semi-convexity. =====
  obtain ⟨D, hDu, hDv⟩ :=
    (SemiConvexDiffAtMax (TranslatedDomain G Ω δ) (fun y => u (G.mul y h)) v
      hstep2 hstep3).2 x hx hxmax
  refine ⟨⟨D, hDu, hDv⟩, ?_⟩
  -- ===== Step 5: part (4), differentiability of `u` at `x * h` via `u = u_h ∘ Θ'`. =====
  have hcomp : ∀ z : EuclideanSpace ℝ (Fin G.n), u (G.mul (G.mul z (-h)) h) = u z := by
    intro z
    rw [G.mul_assoc, G.neg_mul, G.mul_zero]
  have hΘ'pt : G.mul (G.mul x h) (-h) = x := by
    rw [G.mul_assoc, G.mul_neg, G.mul_zero]
  have hΘ'smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin G.n) => G.mul z (-h)) :=
    G.mul_smooth.comp (contDiff_id.prodMk contDiff_const)
  have hL : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin G.n) => G.mul z (-h))
      (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin G.n) => G.mul z (-h)) (G.mul x h))
      (G.mul x h) :=
    ((hΘ'smooth.differentiable (by simp)) (G.mul x h)).hasFDerivAt
  have hDu' : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin G.n) => u (G.mul y h)) D
      ((fun z : EuclideanSpace ℝ (Fin G.n) => G.mul z (-h)) (G.mul x h)) := by
    show HasFDerivAt (fun y : EuclideanSpace ℝ (Fin G.n) => u (G.mul y h)) D
      (G.mul (G.mul x h) (-h))
    rw [hΘ'pt]
    exact hDu
  have hchain := hDu'.comp (G.mul x h) hL
  refine ⟨D.comp (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin G.n) => G.mul z (-h))
    (G.mul x h)), ?_⟩
  exact hchain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => (hcomp z).symm)
