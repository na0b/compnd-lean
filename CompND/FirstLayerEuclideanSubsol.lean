import CompND.IsViscSubsol
import CompND.IsViscSupersol
import Mathlib.Analysis.Normed.Operator.Banach

/-- The operator transfer of thm:uncond(iii): if `u = F ∘ π₁` is a viscosity sub-solution and
`v = Gf ∘ π₁` a viscosity super-solution of `ℒ · = 0` in `Ω`, then on the first-layer image
`Ω' = π₁(Ω) ⊆ ℝᵐ` --- open and bounded, with `∂Ω' ⊆ π₁(∂Ω)` --- the functions `F` and `Gf`
are a pair of sub- and super-solutions for the Euclidean operator
`ψ ↦ -Tr(A(∇ψ) D²ψ) + H(∇ψ)` built from the same `A` and `H`, written out inline on
`ℝᵐ`. -/
theorem FirstLayerEuclideanSubsol (G : CarnotSetting)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (F Gf : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (hFcont : ContinuousOn F (G.pi1 '' closure Ω))
    (hGfcont : ContinuousOn Gf (G.pi1 '' closure Ω))
    (hsub : IsViscSubsol G A H Ω (fun x => F (G.pi1 x)))
    (hsup : IsViscSupersol G A H Ω (fun x => Gf (G.pi1 x)))
    (hbdry : ∀ x ∈ frontier Ω, F (G.pi1 x) ≤ Gf (G.pi1 x)) :
    IsOpen (G.pi1 '' Ω) ∧
    Bornology.IsBounded (G.pi1 '' Ω) ∧
    closure (G.pi1 '' Ω) ⊆ G.pi1 '' closure Ω ∧
    frontier (G.pi1 '' Ω) ⊆ G.pi1 '' frontier Ω ∧
    (∀ ζ ∈ frontier (G.pi1 '' Ω), F ζ ≤ Gf ζ) ∧
    ContinuousOn F (closure (G.pi1 '' Ω)) ∧
    ContinuousOn Gf (closure (G.pi1 '' Ω)) ∧
    (∀ ζ ∈ G.pi1 '' Ω, ∀ ψ : EuclideanSpace ℝ (Fin G.m) → ℝ,
      ContDiffOn ℝ 2 ψ (G.pi1 '' Ω) →
      IsMaxOn (fun w => F w - ψ w) (G.pi1 '' Ω) ζ →
      ∀ (E : EuclideanSpace ℝ (Fin G.m) →L[ℝ] ℝ)
        (C : EuclideanSpace ℝ (Fin G.m) →L[ℝ] EuclideanSpace ℝ (Fin G.m) →L[ℝ] ℝ),
      TwiceDiffAt ψ ζ E C →
      ∀ ξ : EuclideanSpace ℝ (Fin G.m),
        ξ = (EuclideanSpace.equiv (Fin G.m) ℝ).symm
              (fun i => E (EuclideanSpace.single i (1 : ℝ))) →
        ξ ≠ 0 →
        -(A ξ * Matrix.of (fun i j =>
            C (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))).trace
          + H ξ ≤ 0) ∧
    (∀ ζ ∈ G.pi1 '' Ω, ∀ ψ : EuclideanSpace ℝ (Fin G.m) → ℝ,
      ContDiffOn ℝ 2 ψ (G.pi1 '' Ω) →
      IsMinOn (fun w => Gf w - ψ w) (G.pi1 '' Ω) ζ →
      ∀ (E : EuclideanSpace ℝ (Fin G.m) →L[ℝ] ℝ)
        (C : EuclideanSpace ℝ (Fin G.m) →L[ℝ] EuclideanSpace ℝ (Fin G.m) →L[ℝ] ℝ),
      TwiceDiffAt ψ ζ E C →
      ∀ ξ : EuclideanSpace ℝ (Fin G.m),
        ξ = (EuclideanSpace.equiv (Fin G.m) ℝ).symm
              (fun i => E (EuclideanSpace.single i (1 : ℝ))) →
        ξ ≠ 0 →
        0 ≤ -(A ξ * Matrix.of (fun i j =>
            C (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))).trace
          + H ξ) := by
  have hΩcl : IsCompact (closure Ω) := hΩbdd.isCompact_closure
  have hpi1img : IsCompact (G.pi1 '' closure Ω) := hΩcl.image G.pi1.continuous
  have himg : G.pi1 '' Ω ⊆ G.pi1 '' closure Ω := Set.image_mono subset_closure
  -- ===== Step 1: `π₁` is surjective, hence open; conjuncts (1) and (2) =====
  have h1 : IsOpen (G.pi1 '' Ω) := by
    have hsurj : Function.Surjective G.pi1 := fun ζ => ⟨G.hexp ζ, G.pi1_hexp ζ⟩
    exact (ContinuousLinearMap.isOpenMap G.pi1 hsurj) Ω hΩopen
  have h2 : Bornology.IsBounded (G.pi1 '' Ω) := hpi1img.isBounded.subset himg
  -- ===== Step 2: conjunct (3), and (6)/(7) from it =====
  have h3 : closure (G.pi1 '' Ω) ⊆ G.pi1 '' closure Ω :=
    hpi1img.isClosed.closure_subset_iff.2 himg
  -- ===== Step 3: conjunct (4), the limit-point argument =====
  have h4 : frontier (G.pi1 '' Ω) ⊆ G.pi1 '' frontier Ω := by
    intro ζ hζ
    rw [h1.frontier_eq] at hζ
    obtain ⟨hζcl, hζnot⟩ := hζ
    obtain ⟨z, hzmem, hztend⟩ := mem_closure_iff_seq_limit.1 hζcl
    choose xs hxsΩ hxseq using hzmem
    obtain ⟨xbar, hxbar, φ, hφ, hφtend⟩ :=
      hΩcl.tendsto_subseq (fun n => subset_closure (hxsΩ n))
    have hpt : G.pi1 xbar = ζ := by
      have t1 : Filter.Tendsto (fun j => G.pi1 (xs (φ j))) Filter.atTop
          (nhds (G.pi1 xbar)) := (G.pi1.continuous.tendsto xbar).comp hφtend
      have t2 : Filter.Tendsto (fun j => G.pi1 (xs (φ j))) Filter.atTop (nhds ζ) := by
        refine Filter.Tendsto.congr' ?_ (hztend.comp hφ.tendsto_atTop)
        exact Filter.Eventually.of_forall fun j => (hxseq (φ j)).symm
      exact tendsto_nhds_unique t1 t2
    have hxbarnot : xbar ∉ Ω := fun hm => hζnot ⟨xbar, hm, hpt⟩
    refine ⟨xbar, ?_, hpt⟩
    rw [hΩopen.frontier_eq]
    exact ⟨hxbar, hxbarnot⟩
  -- ===== Step 4: conjunct (5) =====
  have h5 : ∀ ζ ∈ frontier (G.pi1 '' Ω), F ζ ≤ Gf ζ := by
    intro ζ hζ
    obtain ⟨x, hx, hxpt⟩ := h4 hζ
    have hb := hbdry x hx
    rwa [hxpt] at hb
  have h6 : ContinuousOn F (closure (G.pi1 '' Ω)) := hFcont.mono h3
  have h7 : ContinuousOn Gf (closure (G.pi1 '' Ω)) := hGfcont.mono h3
  -- (5a), shared by Steps 5 and 6: `φ = ψ ∘ π₁` is `C²` on `Ω`
  have hphiC : ∀ ψ : EuclideanSpace ℝ (Fin G.m) → ℝ, ContDiffOn ℝ 2 ψ (G.pi1 '' Ω) →
      ContDiffOn ℝ 2 (fun y => ψ (G.pi1 y)) Ω :=
    fun ψ hψ => hψ.comp G.pi1.contDiff.contDiffOn fun y hy => ⟨y, hy, rfl⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · -- ===== Step 5: conjunct (7) =====
    intro ζ hζ ψ hψ hmax E C hEC ξ hξ hξne
    subst hξ
    obtain ⟨x, hxΩ, hxpt⟩ := hζ
    -- (5c): `pi1Jet` delivers the statement's two shapes verbatim
    obtain ⟨D, B, hDB, hgD, hhB⟩ := G.pi1Jet ψ x E C (by rw [hxpt]; exact hEC)
    -- (5b): maximality over `Ω'` pulls back to maximality over ALL of `Ω` (pm-0009 is free here)
    have hmaxΩ : IsMaxOn (fun y => F (G.pi1 y) - ψ (G.pi1 y)) Ω x := by
      refine isMaxOn_iff.2 fun y hy => ?_
      have h := isMaxOn_iff.1 hmax (G.pi1 y) ⟨y, hy, rfl⟩
      show F (G.pi1 y) - ψ (G.pi1 y) ≤ F (G.pi1 x) - ψ (G.pi1 x)
      rw [hxpt]
      exact h
    have hgne : hgrad G.sig x D ≠ 0 := by rw [hgD]; exact hξne
    -- (5d)
    have hle := hsub.2 x hxΩ (fun y => ψ (G.pi1 y)) (hphiC ψ hψ) hmaxΩ D B hDB hgne
    simp only [Lop] at hle
    rw [hgD, hhB] at hle
    exact hle
  · -- ===== Step 6: conjunct (8), the mirror =====
    intro ζ hζ ψ hψ hmin E C hEC ξ hξ hξne
    subst hξ
    obtain ⟨x, hxΩ, hxpt⟩ := hζ
    obtain ⟨D, B, hDB, hgD, hhB⟩ := G.pi1Jet ψ x E C (by rw [hxpt]; exact hEC)
    have hminΩ : IsMinOn (fun y => Gf (G.pi1 y) - ψ (G.pi1 y)) Ω x := by
      refine isMinOn_iff.2 fun y hy => ?_
      have h := isMinOn_iff.1 hmin (G.pi1 y) ⟨y, hy, rfl⟩
      show Gf (G.pi1 x) - ψ (G.pi1 x) ≤ Gf (G.pi1 y) - ψ (G.pi1 y)
      rw [hxpt]
      exact h
    have hgne : hgrad G.sig x D ≠ 0 := by rw [hgD]; exact hξne
    have hge := hsup.2 x hxΩ (fun y => ψ (G.pi1 y)) (hphiC ψ hψ) hminΩ D B hDB hgne
    simp only [Lop] at hge
    rw [hgD, hhB] at hge
    exact hge
