import CompND.ComparisonAbelian
import CompND.EuclidSetting

/-- The paper's "by the case `r = 1` applied in `ℝᵐ`": comparison for the Euclidean operator
`ψ ↦ -Tr(A(∇ψ) D²ψ) + H(∇ψ)` on a bounded open `Ω' ⊆ ℝᵐ`, stated with the viscosity
conditions written out inline and with no Carnot setting among the data. The one setting the
statement does name is the Euclidean one on `ℝᵐ`, and only to say where the cited results are
assumed: `EuclidSetting m` is a Carnot group, so assuming the cited results there is
satisfiable, whereas assuming them at every instance of the axiomatization would not be. -/
theorem EuclidFirstLayerComparison (m : ℕ) (hcE : CitedResults (EuclidSetting m))
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ)
    (hAH : StructureConditionsES m A H)
    (Ω' : Set (EuclideanSpace ℝ (Fin m)))
    (hΩopen : IsOpen Ω') (hΩbdd : Bornology.IsBounded Ω')
    (hΩne : ∃ ζ : EuclideanSpace ℝ (Fin m), ζ ∉ Ω')
    (F Gf : EuclideanSpace ℝ (Fin m) → ℝ)
    (hFcont : ContinuousOn F (closure Ω')) (hGfcont : ContinuousOn Gf (closure Ω'))
    (hbdry : ∀ ζ ∈ frontier Ω', F ζ ≤ Gf ζ)
    (R : ℝ) (hR : 0 ≤ R)
    (hRb : ∀ ζ ∈ closure Ω', |F ζ| ≤ R / 2 ∧ |Gf ζ| ≤ R / 2)
    (hFsub : ∀ ζ ∈ Ω', ∀ ψ : EuclideanSpace ℝ (Fin m) → ℝ,
      ContDiffOn ℝ 2 ψ Ω' → IsMaxOn (fun w => F w - ψ w) Ω' ζ →
      ∀ (E : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
        (C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ),
      TwiceDiffAt ψ ζ E C →
      ∀ ξ : EuclideanSpace ℝ (Fin m),
        ξ = (EuclideanSpace.equiv (Fin m) ℝ).symm
              (fun i => E (EuclideanSpace.single i (1 : ℝ))) →
        ξ ≠ 0 →
        -(A ξ * Matrix.of (fun i j =>
            C (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))).trace
          + H ξ ≤ 0)
    (hGfsup : ∀ ζ ∈ Ω', ∀ ψ : EuclideanSpace ℝ (Fin m) → ℝ,
      ContDiffOn ℝ 2 ψ Ω' → IsMinOn (fun w => Gf w - ψ w) Ω' ζ →
      ∀ (E : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
        (C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ),
      TwiceDiffAt ψ ζ E C →
      ∀ ξ : EuclideanSpace ℝ (Fin m),
        ξ = (EuclideanSpace.equiv (Fin m) ℝ).symm
              (fun i => E (EuclideanSpace.single i (1 : ℝ))) →
        ξ ≠ 0 →
        0 ≤ -(A ξ * Matrix.of (fun i j =>
            C (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))).trace
          + H ξ) :
    ∀ ζ ∈ Ω', F ζ ≤ Gf ζ := by
  -- ===== Step 1: the Euclidean setting, and the single transport along `m_E = m` =====
  -- `G` is made opaque first, so that the only cast in the node -- the index-set equality
  -- `m_E = m` -- is discharged once by `subst`.  pm-0010: no `subst` on the topological
  -- dimension, and `pi1` is never assumed to be the identity.
  obtain ⟨G, hGdef⟩ : ∃ G : CarnotSetting, EuclidSetting m = G := ⟨_, rfl⟩
  rw [hGdef] at hcE
  obtain ⟨-, hmm, -, hmul, hnormE, hexppi, hsig⟩ :
      G.n = m ∧ G.m = m ∧ G.r = 1 ∧ (∀ x y, G.mul x y = x + y) ∧
      (∀ x, G.hnorm x = ‖x‖) ∧ (∀ x, G.hexp (G.pi1 x) = x) ∧
      (∀ x i, G.sig x i = G.hexp (EuclideanSpace.single i (1 : ℝ))) := by
    rw [← hGdef]
    exact (EuclideanCarnotSettingExists m).choose_spec
  clear hGdef
  subst hmm
  -- ===== Step 2: `hexp` and `pi1` are mutually inverse linear isometries =====
  have hinj : Function.Injective G.pi1 := by
    intro x y hxy
    rw [← hexppi x, ← hexppi y, hxy]
  obtain ⟨hexpL, hexpLapp⟩ :
      ∃ L : EuclideanSpace ℝ (Fin G.m) →L[ℝ] EuclideanSpace ℝ (Fin G.n),
        ∀ ζ, L ζ = G.hexp ζ := by
    have hker : (G.pi1 : EuclideanSpace ℝ (Fin G.n) →L[ℝ] _).ker = ⊥ :=
      LinearMap.ker_eq_bot.2 hinj
    have hran : (G.pi1 : EuclideanSpace ℝ (Fin G.n) →L[ℝ] _).range = ⊤ :=
      LinearMap.range_eq_top.2 fun ζ => ⟨G.hexp ζ, G.pi1_hexp ζ⟩
    refine ⟨(ContinuousLinearEquiv.ofBijective G.pi1 hker hran).symm, fun ζ => ?_⟩
    refine hinj ?_
    rw [G.pi1_hexp]
    exact ContinuousLinearEquiv.ofBijective_apply_symm_apply G.pi1 hker hran ζ
  have hsubL : ∀ a b : EuclideanSpace ℝ (Fin G.m),
      G.hexp (a - b) = G.hexp a - G.hexp b := by
    intro a b
    refine hinj ?_
    rw [G.pi1_hexp, map_sub, G.pi1_hexp, G.pi1_hexp]
  -- display (2): the isometry
  have hiso : ∀ ζ : EuclideanSpace ℝ (Fin G.m), ‖G.hexp ζ‖ = ‖ζ‖ := by
    intro ζ
    rw [← hnormE (G.hexp ζ), G.hnorm_hexp]
  have hexpcd : ContDiff ℝ 2 (fun w : EuclideanSpace ℝ (Fin G.m) => G.hexp w) := by
    have h : (fun w : EuclideanSpace ℝ (Fin G.m) => G.hexp w) = fun w => hexpL w :=
      funext fun w => (hexpLapp w).symm
    rw [h]
    exact hexpL.contDiff
  -- ===== Step 3: the transported domain and functions =====
  -- display (3)
  have hΩeq : G.hexp '' Ω' = G.pi1 ⁻¹' Ω' := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨ζ, hζ, rfl⟩
      show G.pi1 (G.hexp ζ) ∈ Ω'
      rw [G.pi1_hexp]
      exact hζ
    · intro z hz
      exact ⟨G.pi1 z, hz, hexppi z⟩
  have hΩ''open : IsOpen (G.hexp '' Ω') := by
    rw [hΩeq]
    exact hΩopen.preimage G.pi1.continuous
  have hΩ''bdd : Bornology.IsBounded (G.hexp '' Ω') := by
    obtain ⟨Cb, hCb⟩ := hΩbdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin G.m))
    have hball : Bornology.IsBounded
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin G.n)) Cb) := Metric.isBounded_closedBall
    refine hball.subset ?_
    rintro z ⟨ζ, hζ, rfl⟩
    have h := hCb hζ
    rw [Metric.mem_closedBall, dist_zero_right] at h
    rw [Metric.mem_closedBall, dist_zero_right, hiso]
    exact h
  have hΩ''ne : ∃ z : EuclideanSpace ℝ (Fin G.n), z ∉ G.hexp '' Ω' := by
    obtain ⟨ζ₀, hζ₀⟩ := hΩne
    refine ⟨G.hexp ζ₀, ?_⟩
    rw [hΩeq]
    intro hm
    have : G.pi1 (G.hexp ζ₀) ∈ Ω' := hm
    rw [G.pi1_hexp] at this
    exact hζ₀ this
  have hcl : ∀ z ∈ closure (G.hexp '' Ω'), G.pi1 z ∈ closure Ω' := by
    intro z hz
    rw [hΩeq] at hz
    exact G.pi1.continuous.closure_preimage_subset Ω' hz
  have hfr : ∀ z ∈ frontier (G.hexp '' Ω'), G.pi1 z ∈ frontier Ω' := by
    intro z hz
    rw [hΩ''open.frontier_eq] at hz
    rw [hΩopen.frontier_eq]
    refine ⟨hcl z hz.1, ?_⟩
    intro hmem
    exact hz.2 (by rw [hΩeq]; exact hmem)
  have hUcont : ContinuousOn (fun z => F (G.pi1 z)) (closure (G.hexp '' Ω')) :=
    hFcont.comp G.pi1.continuous.continuousOn hcl
  have hVcont : ContinuousOn (fun z => Gf (G.pi1 z)) (closure (G.hexp '' Ω')) :=
    hGfcont.comp G.pi1.continuous.continuousOn hcl
  have hab : ∀ x y : EuclideanSpace ℝ (Fin G.n), G.mul x y = G.mul y x := by
    intro x y
    rw [hmul, hmul, add_comm]
  -- ===== Step 4 and Step 5(c): the jet package, written once for both directions =====
  have hM : ∀ (z : EuclideanSpace ℝ (Fin G.n)) (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      Mfield G.sig z D = 0 := by
    intro z D
    have hd : ∀ k : Fin G.m,
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin G.n) => G.sig y k) z = 0 := by
      intro k
      rw [show (fun y : EuclideanSpace ℝ (Fin G.n) => G.sig y k)
          = fun _ : EuclideanSpace ℝ (Fin G.n) => G.hexp (EuclideanSpace.single k (1 : ℝ)) from
        funext fun y => hsig y k]
      exact fderiv_const_apply _
    ext i j
    simp only [Mfield, Matrix.of_apply, Matrix.zero_apply, hd i, hd j,
      zero_apply, map_zero]
    ring
  have hpack : ∀ (φ : EuclideanSpace ℝ (Fin G.n) → ℝ) (z : EuclideanSpace ℝ (Fin G.n))
      (ζ : EuclideanSpace ℝ (Fin G.m)), G.hexp ζ = z →
      ∀ (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
        TwiceDiffAt φ z D B →
      ∃ (E : EuclideanSpace ℝ (Fin G.m) →L[ℝ] ℝ)
        (C : EuclideanSpace ℝ (Fin G.m) →L[ℝ] EuclideanSpace ℝ (Fin G.m) →L[ℝ] ℝ),
        TwiceDiffAt (fun w => φ (G.hexp w)) ζ E C ∧
        hgrad G.sig z D = (EuclideanSpace.equiv (Fin G.m) ℝ).symm
          (fun i => E (EuclideanSpace.single i (1 : ℝ))) ∧
        hhessS G.sig z D B = Matrix.of (fun i j =>
          C (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) := by
    intro φ z ζ hzζ D B hDB
    obtain ⟨E, hEapp⟩ : ∃ E : EuclideanSpace ℝ (Fin G.m) →L[ℝ] ℝ,
        ∀ a, E a = D (G.hexp a) :=
      ⟨D.comp hexpL, fun a => by rw [ContinuousLinearMap.comp_apply, hexpLapp]⟩
    obtain ⟨C, hCapp⟩ : ∃ C : EuclideanSpace ℝ (Fin G.m) →L[ℝ]
        EuclideanSpace ℝ (Fin G.m) →L[ℝ] ℝ, ∀ a b, C a b = B (G.hexp a) (G.hexp b) :=
      ⟨(((B.comp hexpL).flip).comp hexpL).flip, fun a b => by simp [hexpLapp]⟩
    refine ⟨E, C, ⟨fun a b => by rw [hCapp, hCapp, hDB.1], ?_⟩, ?_, ?_⟩
    · -- the Peano estimate transports with the SAME `δ`, by linearity and the isometry
      intro ε hε
      obtain ⟨δ, hδ, hb⟩ := hDB.2 ε hε
      refine ⟨δ, hδ, fun w hw => ?_⟩
      have hy : G.hexp w - z = G.hexp (w - ζ) := by rw [hsubL, hzζ]
      have h1 := hb (G.hexp w) (by rw [hy, hiso]; exact hw)
      rw [hy, hiso, ← hEapp (w - ζ), ← hCapp (w - ζ) (w - ζ), ← hzζ] at h1
      exact h1
    · -- the `hgrad` identity, from `sig x i = hexp (e_i)`
      have h0 : hgrad G.sig z D
          = (EuclideanSpace.equiv (Fin G.m) ℝ).symm (fun i => D (G.sig z i)) := rfl
      rw [h0]
      congr 1
      funext i
      rw [hsig z i, hEapp]
    · -- the `hhessS` identity: `Mfield` vanishes because the Euclidean frame is constant
      have h0 : hhessS G.sig z D B
          = Matrix.of (fun i j => B (G.sig z i) (G.sig z j)) + Mfield G.sig z D := rfl
      rw [h0, hM z D, add_zero]
      ext i j
      simp only [Matrix.of_apply]
      rw [hsig z i, hsig z j, hCapp]
  have hpsiC : ∀ φ : EuclideanSpace ℝ (Fin G.n) → ℝ,
      ContDiffOn ℝ 2 φ (G.hexp '' Ω') → ContDiffOn ℝ 2 (fun w => φ (G.hexp w)) Ω' :=
    fun φ hφ => hφ.comp hexpcd.contDiffOn fun ζ hζ => ⟨ζ, hζ, rfl⟩
  -- ===== Step 5: `U` is a viscosity sub-solution in `Ω''` =====
  have hUsub : IsViscSubsol G A H (G.hexp '' Ω') (fun z => F (G.pi1 z)) := by
    refine ⟨(hUcont.mono subset_closure).upperSemicontinuousOn, ?_⟩
    intro z hz φ hφ hmax D B hDB hgne
    have hζΩ : G.pi1 z ∈ Ω' := by rw [hΩeq] at hz; exact hz
    obtain ⟨E, C, hEC, hg, hh⟩ := hpack φ z (G.pi1 z) (hexppi z) D B hDB
    have hmaxζ : IsMaxOn (fun w => F w - φ (G.hexp w)) Ω' (G.pi1 z) := by
      refine isMaxOn_iff.2 fun w hw => ?_
      have h : F (G.pi1 (G.hexp w)) - φ (G.hexp w) ≤ F (G.pi1 z) - φ z :=
        isMaxOn_iff.1 hmax (G.hexp w) ⟨w, hw, rfl⟩
      rw [G.pi1_hexp] at h
      show F w - φ (G.hexp w) ≤ F (G.pi1 z) - φ (G.hexp (G.pi1 z))
      rw [hexppi z]
      exact h
    have hξne : (EuclideanSpace.equiv (Fin G.m) ℝ).symm
        (fun i => E (EuclideanSpace.single i (1 : ℝ))) ≠ 0 := by rw [← hg]; exact hgne
    have hres := hFsub (G.pi1 z) hζΩ (fun w => φ (G.hexp w)) (hpsiC φ hφ) hmaxζ E C hEC _
      rfl hξne
    have h0 : Lop G.sig A H z D B
        = -(A (hgrad G.sig z D) * hhessS G.sig z D B).trace + H (hgrad G.sig z D) := rfl
    rw [h0, hg, hh]
    exact hres
  -- ===== Step 6: `V` is a viscosity super-solution in `Ω''`, the mirror =====
  have hVsup : IsViscSupersol G A H (G.hexp '' Ω') (fun z => Gf (G.pi1 z)) := by
    refine ⟨(hVcont.mono subset_closure).lowerSemicontinuousOn, ?_⟩
    intro z hz φ hφ hmin D B hDB hgne
    have hζΩ : G.pi1 z ∈ Ω' := by rw [hΩeq] at hz; exact hz
    obtain ⟨E, C, hEC, hg, hh⟩ := hpack φ z (G.pi1 z) (hexppi z) D B hDB
    have hminζ : IsMinOn (fun w => Gf w - φ (G.hexp w)) Ω' (G.pi1 z) := by
      refine isMinOn_iff.2 fun w hw => ?_
      have h : Gf (G.pi1 z) - φ z ≤ Gf (G.pi1 (G.hexp w)) - φ (G.hexp w) :=
        isMinOn_iff.1 hmin (G.hexp w) ⟨w, hw, rfl⟩
      rw [G.pi1_hexp] at h
      show Gf (G.pi1 z) - φ (G.hexp (G.pi1 z)) ≤ Gf w - φ (G.hexp w)
      rw [hexppi z]
      exact h
    have hξne : (EuclideanSpace.equiv (Fin G.m) ℝ).symm
        (fun i => E (EuclideanSpace.single i (1 : ℝ))) ≠ 0 := by rw [← hg]; exact hgne
    have hres := hGfsup (G.pi1 z) hζΩ (fun w => φ (G.hexp w)) (hpsiC φ hφ) hminζ E C hEC _
      rfl hξne
    have h0 : Lop G.sig A H z D B
        = -(A (hgrad G.sig z D) * hhessS G.sig z D B).trace + H (hgrad G.sig z D) := rfl
    rw [h0, hg, hh]
    exact hres
  -- ===== Step 7: the abelian comparison on `Ω''`, then descent along `pi1 ∘ hexp = id` =====
  have hCA := ComparisonAbelian G hcE hab A H hAH (G.hexp '' Ω') hΩ''open hΩ''bdd hΩ''ne
    (fun z => F (G.pi1 z)) (fun z => Gf (G.pi1 z)) hUcont hVcont hUsub hVsup
    (fun z hz => hbdry (G.pi1 z) (hfr z hz)) R hR
    (fun z hz => hRb (G.pi1 z) (hcl z hz))
  intro ζ hζ
  have h := hCA (G.hexp ζ) ⟨ζ, hζ, rfl⟩
  rwa [G.pi1_hexp] at h
