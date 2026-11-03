import CompND.IsViscSubsol
import CompND.IsViscSupersol

/-- lem:lefttrans: the left translate `u^h = u ∘ L_h` of a viscosity sub-solution
(resp. super-solution) in `Ω` is a viscosity sub-solution (resp. super-solution) in
`L_h⁻¹(Ω) = h⁻¹ * Ω`, because the horizontal fields are left-invariant. -/
theorem LeftTranslateSubsol (G : CarnotSetting)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (u : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (h : EuclideanSpace ℝ (Fin G.n)) :
    (IsViscSubsol G A H Ω u →
      IsViscSubsol G A H ((fun x => G.mul h x) ⁻¹' Ω) (fun x => u (G.mul h x))) ∧
    (IsViscSupersol G A H Ω u →
      IsViscSupersol G A H ((fun x => G.mul h x) ⁻¹' Ω) (fun x => u (G.mul h x))) := by
  set Ω' : Set (EuclideanSpace ℝ (Fin G.n)) := (fun x => G.mul h x) ⁻¹' Ω with hΩ'
  have hcancel : ∀ x : EuclideanSpace ℝ (Fin G.n), G.mul (-h) (G.mul h x) = x := by
    intro x; rw [← G.mul_assoc, G.neg_mul, G.zero_mul]
  have hcancel' : ∀ x : EuclideanSpace ℝ (Fin G.n), G.mul h (G.mul (-h) x) = x := by
    intro x; rw [← G.mul_assoc, G.mul_neg, G.zero_mul]
  have hLsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin G.n) => G.mul h x) :=
    G.mul_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hLinvsmooth :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin G.n) => G.mul (-h) x) :=
    G.mul_smooth.comp (contDiff_const.prodMk contDiff_id)
  -- the translated test function and its properties
  have hmaps : Set.MapsTo (fun z : EuclideanSpace ℝ (Fin G.n) => G.mul (-h) z) Ω Ω' := by
    intro z hz
    show G.mul h (G.mul (-h) z) ∈ Ω
    rw [hcancel' z]; exact hz
  have hmaps' : Set.MapsTo (fun x : EuclideanSpace ℝ (Fin G.n) => G.mul h x) Ω' Ω :=
    fun x hx => hx
  have hpsiC : ∀ φ : EuclideanSpace ℝ (Fin G.n) → ℝ, ContDiffOn ℝ 2 φ Ω' →
      ContDiffOn ℝ 2 (fun z => φ (G.mul (-h) z)) Ω := by
    intro φ hφ
    exact hφ.comp ((hLinvsmooth.of_le (by norm_cast)).contDiffOn) hmaps
  have hpsix : ∀ (φ : EuclideanSpace ℝ (Fin G.n) → ℝ) (x : EuclideanSpace ℝ (Fin G.n)),
      (fun z => φ (G.mul (-h) z)) (G.mul h x) = φ x := by
    intro φ x; simp only; rw [hcancel x]
  have hjettr : ∀ (φ : EuclideanSpace ℝ (Fin G.n) → ℝ) (x : EuclideanSpace ℝ (Fin G.n))
      (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      TwiceDiffAt φ x D B →
      ∃ (D' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
        (B' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
        TwiceDiffAt (fun z => φ (G.mul (-h) z)) (G.mul h x) D' B' ∧
        hgrad G.sig (G.mul h x) D' = hgrad G.sig x D ∧
        hhessS G.sig (G.mul h x) D' B' = hhessS G.sig x D B := by
    intro φ x D B hjet
    have hjet0 : TwiceDiffAt φ (G.mul (-h) (G.mul h x)) D B := by rw [hcancel x]; exact hjet
    obtain ⟨D', B', hj', hgr', hhe'⟩ := G.leftJet (-h) (G.mul h x) φ D B hjet0
    rw [hcancel x] at hgr' hhe'
    exact ⟨D', B', hj', hgr', hhe'⟩
  have hLop : ∀ (x : EuclideanSpace ℝ (Fin G.n))
      (D D' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (B B' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      hgrad G.sig (G.mul h x) D' = hgrad G.sig x D →
      hhessS G.sig (G.mul h x) D' B' = hhessS G.sig x D B →
      Lop G.sig A H (G.mul h x) D' B' = Lop G.sig A H x D B := by
    intro x D D' B B' hgr hhe
    simp only [Lop, hgr, hhe]
  constructor
  · rintro ⟨husc, hsub⟩
    refine ⟨?_, fun x hx φ hφ hmax D B hjet hg => ?_⟩
    · intro x hx y hy
      have hev := husc (G.mul h x) hx y hy
      exact ((hLsmooth.continuous.continuousWithinAt).tendsto_nhdsWithin hmaps').eventually hev
    · obtain ⟨D', B', hj', hgr', hhe'⟩ := hjettr φ x D B hjet
      have hmaxΩ : IsMaxOn (fun z => u z - (fun w => φ (G.mul (-h) w)) z) Ω (G.mul h x) := by
        intro z hz
        have hw : G.mul (-h) z ∈ Ω' := hmaps hz
        have h1 : u (G.mul h (G.mul (-h) z)) - φ (G.mul (-h) z)
            ≤ u (G.mul h x) - φ x := hmax hw
        show u z - φ (G.mul (-h) z) ≤ u (G.mul h x) - φ (G.mul (-h) (G.mul h x))
        rw [hcancel x]
        rw [hcancel' z] at h1
        exact h1
      have hg' : hgrad G.sig (G.mul h x) D' ≠ 0 := by rw [hgr']; exact hg
      have hle := hsub (G.mul h x) hx (fun z => φ (G.mul (-h) z)) (hpsiC φ hφ) hmaxΩ D' B' hj' hg'
      rw [hLop x D D' B B' hgr' hhe'] at hle
      exact hle
  · rintro ⟨hlsc, hsup⟩
    refine ⟨?_, fun x hx φ hφ hmin D B hjet hg => ?_⟩
    · intro x hx y hy
      have hev := hlsc (G.mul h x) hx y hy
      exact ((hLsmooth.continuous.continuousWithinAt).tendsto_nhdsWithin hmaps').eventually hev
    · obtain ⟨D', B', hj', hgr', hhe'⟩ := hjettr φ x D B hjet
      have hminΩ : IsMinOn (fun z => u z - (fun w => φ (G.mul (-h) w)) z) Ω (G.mul h x) := by
        intro z hz
        have hw : G.mul (-h) z ∈ Ω' := hmaps hz
        have h1 : u (G.mul h x) - φ x
            ≤ u (G.mul h (G.mul (-h) z)) - φ (G.mul (-h) z) := hmin hw
        show u (G.mul h x) - φ (G.mul (-h) (G.mul h x)) ≤ u z - φ (G.mul (-h) z)
        rw [hcancel x]
        rw [hcancel' z] at h1
        exact h1
      have hg' : hgrad G.sig (G.mul h x) D' ≠ 0 := by rw [hgr']; exact hg
      have hge := hsup (G.mul h x) hx (fun z => φ (G.mul (-h) z)) (hpsiC φ hφ) hminΩ D' B' hj' hg'
      rw [hLop x D D' B B' hgr' hhe'] at hge
      exact hge
