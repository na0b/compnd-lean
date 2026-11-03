import CompND.IsViscSubsol
import CompND.IsViscSupersol
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-- The sentence after def:visc: since a test function may be modified away from the point
of contact, a *local* touching is enough. For `u` bounded above (resp. below) on `Ω`, a
viscosity sub-solution (resp. super-solution) satisfies the jet inequality at every local
maximum (resp. minimum) of `u - φ` on a ball inside `Ω` with non-vanishing horizontal
gradient, and is in particular a sub-solution (resp. super-solution) in every open
`V ⊆ Ω`. -/
theorem ViscTestLocalization (G : CarnotSetting)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (u : EuclideanSpace ℝ (Fin G.n) → ℝ) :
    ((∃ Mu : ℝ, ∀ y ∈ Ω, u y ≤ Mu) → IsViscSubsol G A H Ω u →
      (∀ x ∈ Ω, ∀ (φ : EuclideanSpace ℝ (Fin G.n) → ℝ) (r : ℝ), 0 < r →
          Metric.ball x r ⊆ Ω → ContDiffOn ℝ 2 φ (Metric.ball x r) →
          (∀ y ∈ Metric.ball x r, u y - φ y ≤ u x - φ x) →
          ∀ (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
            (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
            TwiceDiffAt φ x D B → hgrad G.sig x D ≠ 0 → Lop G.sig A H x D B ≤ 0) ∧
      (∀ V : Set (EuclideanSpace ℝ (Fin G.n)), IsOpen V → V ⊆ Ω →
          IsViscSubsol G A H V u)) ∧
    ((∃ mu : ℝ, ∀ y ∈ Ω, mu ≤ u y) → IsViscSupersol G A H Ω u →
      (∀ x ∈ Ω, ∀ (φ : EuclideanSpace ℝ (Fin G.n) → ℝ) (r : ℝ), 0 < r →
          Metric.ball x r ⊆ Ω → ContDiffOn ℝ 2 φ (Metric.ball x r) →
          (∀ y ∈ Metric.ball x r, u x - φ x ≤ u y - φ y) →
          ∀ (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
            (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
            TwiceDiffAt φ x D B → hgrad G.sig x D ≠ 0 → 0 ≤ Lop G.sig A H x D B) ∧
      (∀ V : Set (EuclideanSpace ℝ (Fin G.n)), IsOpen V → V ⊆ Ω →
          IsViscSupersol G A H V u)) := by
  constructor
  · rintro ⟨Mu, hMu⟩ ⟨husc, hsub⟩
    have main : ∀ x ∈ Ω, ∀ (φ : EuclideanSpace ℝ (Fin G.n) → ℝ) (r : ℝ), 0 < r →
        Metric.ball x r ⊆ Ω → ContDiffOn ℝ 2 φ (Metric.ball x r) →
        (∀ y ∈ Metric.ball x r, u y - φ y ≤ u x - φ x) →
        ∀ (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
          (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
          TwiceDiffAt φ x D B → hgrad G.sig x D ≠ 0 → Lop G.sig A H x D B ≤ 0 := by
      intro x hx φ r hr hbΩ hφ hloc D B hjet hg
      set bump : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩ with hbumpdef
      set χ : EuclideanSpace ℝ (Fin G.n) → ℝ := fun y => bump y with hχdef
      have hχsmooth : ContDiff ℝ 2 χ := ContDiffBump.contDiff _
      have hχ0 : ∀ y, 0 ≤ χ y := fun y => ContDiffBump.nonneg _
      have hχ1 : ∀ y, χ y ≤ 1 := fun y => ContDiffBump.le_one _
      have hχsupp : ∀ y, χ y ≠ 0 → y ∈ Metric.ball x (r / 2) := by
        intro y hy
        have : y ∈ Function.support χ := hy
        rwa [hχdef, ContDiffBump.support_eq] at this
      have hχone : ∀ y, dist y x ≤ r / 4 → χ y = 1 :=
        fun y hy => ContDiffBump.one_of_mem_closedBall _ (by simpa [Metric.mem_closedBall])
      set K : ℝ := Mu - (u x - φ x) with hKdef
      set φt : EuclideanSpace ℝ (Fin G.n) → ℝ := fun y => χ y * φ y + K * (1 - χ y) with hφtdef
      -- φt is C² on Ω
      have hφtC : ContDiffOn ℝ 2 φt Ω := by
        intro y hy
        have hat : ContDiffAt ℝ 2 φt y := by
          rcases lt_or_ge (r / 2) (dist y x) with hgt | hle
          · have hopen : IsOpen {z : EuclideanSpace ℝ (Fin G.n) | r / 2 < dist z x} :=
              isOpen_lt continuous_const (continuous_id.dist continuous_const)
            have heq : φt =ᶠ[nhds y] fun _ => K := by
              filter_upwards [hopen.mem_nhds hgt] with z hz
              have hz0 : χ z = 0 := by
                by_contra hne
                have := hχsupp z hne
                rw [Metric.mem_ball] at this
                exact absurd this (not_lt.2 (le_of_lt hz))
              simp [hφtdef, hz0]
            exact (contDiffAt_const (c := K)).congr_of_eventuallyEq heq
          · have hyb : y ∈ Metric.ball x r := by
              rw [Metric.mem_ball]; linarith
            have hφat : ContDiffAt ℝ 2 φ y :=
              hφ.contDiffAt (Metric.isOpen_ball.mem_nhds hyb)
            exact (hχsmooth.contDiffAt.mul hφat).add
              (contDiffAt_const.mul (contDiffAt_const.sub hχsmooth.contDiffAt))
        exact hat.contDiffWithinAt
      -- x is a global max of u - φt on Ω
      have hφtx : φt x = φ x := by
        have : χ x = 1 := hχone x (by simp; linarith)
        simp [hφtdef, this]
      have hmax : IsMaxOn (fun y => u y - φt y) Ω x := by
        intro y hy
        have hid : u y - φt y = χ y * (u y - φ y) + (1 - χ y) * (u y - K) := by
          simp only [hφtdef]; ring
        have hKy : u y - K ≤ u x - φ x := by rw [hKdef]; linarith [hMu y hy]
        show u y - φt y ≤ u x - φt x
        rw [hφtx, hid]
        rcases eq_or_ne (χ y) 0 with h0 | hne
        · rw [h0]; simpa using hKy
        · have h1 : χ y * (u y - φ y) ≤ χ y * (u x - φ x) :=
            mul_le_mul_of_nonneg_left (hloc y (Metric.ball_subset_ball (by linarith)
              (hχsupp y hne))) (hχ0 y)
          have h2 : (1 - χ y) * (u y - K) ≤ (1 - χ y) * (u x - φ x) :=
            mul_le_mul_of_nonneg_left hKy (by linarith [hχ1 y])
          nlinarith [h1, h2]
      -- the 2-jet at x is unchanged
      have hjet' : TwiceDiffAt φt x D B := by
        refine ⟨hjet.1, fun ε hε => ?_⟩
        obtain ⟨δ, hδ, hd⟩ := hjet.2 ε hε
        refine ⟨min δ (r / 4), by positivity, fun y hy => ?_⟩
        have h1 : ‖y - x‖ < δ := lt_of_lt_of_le hy (min_le_left _ _)
        have h2 : ‖y - x‖ < r / 4 := lt_of_lt_of_le hy (min_le_right _ _)
        have hχy : χ y = 1 := hχone y (by rw [dist_eq_norm]; linarith)
        have hfy : φt y = φ y := by simp [hφtdef, hχy]
        rw [hfy, hφtx]
        exact hd y h1
      exact hsub x hx φt hφtC hmax D B hjet' hg
    refine ⟨main, ?_⟩
    intro V hV hVΩ
    refine ⟨husc.mono hVΩ, ?_⟩
    intro x hx φ hφ hmax D B hjet hg
    obtain ⟨r, hr, hbV⟩ := Metric.isOpen_iff.1 hV x hx
    exact main x (hVΩ hx) φ r hr (hbV.trans hVΩ) (hφ.mono hbV)
      (fun y hy => hmax (hbV hy)) D B hjet hg
  · rintro ⟨mu, hmu⟩ ⟨hlsc, hsup⟩
    have main : ∀ x ∈ Ω, ∀ (φ : EuclideanSpace ℝ (Fin G.n) → ℝ) (r : ℝ), 0 < r →
        Metric.ball x r ⊆ Ω → ContDiffOn ℝ 2 φ (Metric.ball x r) →
        (∀ y ∈ Metric.ball x r, u x - φ x ≤ u y - φ y) →
        ∀ (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
          (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
          TwiceDiffAt φ x D B → hgrad G.sig x D ≠ 0 → 0 ≤ Lop G.sig A H x D B := by
      intro x hx φ r hr hbΩ hφ hloc D B hjet hg
      set bump : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩ with hbumpdef
      set χ : EuclideanSpace ℝ (Fin G.n) → ℝ := fun y => bump y with hχdef
      have hχsmooth : ContDiff ℝ 2 χ := ContDiffBump.contDiff _
      have hχ0 : ∀ y, 0 ≤ χ y := fun y => ContDiffBump.nonneg _
      have hχ1 : ∀ y, χ y ≤ 1 := fun y => ContDiffBump.le_one _
      have hχsupp : ∀ y, χ y ≠ 0 → y ∈ Metric.ball x (r / 2) := by
        intro y hy
        have : y ∈ Function.support χ := hy
        rwa [hχdef, ContDiffBump.support_eq] at this
      have hχone : ∀ y, dist y x ≤ r / 4 → χ y = 1 :=
        fun y hy => ContDiffBump.one_of_mem_closedBall _ (by simpa [Metric.mem_closedBall])
      set K : ℝ := mu - (u x - φ x) with hKdef
      set φt : EuclideanSpace ℝ (Fin G.n) → ℝ := fun y => χ y * φ y + K * (1 - χ y) with hφtdef
      have hφtC : ContDiffOn ℝ 2 φt Ω := by
        intro y hy
        have hat : ContDiffAt ℝ 2 φt y := by
          rcases lt_or_ge (r / 2) (dist y x) with hgt | hle
          · have hopen : IsOpen {z : EuclideanSpace ℝ (Fin G.n) | r / 2 < dist z x} :=
              isOpen_lt continuous_const (continuous_id.dist continuous_const)
            have heq : φt =ᶠ[nhds y] fun _ => K := by
              filter_upwards [hopen.mem_nhds hgt] with z hz
              have hz0 : χ z = 0 := by
                by_contra hne
                have := hχsupp z hne
                rw [Metric.mem_ball] at this
                exact absurd this (not_lt.2 (le_of_lt hz))
              simp [hφtdef, hz0]
            exact (contDiffAt_const (c := K)).congr_of_eventuallyEq heq
          · have hyb : y ∈ Metric.ball x r := by
              rw [Metric.mem_ball]; linarith
            have hφat : ContDiffAt ℝ 2 φ y :=
              hφ.contDiffAt (Metric.isOpen_ball.mem_nhds hyb)
            exact (hχsmooth.contDiffAt.mul hφat).add
              (contDiffAt_const.mul (contDiffAt_const.sub hχsmooth.contDiffAt))
        exact hat.contDiffWithinAt
      have hφtx : φt x = φ x := by
        have : χ x = 1 := hχone x (by simp; linarith)
        simp [hφtdef, this]
      have hmin : IsMinOn (fun y => u y - φt y) Ω x := by
        intro y hy
        have hid : u y - φt y = χ y * (u y - φ y) + (1 - χ y) * (u y - K) := by
          simp only [hφtdef]; ring
        have hKy : u x - φ x ≤ u y - K := by rw [hKdef]; linarith [hmu y hy]
        show u x - φt x ≤ u y - φt y
        rw [hφtx, hid]
        rcases eq_or_ne (χ y) 0 with h0 | hne
        · rw [h0]; simpa using hKy
        · have h1 : χ y * (u x - φ x) ≤ χ y * (u y - φ y) :=
            mul_le_mul_of_nonneg_left (hloc y (Metric.ball_subset_ball (by linarith)
              (hχsupp y hne))) (hχ0 y)
          have h2 : (1 - χ y) * (u x - φ x) ≤ (1 - χ y) * (u y - K) :=
            mul_le_mul_of_nonneg_left hKy (by linarith [hχ1 y])
          nlinarith [h1, h2]
      have hjet' : TwiceDiffAt φt x D B := by
        refine ⟨hjet.1, fun ε hε => ?_⟩
        obtain ⟨δ, hδ, hd⟩ := hjet.2 ε hε
        refine ⟨min δ (r / 4), by positivity, fun y hy => ?_⟩
        have h1 : ‖y - x‖ < δ := lt_of_lt_of_le hy (min_le_left _ _)
        have h2 : ‖y - x‖ < r / 4 := lt_of_lt_of_le hy (min_le_right _ _)
        have hχy : χ y = 1 := hχone y (by rw [dist_eq_norm]; linarith)
        have hfy : φt y = φ y := by simp [hφtdef, hχy]
        rw [hfy, hφtx]
        exact hd y h1
      exact hsup x hx φt hφtC hmin D B hjet' hg
    refine ⟨main, ?_⟩
    intro V hV hVΩ
    refine ⟨hlsc.mono hVΩ, ?_⟩
    intro x hx φ hφ hmin D B hjet hg
    obtain ⟨r, hr, hbV⟩ := Metric.isOpen_iff.1 hV x hx
    exact main x (hVΩ hx) φ r hr (hbV.trans hVΩ) (hφ.mono hbV)
      (fun y hy => hmin (hbV hy)) D B hjet hg
