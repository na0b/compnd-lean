import CompND.IsViscSubsol
import CompND.IsViscSupersol

/-- Adding a constant to a viscosity sub-solution (resp. super-solution) of `ℒ u = 0` again
gives one: `ℒ` of eq:maineq carries no zeroth-order term, so the constant is absorbed into
the test function. -/
theorem AddConstPreservesSubsol (G : CarnotSetting)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (u : EuclideanSpace ℝ (Fin G.n) → ℝ) (c : ℝ) :
    (IsViscSubsol G A H Ω u → IsViscSubsol G A H Ω (fun x => u x + c)) ∧
    (IsViscSupersol G A H Ω u → IsViscSupersol G A H Ω (fun x => u x + c)) := by
  have hjet : ∀ (φ : EuclideanSpace ℝ (Fin G.n) → ℝ) (x : EuclideanSpace ℝ (Fin G.n))
      (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      TwiceDiffAt φ x D B → TwiceDiffAt (fun y => φ y - c) x D B := by
    intro φ x D B h
    refine ⟨h.1, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hb⟩ := h.2 ε hε
    exact ⟨δ, hδ, fun y hy => by simpa using hb y hy⟩
  constructor
  · intro h
    refine ⟨?_, fun x hx φ hφ hmax D B hj hg => ?_⟩
    · intro x hx y hy
      have hy' : u x < y - c := by linarith
      filter_upwards [h.1 x hx (y - c) hy'] with z hz
      show u z + c < y
      linarith
    · refine h.2 x hx (fun y => φ y - c) (hφ.sub contDiffOn_const) ?_ D B (hjet φ x D B hj) hg
      rw [isMaxOn_iff]
      intro y hy
      have h1 := isMaxOn_iff.1 hmax y hy
      simp only at h1 ⊢
      linarith
  · intro h
    refine ⟨?_, fun x hx φ hφ hmin D B hj hg => ?_⟩
    · intro x hx y hy
      have hy' : y - c < u x := by linarith
      filter_upwards [h.1 x hx (y - c) hy'] with z hz
      show u z + c > y
      linarith
    · refine h.2 x hx (fun y => φ y - c) (hφ.sub contDiffOn_const) ?_ D B (hjet φ x D B hj) hg
      rw [isMinOn_iff]
      intro y hy
      have h1 := isMinOn_iff.1 hmin y hy
      simp only at h1 ⊢
      linarith
