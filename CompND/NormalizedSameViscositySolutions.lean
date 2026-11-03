import CompND.IsViscSubsol
import CompND.IsViscSupersol

/-- subsec:str: multiplying `(A, H)` by a positive function of the horizontal gradient does
not change the viscosity sub- or super-solutions, because test functions are only ever
evaluated where the horizontal gradient does not vanish. -/
theorem NormalizedSameViscositySolutions (G : CarnotSetting)
    (A A₀ : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H H₀ : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (a : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (ha : ∀ ξ : EuclideanSpace ℝ (Fin G.m), ξ ≠ 0 → 0 < a ξ)
    (hA : ∀ ξ : EuclideanSpace ℝ (Fin G.m), ξ ≠ 0 → A ξ = a ξ • A₀ ξ)
    (hH : ∀ ξ : EuclideanSpace ℝ (Fin G.m), ξ ≠ 0 → H ξ = a ξ * H₀ ξ)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (u : EuclideanSpace ℝ (Fin G.n) → ℝ) :
    (IsViscSubsol G A H Ω u ↔ IsViscSubsol G A₀ H₀ Ω u) ∧
    (IsViscSupersol G A H Ω u ↔ IsViscSupersol G A₀ H₀ Ω u) := by
  have key : ∀ (x : EuclideanSpace ℝ (Fin G.n)) (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      hgrad G.sig x D ≠ 0 →
      Lop G.sig A H x D B = a (hgrad G.sig x D) * Lop G.sig A₀ H₀ x D B := by
    intro x D B hg
    simp only [Lop, hA _ hg, hH _ hg, Matrix.smul_mul, Matrix.trace_smul]
    ring
  refine ⟨⟨fun h => ⟨h.1, fun x hx φ hφ hmax D B hj hg => ?_⟩,
           fun h => ⟨h.1, fun x hx φ hφ hmax D B hj hg => ?_⟩⟩,
          ⟨fun h => ⟨h.1, fun x hx φ hφ hmin D B hj hg => ?_⟩,
           fun h => ⟨h.1, fun x hx φ hφ hmin D B hj hg => ?_⟩⟩⟩
  · have hle := h.2 x hx φ hφ hmax D B hj hg
    rw [key x D B hg] at hle
    have h2 : a (hgrad G.sig x D) * Lop G.sig A₀ H₀ x D B ≤ a (hgrad G.sig x D) * 0 := by
      simpa using hle
    exact le_of_mul_le_mul_left h2 (ha _ hg)
  · have hle := h.2 x hx φ hφ hmax D B hj hg
    rw [key x D B hg]
    have h2 : a (hgrad G.sig x D) * Lop G.sig A₀ H₀ x D B ≤ a (hgrad G.sig x D) * 0 :=
      mul_le_mul_of_nonneg_left hle (le_of_lt (ha _ hg))
    simpa using h2
  · have hge := h.2 x hx φ hφ hmin D B hj hg
    rw [key x D B hg] at hge
    have h2 : a (hgrad G.sig x D) * 0 ≤ a (hgrad G.sig x D) * Lop G.sig A₀ H₀ x D B := by
      simpa using hge
    exact le_of_mul_le_mul_left h2 (ha _ hg)
  · have hge := h.2 x hx φ hφ hmin D B hj hg
    rw [key x D B hg]
    have h2 : a (hgrad G.sig x D) * 0 ≤ a (hgrad G.sig x D) * Lop G.sig A₀ H₀ x D B :=
      mul_le_mul_of_nonneg_left hge (le_of_lt (ha _ hg))
    simpa using h2
