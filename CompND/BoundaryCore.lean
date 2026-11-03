import CompND.CarnotSetting

/-- The second half of eq:omdelta: `K_ρ = {x ∈ Ω : dist(x, ∂Ω) ≥ ρ}`, with `dist` taken in
the left-invariant distance `d(x,y) = ‖y⁻¹ * x‖` and written out as "every boundary point is
at `d`-distance at least `ρ` from `x`". -/
def BoundaryCore (G : CarnotSetting) (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (ρ : ℝ) :
    Set (EuclideanSpace ℝ (Fin G.n)) :=
  {x ∈ Ω | ∀ y ∈ frontier Ω, ρ ≤ G.hnorm (G.mul (-y) x)}
