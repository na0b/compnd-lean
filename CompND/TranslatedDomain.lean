import CompND.CarnotSetting

/-- The first half of eq:omdelta: `Ω_δ = {x ∈ Ω : dist(x, ∂Ω) > δ}`, with `dist` taken in the
left-invariant distance `d(x,y) = ‖y⁻¹ * x‖` and written out as "every boundary point is at
`d`-distance more than `δ` from `x`". -/
def TranslatedDomain (G : CarnotSetting) (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin G.n)) :=
  {x ∈ Ω | ∀ y ∈ frontier Ω, δ < G.hnorm (G.mul (-y) x)}
