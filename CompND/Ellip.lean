import CompND.Preamble

/-- The ellipticity function of eq:ell: `𝓔 A ξ = ⟪A ξ • ξ, ξ⟫ = ∑ i, ∑ j, A ξ i j * ξ j * ξ i`.
Condition (E) is exactly `0 < Ellip A ξ` for `ξ ≠ 0`. -/
noncomputable def Ellip {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (ξ : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ i, ∑ j, A ξ i j * ξ j * ξ i
