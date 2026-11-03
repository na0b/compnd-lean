import CompND.Preamble

/-- Pansu differentiability at `x` with horizontal differential `ξ`:
`f (x * g) = f x + ⟪ξ, π₁ g⟫ + o (‖g‖)` as `g → 0` in the homogeneous norm. -/
def HasPansuGradAt {n m : ℕ}
    (mul : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (pi1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hnorm : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (ξ : EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ g : EuclideanSpace ℝ (Fin n), hnorm g < δ →
    |f (mul x g) - f x - ∑ i, ξ i * (pi1 g) i| ≤ ε * hnorm g
