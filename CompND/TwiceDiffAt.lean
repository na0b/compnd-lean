import CompND.Preamble

/-- `TwiceDiffAt w x D B` says that the symmetric continuous bilinear form `B` and the
continuous linear functional `D` form a second-order (Peano) jet of `w` at `x`. -/
def TwiceDiffAt {N : ℕ} (w : EuclideanSpace ℝ (Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N))
    (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) : Prop :=
  (∀ u v, B u v = B v u) ∧
  ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : EuclideanSpace ℝ (Fin N), ‖y - x‖ < δ →
    |w y - w x - D (y - x) - (1 / 2) * B (y - x) (y - x)| ≤ ε * ‖y - x‖ ^ 2
