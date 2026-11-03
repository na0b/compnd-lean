import CompND.Preamble

/-- Local semi-convexity: around every point of `Ω` there is a ball inside `Ω` and a
constant `Λ ≥ 0` with `y ↦ w y + Λ/2 * ‖y‖ ^ 2` convex on that ball. -/
def LocallySemiConvexOn {N : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin N)))
    (w : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ∀ x ∈ Ω, ∃ ρ > 0, ∃ Λ : ℝ, 0 ≤ Λ ∧ Metric.ball x ρ ⊆ Ω ∧
    ConvexOn ℝ (Metric.ball x ρ) (fun y => w y + Λ / 2 * ‖y‖ ^ 2)
