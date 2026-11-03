import CompND.LocallySemiConvexOn
import CompND.TwiceDiffAt

/-- The two *Euclidean* results the paper cites from the literature and does not prove:
Aleksandrov's theorem and Jensen's lemma, items (2) and (3) of the note for the
formalization. Neither mentions a Carnot group: both are statements about
`EuclideanSpace ℝ (Fin N)` for an arbitrary `N`, and both are classical. They are bundled
separately from the Carnot-side cited results precisely because they do not depend on a
sub-elliptic setting, so a consumer that is itself Euclidean can assume them without naming
one. No axiom is introduced; every result that uses one of these carries this structure, or
a structure extending it, as an explicit hypothesis. -/
structure EuclidCitedResults : Prop where
  aleksandrov : ∀ (N : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin N))), IsOpen Ω →
      ∀ w : EuclideanSpace ℝ (Fin N) → ℝ, LocallySemiConvexOn Ω w →
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin N))),
        x ∈ Ω → ∃ (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
          (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
          TwiceDiffAt w x D B
  jensen : ∀ (N : ℕ) (w : EuclideanSpace ℝ (Fin N) → ℝ) (xh : EuclideanSpace ℝ (Fin N)),
      (∃ ν > 0, LocallySemiConvexOn (Metric.ball xh ν) w) →
      (∃ ν > 0, ∀ y ∈ Metric.ball xh ν, y ≠ xh → w y < w xh) →
      ∃ ρ₀ > 0, ∃ δ₀ > 0, ∀ ρ, 0 < ρ → ρ < ρ₀ → ∀ δ, 0 < δ → δ < δ₀ →
        0 < (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin N)))
          (⋃ p ∈ {p : EuclideanSpace ℝ (Fin N) | ‖p‖ < δ},
            {x ∈ Metric.ball xh ρ |
              IsMaxOn (fun y => w y + ∑ i, p i * y i) (Metric.ball xh ρ) x})
