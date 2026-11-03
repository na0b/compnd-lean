import CompND.Preamble

/-- The structure conditions on `(A, H)` of section subsec:defs: `A` symmetric positive
semidefinite, `A` and `H` continuous on `ℝᵐ \ {0}`, strict ellipticity in the gradient
direction (E) eq:ell, and homogeneity along rays (S) eq:scale. -/
structure StructureConditionsES (m : ℕ)
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ) : Prop where
  symm : ∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → (A ξ).IsSymm
  psd : ∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → ∀ η : EuclideanSpace ℝ (Fin m),
    0 ≤ ∑ i, ∑ j, A ξ i j * η j * η i
  contA : ContinuousOn A {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0}
  contH : ContinuousOn H {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0}
  ellipticity : ∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → 0 < ∑ i, ∑ j, A ξ i j * ξ j * ξ i
  scaling : ∃ κ : ℝ → EuclideanSpace ℝ (Fin m) → ℝ,
    (∀ t ξ, 1 ≤ t → ξ ≠ 0 → 0 < κ t ξ) ∧
    (∀ t ξ, 1 ≤ t → ξ ≠ 0 → A (t • ξ) = κ t ξ • A ξ) ∧
    (∀ t ξ, 1 ≤ t → ξ ≠ 0 → H (t • ξ) = t * κ t ξ * H ξ)
