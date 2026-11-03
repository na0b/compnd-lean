import CompND.Preamble

/-- The normalization eq:normal: `A` is `0`-homogeneous and `H` is `1`-homogeneous along
rays, i.e. `A (t ξ) = A ξ` and `H (t ξ) = t H ξ` for all `t > 0` and `ξ ≠ 0`. -/
structure NormalizedAH (m : ℕ)
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ) : Prop where
  A_homog : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin m)), 0 < t → ξ ≠ 0 → A (t • ξ) = A ξ
  H_homog : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin m)), 0 < t → ξ ≠ 0 → H (t • ξ) = t * H ξ
