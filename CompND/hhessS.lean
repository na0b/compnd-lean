import CompND.Mfield

/-- The symmetrized horizontal second derivative of a `2`-jet `(D, B)` at `x`:
`σᵀ D²u σ + 𝓜(x, ∇u)` of eq:sigrad, read on jets. -/
noncomputable def hhessS {n m : ℕ}
    (sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of (fun i j => B (sig x i) (sig x j)) + Mfield sig x D
