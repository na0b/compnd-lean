import CompND.Preamble

/-- The horizontal gradient of a `1`-jet `D` at `x` for the frame `sig`:
`(hgrad sig x D) i = D (sig x i)`. This is `𝔛u = σ(x)ᵀ ∇u` of eq:sigrad. -/
noncomputable def hgrad {n m : ℕ}
    (sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => D (sig x i))
