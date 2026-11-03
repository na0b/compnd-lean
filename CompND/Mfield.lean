import CompND.Preamble

/-- The matrix `𝓜(x, ζ)` of eq:Mxz, with the `1`-jet `D` in the role of `ζ = ∇u(x)`:
`𝓜(x,D)ᵢⱼ = ½ (D (Dσʲ(x) σⁱ(x)) + D (Dσⁱ(x) σʲ(x)))`. -/
noncomputable def Mfield {n m : ℕ}
    (sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    (1 / 2) * (D (fderiv ℝ (fun y => sig y j) x (sig x i))
             + D (fderiv ℝ (fun y => sig y i) x (sig x j)))
