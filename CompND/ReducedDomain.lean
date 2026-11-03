import CompND.CarnotSetting

/-- The reduced domain `Ω[ε]` of eq:redom:
`{ x ∈ Ω : inf_{y ∉ Ω} ‖y * x⁻¹‖ ^ q > (1 + 4 R) ε }` with `q = 2 r!`. -/
noncomputable def ReducedDomain (G : CarnotSetting) (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (R ε : ℝ) : Set (EuclideanSpace ℝ (Fin G.n)) :=
  {x ∈ Ω | (1 + 4 * R) * ε <
    ⨅ y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω},
      G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r)}
