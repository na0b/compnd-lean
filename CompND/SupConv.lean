import CompND.CarnotSetting

/-- The sup-convolution `wᵋ` of eq:supinfconv, in the left-translate form eq:leftsup:
`wᵋ x = sup { w (z * x) - ‖z‖ ^ q / (2 ε) : z * x ∈ closure Ω }` with `q = 2 r!`. -/
noncomputable def SupConv (G : CarnotSetting) (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (w : EuclideanSpace ℝ (Fin G.n) → ℝ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin G.n)) : ℝ :=
  ⨆ z : {z : EuclideanSpace ℝ (Fin G.n) // G.mul z x ∈ closure Ω},
    w (G.mul z.1 x) - G.hnorm z.1 ^ (2 * Nat.factorial G.r) / (2 * ε)
