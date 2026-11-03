import CompND.TranslatedDomain

/-- The first half of eq:MAl: the value `M_δ(h) = sup_{x ∈ Ω_δ} (u (x * h) - v x)` of the
right translate `u_h = u (· * h)` against `v` over the inner domain `Ω_δ`
(\noderef{TranslatedDomain}). -/
noncomputable def MaxTranslate (G : CarnotSetting) (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (δ : ℝ) (u v : EuclideanSpace ℝ (Fin G.n) → ℝ) (h : EuclideanSpace ℝ (Fin G.n)) : ℝ :=
  ⨆ x : {x : EuclideanSpace ℝ (Fin G.n) // x ∈ TranslatedDomain G Ω δ},
    (u (G.mul x.1 h) - v x.1)
