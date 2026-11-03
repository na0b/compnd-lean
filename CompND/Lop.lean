import CompND.hgrad
import CompND.hhessS

/-- The operator `ℒ` of eq:maineq evaluated on a `2`-jet, which is eq:FtoG read literally:
`Lop sig A H x D B = -Tr (A (𝔛u) 𝔛𝔛ˢu) + H (𝔛u)`. -/
noncomputable def Lop {n m : ℕ}
    (sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) : ℝ :=
  -(A (hgrad sig x D) * hhessS sig x D B).trace + H (hgrad sig x D)
