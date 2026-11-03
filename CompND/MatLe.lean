import CompND.Preamble

/-- The order `A ≤ B` on symmetric matrices of eq:matord: `⟨Aξ,ξ⟩ ≤ ⟨Bξ,ξ⟩` for all `ξ`. -/
def MatLe {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ ξ : EuclideanSpace ℝ (Fin m),
    (∑ i, ∑ j, A i j * ξ j * ξ i) ≤ ∑ i, ∑ j, B i j * ξ j * ξ i
