import CompND.CarnotSetting
import CompND.Lop

/-- Viscosity sub-solution of `ℒ u = 0` in `Ω`, in the sense of def:visc: `u` is upper
semi-continuous on `Ω` and `Lop ≤ 0` at the second-order jet of every `C²` test function
touching `u` from above on `Ω` with non-vanishing horizontal gradient. -/
def IsViscSubsol (G : CarnotSetting)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (u : EuclideanSpace ℝ (Fin G.n) → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧
  ∀ x ∈ Ω, ∀ φ : EuclideanSpace ℝ (Fin G.n) → ℝ, ContDiffOn ℝ 2 φ Ω →
    IsMaxOn (fun y => u y - φ y) Ω x →
    ∀ (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      TwiceDiffAt φ x D B → hgrad G.sig x D ≠ 0 → Lop G.sig A H x D B ≤ 0
