import CompND.CarnotNorm
import CompND.LieHull
import CompND.TwiceDiffAt
import CompND.HasPansuGradAt
import CompND.hgrad
import CompND.hhessS

/-- The sub-elliptic setting: a Carnot group with its homogeneous norm, together with the
horizontal frame `sig` (`Xᵢ = σⁱ(x) · ∇`) and, at the level of jets, the facts of section
subsec:carnot that the development uses — Hörmander's rank condition eq:horcond,
the Taylor formula eq:taylor2, left-invariance of the horizontal derivatives, and the form
of the `Xᵢ` on functions of the first layer. -/
structure CarnotSetting extends CarnotNorm where
  /-- The horizontal frame: `sig x i` is `σⁱ(x)`, the value at `x` of the `i`-th
  generator. -/
  sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n)
  sig_smooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => sig x i)
  sig_indep : ∀ x, LinearIndependent ℝ (sig x)
  /-- Hörmander's rank condition eq:horcond. -/
  hormander : ∀ x : EuclideanSpace ℝ (Fin n),
    Submodule.span ℝ
      ((fun V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) => V x) ''
        LieHull sig) = ⊤
  /-- The first-order Taylor formula eq:taylor2. -/
  taylor2 : ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
      (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ), HasFDerivAt u D x →
      HasPansuGradAt mul pi1 hnorm u x (hgrad sig x D)
  /-- Left-invariance of the horizontal derivatives, at the level of second-order jets. -/
  leftJet : ∀ (h x : EuclideanSpace ℝ (Fin n)) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      TwiceDiffAt φ (mul h x) D B →
      ∃ (D' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (B' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
        TwiceDiffAt (fun y => φ (mul h y)) x D' B' ∧
        hgrad sig x D' = hgrad sig (mul h x) D ∧
        hhessS sig x D' B' = hhessS sig (mul h x) D B
  /-- The form of the `Xᵢ`: on a function of the first layer the horizontal derivatives
  are the Euclidean ones of the function on `ℝᵐ`. -/
  pi1Jet : ∀ (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin n))
      (E : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ),
      TwiceDiffAt ψ (pi1 x) E C →
      ∃ (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
        TwiceDiffAt (fun y => ψ (pi1 y)) x D B ∧
        hgrad sig x D =
          (EuclideanSpace.equiv (Fin m) ℝ).symm
            (fun i => E (EuclideanSpace.single i (1 : ℝ))) ∧
        hhessS sig x D B =
          Matrix.of fun i j =>
            C (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
