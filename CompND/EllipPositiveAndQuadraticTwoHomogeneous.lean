import CompND.Ellip
import CompND.StructureConditionsES

/-- Two elementary facts about eq:ell used throughout rem:scale: condition (E) of
`StructureConditionsES` says exactly that `𝓔 A η > 0` for `η ≠ 0`, and the quadratic form
`η ↦ ∑ᵢ∑ⱼ Mᵢⱼ ηⱼ ηᵢ` is `2`-homogeneous in its vector slot, for every fixed matrix `M`. -/
theorem EllipPositiveAndQuadraticTwoHomogeneous {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ) (hAH : StructureConditionsES m A H) :
    (∀ η : EuclideanSpace ℝ (Fin m), η ≠ 0 → 0 < Ellip A η) ∧
    (∀ (M : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (η : EuclideanSpace ℝ (Fin m)),
      ∑ i, ∑ j, M i j * (s • η) j * (s • η) i
        = s ^ 2 * ∑ i, ∑ j, M i j * η j * η i) := by
  refine ⟨fun η hη => hAH.ellipticity η hη, fun M s η => ?_⟩
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
