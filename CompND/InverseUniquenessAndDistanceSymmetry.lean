import CompND.CarnotSetting

/-- Uniqueness of inverses in the group `(ℝⁿ, *)` of a Carnot setting, the resulting
anti-automorphism identity `(a * b)⁻¹ = b⁻¹ * a⁻¹` for the inverse `x ↦ -x` of section
subsec:carnot, and the symmetry `d(a,b) = d(b,a)` of the left-invariant quasi-distance
`d(x,y) = ‖y⁻¹ * x‖` induced by the homogeneous norm eq:homnorm. -/
theorem InverseUniquenessAndDistanceSymmetry (G : CarnotSetting) :
    (∀ a b : EuclideanSpace ℝ (Fin G.n), G.mul a b = 0 → b = -a) ∧
    (∀ a b : EuclideanSpace ℝ (Fin G.n), -(G.mul a b) = G.mul (-b) (-a)) ∧
    (∀ a b : EuclideanSpace ℝ (Fin G.n),
      G.hnorm (G.mul (-b) a) = G.hnorm (G.mul (-a) b)) := by
  -- Uniqueness of inverses: a right inverse of `a` equals the given left inverse `-a`.
  have hinvu : ∀ a b : EuclideanSpace ℝ (Fin G.n), G.mul a b = 0 → b = -a := by
    intro a b h
    calc b = G.mul 0 b := (G.zero_mul b).symm
      _ = G.mul (G.mul (-a) a) b := by rw [G.neg_mul]
      _ = G.mul (-a) (G.mul a b) := G.mul_assoc _ _ _
      _ = G.mul (-a) 0 := by rw [h]
      _ = -a := G.mul_zero _
  -- `(-b) * (-a)` is a right inverse of `a * b`, so by uniqueness it is `-(a * b)`.
  have hnegmul : ∀ a b : EuclideanSpace ℝ (Fin G.n),
      -(G.mul a b) = G.mul (-b) (-a) := by
    intro a b
    refine (hinvu (G.mul a b) (G.mul (-b) (-a)) ?_).symm
    calc G.mul (G.mul a b) (G.mul (-b) (-a))
        = G.mul a (G.mul b (G.mul (-b) (-a))) := G.mul_assoc _ _ _
      _ = G.mul a (G.mul (G.mul b (-b)) (-a)) := by rw [G.mul_assoc]
      _ = G.mul a (G.mul 0 (-a)) := by rw [G.mul_neg]
      _ = G.mul a (-a) := by rw [G.zero_mul]
      _ = 0 := G.mul_neg a
  -- Symmetry of `d`: the two arguments are inverse to one another, and `‖·‖` is even.
  refine ⟨hinvu, hnegmul, fun a b => ?_⟩
  have h : G.mul (-a) b = -(G.mul (-b) a) := by
    rw [hnegmul (-b) a, neg_neg]
  rw [h, G.hnorm_neg]
