import CompND.CarnotGroup

/-- A Carnot group together with the homogeneous norm eq:homnorm and the structural
properties of section subsec:carnot that the development uses: evenness, `‖hexp ζ‖ = |ζ|`,
smoothness of `‖·‖ ^ (2 r!)`, the two inequalities eq:trinangle, Hölder equivalence of the
left-invariant distance with the Euclidean one on bounded sets, connectedness of balls, and
properness of the homogeneous norm. -/
structure CarnotNorm extends CarnotGroup where
  /-- The homogeneous norm `‖x‖` of eq:homnorm. -/
  hnorm : EuclideanSpace ℝ (Fin n) → ℝ
  hnorm_nonneg : ∀ x, 0 ≤ hnorm x
  hnorm_eq_zero : ∀ x, hnorm x = 0 ↔ x = 0
  hnorm_neg : ∀ x, hnorm (-x) = hnorm x
  hnorm_cont : Continuous hnorm
  hnorm_hexp : ∀ ζ, hnorm (hexp ζ) = ‖ζ‖
  hnorm_pow_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => hnorm x ^ (2 * Nat.factorial r))
  hnorm_mul_le : ∀ ν : ℝ, 0 < ν → ∃ c : ℝ, 0 < c ∧ ∀ x y,
    hnorm x < ν → hnorm y < ν → hnorm (mul x y) ≤ c * (hnorm x + hnorm y)
  hnorm_conj_le : ∀ ν : ℝ, 0 < ν → ∃ c : ℝ, 0 < c ∧ ∀ x y,
    hnorm x < ν → hnorm y < ν → hnorm (mul (mul (-x) y) x) ≤ c * hnorm y ^ ((1 : ℝ) / r)
  holder_equiv : ∀ ν : ℝ, 0 < ν → ∃ c : ℝ, 0 < c ∧ ∀ x y, ‖x‖ ≤ ν → ‖y‖ ≤ ν →
    c⁻¹ * ‖x - y‖ ≤ hnorm (mul (-y) x) ∧ hnorm (mul (-y) x) ≤ c * ‖x - y‖ ^ ((1 : ℝ) / r)
  ball_connected : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
    IsConnected {y | hnorm (mul (-x) y) < ρ}
  /-- The homogeneous norm is proper: each of its sublevel sets is bounded. This is
  eq:homnorm read off coordinatewise, and it is what makes the infimum of eq:redom locally
  an infimum over a compact set of `y`. -/
  hnorm_proper : ∀ C : ℝ, Bornology.IsBounded {x : EuclideanSpace ℝ (Fin n) | hnorm x ≤ C}
