import CompND.Preamble

/-- The group-level data of a Carnot group of step `r` with `m` generators, written in the
exponential coordinates of section subsec:carnot: a smooth group law on `ℝⁿ` with neutral
element `0` and inverse `x ↦ -x`, the first-layer projection `π₁` onto `ℝᵐ`, and the
horizontal exponential `hexp`. -/
structure CarnotGroup where
  /-- The topological dimension of the group. -/
  n : ℕ
  /-- The number of generators, i.e. the dimension of the first layer. -/
  m : ℕ
  /-- The step of the stratification. -/
  r : ℕ
  one_le_r : 1 ≤ r
  /-- The group law `x * y`. -/
  mul : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_zero : ∀ x, mul x 0 = x
  zero_mul : ∀ x, mul 0 x = x
  mul_neg : ∀ x, mul x (-x) = 0
  neg_mul : ∀ x, mul (-x) x = 0
  mul_smooth : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => mul p.1 p.2)
  /-- The projection onto the first layer. -/
  pi1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)
  pi1_mul : ∀ x y, pi1 (mul x y) = pi1 x + pi1 y
  /-- The horizontal exponential `ζ ↦ exp (∑ i, ζ i • Xᵢ)`. -/
  hexp : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)
  hexp_cont : Continuous hexp
  pi1_hexp : ∀ ζ, pi1 (hexp ζ) = ζ
  abelian_of_step_one : r = 1 → ∀ x y, mul x y = mul y x
