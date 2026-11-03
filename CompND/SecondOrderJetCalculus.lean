import CompND.TwiceDiffAt

/-- The second-order (Peano) jet calculus of `TwiceDiffAt` that the comparison
argument runs on, for jets at a point of `ℝᴺ`: (1) a cubic remainder bound on the unit ball
around the base point already forces a jet; (2) jets add, (3) negate and (4) subtract, with
the jet data adding, negating and subtracting accordingly; and (5) a linear functional
`y ↦ ∑ᵢ pᵢ yᵢ` has, at every point, the jet `(⟪p, ·⟫, 0)` with vanishing second-order
part. -/
theorem SecondOrderJetCalculus {N : ℕ} :
    (∀ (g : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N))
        (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) (C : ℝ),
      (∀ a b, B a b = B b a) → 0 ≤ C →
      (∀ y, ‖y - z‖ ≤ 1 →
        |g y - g z - D (y - z) - 1 / 2 * B (y - z) (y - z)| ≤ C * ‖y - z‖ ^ 3) →
      TwiceDiffAt g z D B) ∧
    (∀ (w w' : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N))
        (D D' : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (B B' : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt w z D B → TwiceDiffAt w' z D' B' →
      TwiceDiffAt (fun y => w y + w' y) z (D + D') (B + B')) ∧
    (∀ (w : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N))
        (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt w z D B → TwiceDiffAt (fun y => -w y) z (-D) (-B)) ∧
    (∀ (w w' : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N))
        (D D' : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (B B' : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt w z D B → TwiceDiffAt w' z D' B' →
      TwiceDiffAt (fun y => w y - w' y) z (D - D') (B - B')) ∧
    (∀ p z : EuclideanSpace ℝ (Fin N),
      TwiceDiffAt (fun y => ∑ i, p i * y i) z (innerSL ℝ p) 0) := by
  -- (1): a CUBIC remainder bound on the unit ball already gives a second-order jet.  This
  -- is the form in which the comparison argument instantiates it, at concrete polynomials.
  have jetOfCubicBound : ∀ (g : EuclideanSpace ℝ (Fin N) → ℝ)
      (z : EuclideanSpace ℝ (Fin N)) (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) (C : ℝ),
      (∀ a b, B a b = B b a) → 0 ≤ C →
      (∀ y, ‖y - z‖ ≤ 1 →
        |g y - g z - D (y - z) - 1 / 2 * B (y - z) (y - z)| ≤ C * ‖y - z‖ ^ 3) →
      TwiceDiffAt g z D B := by
    intro g z D B C hsymm hC hbd
    refine ⟨hsymm, fun ε hε => ⟨min 1 (ε / (C + 1)),
      lt_min one_pos (by positivity), fun y hy => ?_⟩⟩
    have h1 : ‖y - z‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hy (min_le_left _ _))
    have h2 : ‖y - z‖ < ε / (C + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    have hCN : C * ‖y - z‖ ≤ ε := by
      have h3 : C * ‖y - z‖ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left h2.le hC
      have h4 : C * (ε / (C + 1)) ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith only [hε.le, hC]
      linarith only [h3, h4]
    refine (hbd y h1).trans ?_
    calc C * ‖y - z‖ ^ 3 = C * ‖y - z‖ * ‖y - z‖ ^ 2 := by ring
      _ ≤ ε * ‖y - z‖ ^ 2 := mul_le_mul_of_nonneg_right hCN (by positivity)
  -- (2), (3), (4): second-order jets add, negate, and subtract.
  have jetAdd : ∀ (w w' : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N))
      (D D' : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (B B' : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt w z D B → TwiceDiffAt w' z D' B' →
      TwiceDiffAt (fun y => w y + w' y) z (D + D') (B + B') := by
    intro w w' z D D' B B' h h'
    refine ⟨fun a b => ?_, fun ε hε => ?_⟩
    · simp only [add_apply]
      rw [h.1 a b, h'.1 a b]
    · obtain ⟨δ₁, hδ₁, hb₁⟩ := h.2 (ε / 2) (by positivity)
      obtain ⟨δ₂, hδ₂, hb₂⟩ := h'.2 (ε / 2) (by positivity)
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy => ?_⟩
      have e1 := hb₁ y (lt_of_lt_of_le hy (min_le_left _ _))
      have e2 := hb₂ y (lt_of_lt_of_le hy (min_le_right _ _))
      have hid : w y + w' y - (w z + w' z) - (D + D') (y - z)
          - 1 / 2 * (B + B') (y - z) (y - z)
          = (w y - w z - D (y - z) - 1 / 2 * B (y - z) (y - z))
            + (w' y - w' z - D' (y - z) - 1 / 2 * B' (y - z) (y - z)) := by
        simp only [add_apply]
        ring
      rw [hid]
      refine (abs_add_le _ _).trans ?_
      linarith only [e1, e2]
  have jetNeg : ∀ (w : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N))
      (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt w z D B → TwiceDiffAt (fun y => -w y) z (-D) (-B) := by
    intro w z D B h
    refine ⟨fun a b => ?_, fun ε hε => ?_⟩
    · simp only [neg_apply]
      rw [h.1 a b]
    · obtain ⟨δ, hδ, hb⟩ := h.2 ε hε
      refine ⟨δ, hδ, fun y hy => ?_⟩
      have hid : -w y - -w z - (-D) (y - z) - 1 / 2 * (-B) (y - z) (y - z)
          = -(w y - w z - D (y - z) - 1 / 2 * B (y - z) (y - z)) := by
        simp only [neg_apply]
        ring
      rw [hid, abs_neg]
      exact hb y hy
  have jetSub : ∀ (w w' : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N))
      (D D' : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (B B' : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt w z D B → TwiceDiffAt w' z D' B' →
      TwiceDiffAt (fun y => w y - w' y) z (D - D') (B - B') := by
    intro w w' z D D' B B' h h'
    have hA := jetAdd w (fun y => -w' y) z D (-D') B (-B') h (jetNeg w' z D' B' h')
    refine ⟨fun a b => ?_, fun ε hε => ?_⟩
    · simp only [sub_apply]
      rw [h.1 a b, h'.1 a b]
    · obtain ⟨δ, hδ, hb⟩ := hA.2 ε hε
      refine ⟨δ, hδ, fun y hy => ?_⟩
      have hb' := hb y hy
      have hid : w y - w' y - (w z - w' z) - (D - D') (y - z)
            - 1 / 2 * (B - B') (y - z) (y - z)
          = w y + -w' y - (w z + -w' z) - (D + -D') (y - z)
            - 1 / 2 * (B + -B') (y - z) (y - z) := by
        simp only [sub_apply, add_apply,
          neg_apply]
        ring
      rw [hid]
      exact hb'
  -- (5): the inner-product form of the linear functional, and its (zero) second-order jet
  have hinnerSum : ∀ p w : EuclideanSpace ℝ (Fin N), (inner ℝ p w : ℝ) = ∑ i, p i * w i := by
    intro p w
    simp [PiLp.inner_apply, mul_comm]
  have jetLinear : ∀ p z : EuclideanSpace ℝ (Fin N),
      TwiceDiffAt (fun y => ∑ i, p i * y i) z (innerSL ℝ p) 0 := by
    intro p z
    refine jetOfCubicBound _ z (innerSL ℝ p) 0 0 (by simp) le_rfl (fun y _ => ?_)
    have hs : ∑ i, p i * (y - z) i = (∑ i, p i * y i) - ∑ i, p i * z i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.sub_apply]; ring
    simp only [innerSL_apply_apply, zero_apply, hinnerSum, hs]
    simp
  exact ⟨jetOfCubicBound, jetAdd, jetNeg, jetSub, jetLinear⟩
