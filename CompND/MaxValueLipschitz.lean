import CompND.BoundaryCore
import CompND.MaxTranslate
import CompND.InverseUniquenessAndDistanceSymmetry

/-- lem:Mlip, eq:lip: the translated maximum value `M_δ` is `d`-Lipschitz on the ball
`B_δ(0)`, with constant the `d`-Lipschitz constant `L_u` of `u` on the compact core
`K_{ρ₂}`: `|M_δ(h) - M_δ(h')| ≤ L_u d(h,h')`. -/
theorem MaxValueLipschitz (G : CarnotSetting)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (δ ρ₁ ρ₂ : ℝ) (hδ : 0 < δ)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (Lu : ℝ) (hLu : 0 ≤ Lu)
    (hLip : ∀ a ∈ BoundaryCore G Ω ρ₂, ∀ b ∈ BoundaryCore G Ω ρ₂,
      |u a - u b| ≤ Lu * G.hnorm (G.mul (-b) a))
    (hattain : ∀ g : EuclideanSpace ℝ (Fin G.n), G.hnorm g < δ →
      ∃ x ∈ TranslatedDomain G Ω δ,
        IsMaxOn (fun y => u (G.mul y g) - v y) (TranslatedDomain G Ω δ) x ∧
        MaxTranslate G Ω δ u v g = u (G.mul x g) - v x)
    (hAcore : ∀ g : EuclideanSpace ℝ (Fin G.n), G.hnorm g < δ →
      ∀ x ∈ TranslatedDomain G Ω δ,
        IsMaxOn (fun y => u (G.mul y g) - v y) (TranslatedDomain G Ω δ) x →
          x ∈ BoundaryCore G Ω ρ₁)
    (htrans : ∀ x ∈ BoundaryCore G Ω ρ₁, ∀ g : EuclideanSpace ℝ (Fin G.n),
      G.hnorm g < δ → G.mul x g ∈ BoundaryCore G Ω ρ₂) :
    ∀ h h' : EuclideanSpace ℝ (Fin G.n), G.hnorm h < δ → G.hnorm h' < δ →
      |MaxTranslate G Ω δ u v h - MaxTranslate G Ω δ u v h'|
        ≤ Lu * G.hnorm (G.mul (-h') h) := by
  -- ===== Step 0: `-(a*b) = (-b)*(-a)` (1) and the symmetry (2) of `d` =====
  obtain ⟨-, hnegmul, hdsymm⟩ := InverseUniquenessAndDistanceSymmetry G
  -- ===== Step 1: the exact translation identity (3).  No quasi-triangle constant. =====
  have hstep1 : ∀ x a b : EuclideanSpace ℝ (Fin G.n),
      G.hnorm (G.mul (-(G.mul x b)) (G.mul x a)) = G.hnorm (G.mul (-b) a) := by
    intro x a b
    have hc : G.mul (-x) (G.mul x a) = a := by
      rw [← G.mul_assoc, G.neg_mul, G.zero_mul]
    calc G.hnorm (G.mul (-(G.mul x b)) (G.mul x a))
        = G.hnorm (G.mul (G.mul (-b) (-x)) (G.mul x a)) := by rw [hnegmul]
      _ = G.hnorm (G.mul (-b) (G.mul (-x) (G.mul x a))) := by rw [G.mul_assoc]
      _ = G.hnorm (G.mul (-b) a) := by rw [hc]
  -- ===== Step 2: the one-sided estimate (9), stated once for an ordered pair =====
  have hone : ∀ a b : EuclideanSpace ℝ (Fin G.n), G.hnorm a < δ → G.hnorm b < δ →
      MaxTranslate G Ω δ u v a - MaxTranslate G Ω δ u v b
        ≤ Lu * G.hnorm (G.mul (-b) a) := by
    intro a b ha hb
    -- (4) and (5)
    obtain ⟨x, hx, hxmax, hxeq⟩ := hattain a ha
    obtain ⟨x', hx', hx'max, hx'eq⟩ := hattain b hb
    -- (6): maximality at `x'` applied at the point `x ∈ Ω_δ`
    have h6 : u (G.mul x b) - v x ≤ u (G.mul x' b) - v x' := isMaxOn_iff.1 hx'max x hx
    -- (8)
    have hxK1 : x ∈ BoundaryCore G Ω ρ₁ := hAcore a ha x hx hxmax
    have hxaK : G.mul x a ∈ BoundaryCore G Ω ρ₂ := htrans x hxK1 a ha
    have hxbK : G.mul x b ∈ BoundaryCore G Ω ρ₂ := htrans x hxK1 b hb
    have hLipab : |u (G.mul x a) - u (G.mul x b)|
        ≤ Lu * G.hnorm (G.mul (-(G.mul x b)) (G.mul x a)) := hLip _ hxaK _ hxbK
    rw [hstep1 x a b] at hLipab
    have hup := le_trans (le_abs_self _) hLipab
    -- (7) plus the Lipschitz bound
    rw [hxeq, hx'eq]
    linarith
  -- ===== Step 3: conclusion =====
  intro h h' hh hh'
  refine abs_sub_le_iff.2 ⟨hone h h' hh hh', ?_⟩
  have h2 := hone h' h hh' hh
  rwa [hdsymm h' h] at h2
