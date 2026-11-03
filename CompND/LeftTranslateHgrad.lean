import CompND.CarnotSetting
import CompND.hgrad

/-- First-order left-invariance of the horizontal gradient: if `u` is differentiable at
`g * x` with derivative `D` and the left translate `u ∘ L_g` is differentiable at `x` with
derivative `D'`, then `𝔛(u ∘ L_g)(x) = (𝔛u)(g * x)`. This is the first-order companion of
`CarnotSetting.leftJet`, which is a statement about `2`-jets and therefore unusable when the
function is only once differentiable. -/
theorem LeftTranslateHgrad (G : CarnotSetting)
    (u : EuclideanSpace ℝ (Fin G.n) → ℝ) (g x : EuclideanSpace ℝ (Fin G.n))
    (D D' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
    (hD : HasFDerivAt u D (G.mul g x))
    (hD' : HasFDerivAt (fun y => u (G.mul g y)) D' x) :
    hgrad G.sig x D' = hgrad G.sig (G.mul g x) D := by
  -- Uniqueness of the Pansu horizontal differential, tested on the horizontal
  -- one-parameter subgroups `hexp (t • ζ)`.
  have puniq : ∀ (f : EuclideanSpace ℝ (Fin G.n) → ℝ) (y : EuclideanSpace ℝ (Fin G.n))
      (a b : EuclideanSpace ℝ (Fin G.m)),
      HasPansuGradAt G.mul G.pi1 G.hnorm f y a →
      HasPansuGradAt G.mul G.pi1 G.hnorm f y b → a = b := by
    intro f y a b ha hb
    by_contra hne
    set ζ : EuclideanSpace ℝ (Fin G.m) := a - b with hζ
    have hζne : ζ ≠ 0 := sub_ne_zero_of_ne hne
    have hnζ : 0 < ‖ζ‖ := norm_pos_iff.mpr hζne
    obtain ⟨δ₁, hδ₁, h₁⟩ := ha (‖ζ‖ / 4) (by positivity)
    obtain ⟨δ₂, hδ₂, h₂⟩ := hb (‖ζ‖ / 4) (by positivity)
    set δ : ℝ := min δ₁ δ₂ with hδdef
    have hδ : 0 < δ := lt_min hδ₁ hδ₂
    set t : ℝ := δ / (2 * ‖ζ‖) with htdef
    have ht : 0 < t := by positivity
    set gg : EuclideanSpace ℝ (Fin G.n) := G.hexp (t • ζ) with hgdef
    have hng : G.hnorm gg = t * ‖ζ‖ := by
      rw [hgdef, G.hnorm_hexp, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hngval : G.hnorm gg = δ / 2 := by
      rw [hng, htdef]; field_simp
    have hlt : G.hnorm gg < δ := by rw [hngval]; linarith
    have hpi : G.pi1 gg = t • ζ := by rw [hgdef, G.pi1_hexp]
    have e₁ := h₁ gg (lt_of_lt_of_le hlt (min_le_left _ _))
    have e₂ := h₂ gg (lt_of_lt_of_le hlt (min_le_right _ _))
    have hnormsq : ‖ζ‖ ^ 2 = ∑ i, ζ i * ζ i := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]; ring
    have key : (∑ i, a i * (G.pi1 gg) i) - (∑ i, b i * (G.pi1 gg) i) = t * ‖ζ‖ ^ 2 := by
      rw [hpi, ← Finset.sum_sub_distrib, hnormsq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsm : ((t • ζ : EuclideanSpace ℝ (Fin G.m)) i) = t * ζ i := rfl
      have hz : ζ i = a i - b i := rfl
      rw [hsm, hz]; ring
    obtain ⟨b1, b2⟩ := abs_le.mp e₁
    obtain ⟨c1, c2⟩ := abs_le.mp e₂
    rw [hng] at b1 b2 c1 c2
    nlinarith [key, hnζ, ht]
  -- the two Pansu expansions
  have P1 : HasPansuGradAt G.mul G.pi1 G.hnorm (fun y => u (G.mul g y)) x
      (hgrad G.sig x D') := G.taylor2 _ x D' hD'
  have P2 : HasPansuGradAt G.mul G.pi1 G.hnorm u (G.mul g x)
      (hgrad G.sig (G.mul g x) D) := G.taylor2 u (G.mul g x) D hD
  have P2' : HasPansuGradAt G.mul G.pi1 G.hnorm (fun y => u (G.mul g y)) x
      (hgrad G.sig (G.mul g x) D) := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := P2 ε hε
    refine ⟨δ, hδ, fun p hp => ?_⟩
    have hthis := h p hp
    rwa [G.mul_assoc] at hthis
  exact puniq _ x _ _ P1 P2'
