import CompND.TwiceDiffAt
import CompND.hgrad
import CompND.hhessS
import CompND.MatLe

/-- The elementary observation opening subsec:semicomp: at a local maximum of `u - v` at
which both have second-order jets, the first jets agree and the second jets are ordered;
transporting through eq:sigrad, the horizontal gradients agree and the symmetrized
horizontal second derivatives are ordered. -/
theorem LocalMaxSecondOrder {n m : ℕ}
    (sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n))
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (Du Dv : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (Bu Bv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hu : TwiceDiffAt u x₀ Du Bu) (hv : TwiceDiffAt v x₀ Dv Bv)
    (hmax : IsLocalMax (fun y => u y - v y) x₀) :
    Du = Dv ∧
    (∀ h : EuclideanSpace ℝ (Fin n), Bu h h ≤ Bv h h) ∧
    hgrad sig x₀ Du = hgrad sig x₀ Dv ∧
    MatLe (hhessS sig x₀ Du Bu) (hhessS sig x₀ Dv Bv) := by
  obtain ⟨r, hr, hmx⟩ := Metric.eventually_nhds_iff.1 hmax
  have hmx' : ∀ y : EuclideanSpace ℝ (Fin n), ‖y - x₀‖ < r → u y - v y ≤ u x₀ - v x₀ :=
    fun y hy => hmx (by rwa [dist_eq_norm])
  have hlin : ∀ (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (τ : ℝ)
      (h : EuclideanSpace ℝ (Fin n)), D (τ • h) = τ * D h := by
    intro D τ h; simp [map_smul]
  have hbil : ∀ (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (τ : ℝ) (h : EuclideanSpace ℝ (Fin n)), B (τ • h) (τ • h) = τ ^ 2 * B h h := by
    intro B τ h; simp [map_smul]; ring
  -- Step 1: the key inequality
  have key : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : EuclideanSpace ℝ (Fin n), ‖y - x₀‖ < δ →
      Du (y - x₀) - Dv (y - x₀)
        + (1 / 2) * (Bu (y - x₀) (y - x₀) - Bv (y - x₀) (y - x₀))
        ≤ 2 * ε * ‖y - x₀‖ ^ 2 := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, h1⟩ := hu.2 ε hε
    obtain ⟨δ₂, hδ₂, h2⟩ := hv.2 ε hε
    refine ⟨min r (min δ₁ δ₂), by positivity, fun y hy => ?_⟩
    have hyr : ‖y - x₀‖ < r := lt_of_lt_of_le hy (min_le_left _ _)
    have hy1 : ‖y - x₀‖ < δ₁ :=
      lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_left _ _))
    have hy2 : ‖y - x₀‖ < δ₂ :=
      lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_right _ _))
    have e1 := abs_le.1 (h1 y hy1)
    have e2 := abs_le.1 (h2 y hy2)
    have hm := hmx' y hyr
    linarith [e1.1, e1.2, e2.1, e2.2, hm]
  -- Step 2: Du = Dv
  have hDle : ∀ h : EuclideanSpace ℝ (Fin n), Du h ≤ Dv h := by
    intro h
    by_cases h0 : h = 0
    · subst h0; simp
    have hh : 0 < ‖h‖ := norm_pos_iff.2 h0
    obtain ⟨δ, hδ, hk⟩ := key 1 one_pos
    set κ : ℝ := 2 * ‖h‖ ^ 2 - (1 / 2) * (Bu h h - Bv h h) with hκ
    have step : ∀ τ : ℝ, 0 < τ → τ * ‖h‖ < δ → Du h - Dv h ≤ τ * κ := by
      intro τ hτ hτδ
      have hsub : (x₀ + τ • h) - x₀ = τ • h := by abel
      have hy : ‖(x₀ + τ • h) - x₀‖ < δ := by
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]; exact hτδ
      have hres := hk (x₀ + τ • h) hy
      rw [hsub, hlin Du, hlin Dv, hbil Bu, hbil Bv, norm_smul, Real.norm_eq_abs,
        abs_of_pos hτ] at hres
      have hτ2 : (0 : ℝ) < τ := hτ
      have hmul : τ * (Du h - Dv h) ≤ τ * (τ * κ) := by rw [hκ]; nlinarith [hres]
      exact le_of_mul_le_mul_left hmul hτ2
    have hzero : Du h - Dv h ≤ 0 := by
      have hden : (0 : ℝ) < |κ| + 1 := by positivity
      refine le_of_forall_pos_le_add ?_
      intro η hη
      set τ : ℝ := min (η / (|κ| + 1)) (δ / (2 * ‖h‖)) with hτdef
      have hτpos : 0 < τ := lt_min (by positivity) (by positivity)
      have hτh : τ * ‖h‖ < δ := by
        have h1 : τ ≤ δ / (2 * ‖h‖) := min_le_right _ _
        have h2 : τ * ‖h‖ ≤ (δ / (2 * ‖h‖)) * ‖h‖ :=
          mul_le_mul_of_nonneg_right h1 hh.le
        have h3 : (δ / (2 * ‖h‖)) * ‖h‖ = δ / 2 := by field_simp
        rw [h3] at h2; linarith
      have hA := step τ hτpos hτh
      have hB : τ * κ ≤ η := by
        have c1 : τ * κ ≤ τ * |κ| := by nlinarith [le_abs_self κ, hτpos.le]
        have c2 : τ * |κ| ≤ (η / (|κ| + 1)) * |κ| :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg κ)
        have c3 : (η / (|κ| + 1)) * |κ| ≤ η := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hden]
          nlinarith [hη.le, abs_nonneg κ]
        linarith
      linarith
    linarith
  have hDeq : Du = Dv := by
    ext h
    refine le_antisymm (hDle h) ?_
    have := hDle (-h)
    simp only [map_neg] at this
    linarith
  -- Step 3: Bu h h ≤ Bv h h
  have hBle : ∀ h : EuclideanSpace ℝ (Fin n), Bu h h ≤ Bv h h := by
    intro h
    by_cases h0 : h = 0
    · subst h0; simp
    have hh : 0 < ‖h‖ := norm_pos_iff.2 h0
    refine le_of_forall_pos_le_add ?_
    intro η hη
    have hden : (0 : ℝ) < 4 * ‖h‖ ^ 2 + 1 := by positivity
    set ε : ℝ := η / (4 * ‖h‖ ^ 2 + 1) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    obtain ⟨δ, hδ, hk⟩ := key ε hεpos
    set τ : ℝ := δ / (2 * ‖h‖) with hτdef
    have hτpos : 0 < τ := by rw [hτdef]; positivity
    have hτh : τ * ‖h‖ < δ := by
      have h3 : τ * ‖h‖ = δ / 2 := by rw [hτdef]; field_simp
      rw [h3]; linarith
    have hsub : (x₀ + τ • h) - x₀ = τ • h := by abel
    have hy : ‖(x₀ + τ • h) - x₀‖ < δ := by
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hτpos]; exact hτh
    have hres := hk (x₀ + τ • h) hy
    rw [hsub, hlin Du, hlin Dv, hbil Bu, hbil Bv, norm_smul, Real.norm_eq_abs,
      abs_of_pos hτpos, hDeq] at hres
    have hτ2 : (0 : ℝ) < τ ^ 2 := by positivity
    have hmul : τ ^ 2 * (Bu h h - Bv h h) ≤ τ ^ 2 * (4 * ε * ‖h‖ ^ 2) := by nlinarith [hres]
    have hfin := le_of_mul_le_mul_left hmul hτ2
    have hexp : 4 * ε * ‖h‖ ^ 2 + ε = η := by rw [hεdef]; field_simp
    linarith
  -- Step 5: the matrix comparison
  refine ⟨hDeq, hBle, by rw [hDeq], ?_⟩
  intro ξ
  have hquad : ∀ B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      ∑ i, ∑ j, B (sig x₀ i) (sig x₀ j) * ξ j * ξ i
        = B (∑ i, ξ i • sig x₀ i) (∑ i, ξ i • sig x₀ i) := by
    intro B
    simp only [map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∀ (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      ∑ i, ∑ j, (hhessS sig x₀ D B) i j * ξ j * ξ i
        = (∑ i, ∑ j, B (sig x₀ i) (sig x₀ j) * ξ j * ξ i)
          + ∑ i, ∑ j, (Mfield sig x₀ D) i j * ξ j * ξ i := by
    intro D B
    simp only [hhessS, Matrix.add_apply, Matrix.of_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  show ∑ i, ∑ j, (hhessS sig x₀ Du Bu) i j * ξ j * ξ i
      ≤ ∑ i, ∑ j, (hhessS sig x₀ Dv Bv) i j * ξ j * ξ i
  rw [hsplit Du Bu, hsplit Dv Bv, hquad Bu, hquad Bv, hDeq]
  linarith [hBle (∑ i, ξ i • sig x₀ i)]
