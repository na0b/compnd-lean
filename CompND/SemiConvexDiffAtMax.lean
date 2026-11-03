import CompND.LocallySemiConvexOn
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-- subsec:semi(1): at a local maximum of `u - v` with `u` locally semi-convex and `v`
locally semi-concave, both functions are differentiable and their derivatives agree; and
likewise at every point of `argmax_Ω (u - v)`. -/
theorem SemiConvexDiffAtMax {N : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin N)))
    (u v : EuclideanSpace ℝ (Fin N) → ℝ)
    (hu : LocallySemiConvexOn Ω u) (hv : LocallySemiConvexOn Ω (fun y => -v y)) :
    (∀ x₀ ∈ Ω, IsLocalMax (fun y => u y - v y) x₀ →
      ∃ D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ, HasFDerivAt u D x₀ ∧ HasFDerivAt v D x₀) ∧
    (∀ x₀ ∈ Ω, IsMaxOn (fun y => u y - v y) Ω x₀ →
      ∃ D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ, HasFDerivAt u D x₀ ∧ HasFDerivAt v D x₀) := by
  -- A quadratic two-sided bound at a point gives Fréchet differentiability there.
  have quadDeriv : ∀ (f : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N))
      (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) (r K : ℝ), 0 < r → 0 ≤ K →
      (∀ y ∈ Metric.ball z r, |f y - f z - D (y - z)| ≤ K * ‖y - z‖ ^ 2) →
      HasFDerivAt f D z := by
    intro f z D r K hr hK hbd
    rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hd : (0:ℝ) < K + 1 := by linarith
    have hr' : 0 < min r (c / (K + 1)) := lt_min hr (by positivity)
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds z hr') ?_
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hy1 : y ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : ‖y - z‖ ≤ c / (K + 1) := le_of_lt (lt_of_lt_of_le hy (min_le_right _ _))
    have h0 : (0:ℝ) ≤ ‖y - z‖ := norm_nonneg _
    have hX : (0:ℝ) ≤ c / (K + 1) := div_nonneg hc.le hd.le
    have hXe : c / (K + 1) * (K + 1) = c := by field_simp
    have hKb : K * ‖y - z‖ ≤ c := by
      have hstep : K * ‖y - z‖ ≤ K * (c / (K + 1)) := mul_le_mul_of_nonneg_left hy2 hK
      nlinarith [hX, hXe, hstep]
    simp only [Real.norm_eq_abs]
    calc |f y - f z - D (y - z)| ≤ K * ‖y - z‖ ^ 2 := hbd y hy1
      _ = (K * ‖y - z‖) * ‖y - z‖ := by ring
      _ ≤ c * ‖y - z‖ := mul_le_mul_of_nonneg_right hKb h0
  -- Adding an affine function preserves convexity on a set.
  have haddaff : ∀ (s : Set (EuclideanSpace ℝ (Fin N))) (F : EuclideanSpace ℝ (Fin N) → ℝ),
      ConvexOn ℝ s F → ∀ (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) (b : ℝ),
      ConvexOn ℝ s (fun y => F y + (L y + b)) := by
    intro s F hF L b
    refine ⟨hF.1, fun p hp q hq a c ha hc hac => ?_⟩
    have h1 := hF.2 hp hq ha hc hac
    have hb : a * b + c * b = b := by rw [← add_mul, hac, one_mul]
    have hL : L (a • p + c • q) = a * L p + c * L q := by
      rw [map_add, map_smul, map_smul]; simp
    simp only [smul_eq_mul] at h1 ⊢
    rw [hL]
    linarith [h1, hb]
  -- The one gap in the `.tex` proof: a convex function on an open ball has a subgradient
  -- at the centre.  Built from the geometric Hahn-Banach theorem applied to the open
  -- epigraph.
  have subgrad : ∀ (g : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N)) (r : ℝ),
      0 < r → ConvexOn ℝ (Metric.ball z r) g →
      ∃ q : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
        ∀ y ∈ Metric.ball z r, g z + q (y - z) ≤ g y := by
    intro g z r hr hconv
    have hgc : ContinuousOn g (Metric.ball z r) := hconv.continuousOn Metric.isOpen_ball
    have hstrict : ∀ r1 s1 r2 s2 a b : ℝ, r1 < s1 → r2 < s2 → 0 ≤ a → 0 ≤ b → a + b = 1 →
        a * r1 + b * r2 < a * s1 + b * s2 := by
      intro r1 s1 r2 s2 a b h1 h2 ha hb hab
      rcases ha.lt_or_eq with ha' | ha'
      · have e1 := mul_lt_mul_of_pos_left h1 ha'
        have e2 := mul_le_mul_of_nonneg_left h2.le hb
        linarith
      · have hb1 : b = 1 := by linarith [ha'.symm]
        rw [← ha', hb1]
        linarith
    set S : Set (EuclideanSpace ℝ (Fin N) × ℝ) :=
      {p | p.1 ∈ Metric.ball z r ∧ g p.1 < p.2} with hS
    have hSconv : Convex ℝ S := by
      intro p hp q' hq' a b ha hb hab
      rw [hS] at hp hq' ⊢
      simp only [Set.mem_ofPred_eq] at hp hq' ⊢
      have hcv := hconv.2 hp.1 hq'.1 ha hb hab
      simp only [smul_eq_mul] at hcv
      refine ⟨?_, ?_⟩
      · simpa using convex_ball z r hp.1 hq'.1 ha hb hab
      · have hlt := hstrict (g p.1) p.2 (g q'.1) q'.2 a b hp.2 hq'.2 ha hb hab
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        linarith
    have hSopen : IsOpen S := by
      rw [isOpen_iff_mem_nhds]
      intro p hp
      rw [hS] at hp
      have hpb : p.1 ∈ Metric.ball z r := hp.1
      have hcont : ContinuousAt g p.1 := hgc.continuousAt (Metric.isOpen_ball.mem_nhds hpb)
      have h1 : ContinuousAt (fun w : EuclideanSpace ℝ (Fin N) × ℝ => g w.1) p :=
        hcont.comp continuousAt_fst
      have h2 : ContinuousAt (fun w : EuclideanSpace ℝ (Fin N) × ℝ => w.2) p := continuousAt_snd
      have hA : {w : EuclideanSpace ℝ (Fin N) × ℝ | g w.1 < w.2} ∈ nhds p :=
        h1.eventually_lt h2 hp.2
      have hB : {w : EuclideanSpace ℝ (Fin N) × ℝ | w.1 ∈ Metric.ball z r} ∈ nhds p :=
        (Metric.isOpen_ball.preimage continuous_fst).mem_nhds hpb
      refine Filter.mem_of_superset (Filter.inter_mem hB hA) ?_
      intro w hw
      rw [hS]
      exact ⟨hw.1, hw.2⟩
    have hnot : ((z, g z) : EuclideanSpace ℝ (Fin N) × ℝ) ∉ S := by
      rw [hS]
      simp
    obtain ⟨F, hF⟩ := geometric_hahn_banach_open_point hSconv hSopen hnot
    set φ : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
      F.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ) with hφ
    set c : ℝ := F (0, 1) with hc
    have hFsplit : ∀ (y : EuclideanSpace ℝ (Fin N)) (t : ℝ), F (y, t) = φ y + t * c := by
      intro y t
      have h : ((y, t) : EuclideanSpace ℝ (Fin N) × ℝ) = (y, 0) + t • (0, 1) := by
        simp
      rw [h, map_add, map_smul]
      simp [hφ, hc, smul_eq_mul]
    have hc0 : c < 0 := by
      have hmem : ((z, g z + 1) : EuclideanSpace ℝ (Fin N) × ℝ) ∈ S := by
        rw [hS]
        exact ⟨Metric.mem_ball_self hr, by linarith⟩
      have hlt := hF _ hmem
      rw [hFsplit, hFsplit] at hlt
      have hexp : (g z + 1) * c = g z * c + c := by ring
      rw [hexp] at hlt
      linarith
    have hcne : c ≠ 0 := ne_of_lt hc0
    have hkey : ∀ y ∈ Metric.ball z r, φ y + g y * c ≤ φ z + g z * c := by
      intro y hy
      by_contra hcon
      push Not at hcon
      have hdpos : 0 < ((φ y + g y * c) - (φ z + g z * c)) / (-c) :=
        div_pos (by linarith) (by linarith)
      have hmem : ((y, g y + ((φ y + g y * c) - (φ z + g z * c)) / (-c)) :
          EuclideanSpace ℝ (Fin N) × ℝ) ∈ S := by
        rw [hS]
        exact ⟨hy, by linarith⟩
      have hlt := hF _ hmem
      rw [hFsplit, hFsplit] at hlt
      have hcc : (g y + ((φ y + g y * c) - (φ z + g z * c)) / (-c)) * c
          = g y * c - ((φ y + g y * c) - (φ z + g z * c)) := by
        field_simp
        ring
      rw [hcc] at hlt
      linarith
    have hinv : 0 < (-c)⁻¹ := inv_pos.2 (by linarith)
    refine ⟨(-c)⁻¹ • φ, ?_⟩
    intro y hy
    have h6 := hkey y hy
    have hφs : (((-c)⁻¹ • φ) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) (y - z)
        = (-c)⁻¹ * (φ y - φ z) := by
      simp [map_sub]
      ring
    rw [hφs]
    have h7 : φ y - φ z ≤ (g z - g y) * c := by
      have hre : (g z - g y) * c = g z * c - g y * c := by ring
      rw [hre]; linarith
    have h8 := mul_le_mul_of_nonneg_left h7 hinv.le
    have h9 : (-c)⁻¹ * ((g z - g y) * c) = g y - g z := by field_simp; ring
    rw [h9] at h8
    linarith
  -- The quadratic minorant of `.tex` Step 1, with the reparametrised quadratic term.
  have minorant : ∀ (f : EuclideanSpace ℝ (Fin N) → ℝ), LocallySemiConvexOn Ω f →
      ∀ z ∈ Ω, ∃ ρ > 0, ∃ Λ : ℝ, 0 ≤ Λ ∧ Metric.ball z ρ ⊆ Ω ∧
        ∃ D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
          ∀ y ∈ Metric.ball z ρ, f z + D (y - z) - Λ / 2 * ‖y - z‖ ^ 2 ≤ f y := by
    intro f hf z hz
    obtain ⟨ρ, hρ, Λ, hΛ, hball, hconv⟩ := hf z hz
    have hid : ∀ y : EuclideanSpace ℝ (Fin N),
        f y + Λ / 2 * ‖y - z‖ ^ 2
          = (f y + Λ / 2 * ‖y‖ ^ 2) + (((-(Λ • innerSL ℝ z)) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) y
              + Λ / 2 * ‖z‖ ^ 2) := by
      intro y
      have h := norm_sub_sq_real y z
      simp only [neg_apply, smul_apply,
        innerSL_apply_apply, smul_eq_mul]
      rw [h, real_inner_comm z y]
      ring
    have hconv2 : ConvexOn ℝ (Metric.ball z ρ) (fun y => f y + Λ / 2 * ‖y - z‖ ^ 2) := by
      have heq : (fun y => f y + Λ / 2 * ‖y - z‖ ^ 2)
          = (fun y => (f y + Λ / 2 * ‖y‖ ^ 2)
              + (((-(Λ • innerSL ℝ z)) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) y
                  + Λ / 2 * ‖z‖ ^ 2)) := funext hid
      rw [heq]
      exact haddaff _ _ hconv _ _
    obtain ⟨q, hq⟩ := subgrad _ z ρ hρ hconv2
    refine ⟨ρ, hρ, Λ, hΛ, hball, q, ?_⟩
    intro y hy
    have hqy := hq y hy
    have hzz : ‖z - z‖ ^ 2 = (0:ℝ) := by simp
    rw [hzz] at hqy
    linarith
  -- Part (1): the local-maximum case.
  have part1 : ∀ x₀ ∈ Ω, IsLocalMax (fun y => u y - v y) x₀ →
      ∃ D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ, HasFDerivAt u D x₀ ∧ HasFDerivAt v D x₀ := by
    intro x₀ hx₀ hmax
    obtain ⟨ρ₁, hρ₁, Λ₁, hΛ₁, hb₁, D₁, h1⟩ := minorant u hu x₀ hx₀
    obtain ⟨ρ₂, hρ₂, Λ₂, hΛ₂, hb₂, D₂, h2⟩ := minorant (fun y => -v y) hv x₀ hx₀
    have hmax' : ∀ᶠ y in nhds x₀, u y - v y ≤ u x₀ - v x₀ := hmax
    obtain ⟨ρ₃, hρ₃, h3⟩ := Metric.eventually_nhds_iff_ball.1 hmax'
    set ρ : ℝ := min ρ₁ (min ρ₂ ρ₃) with hρdef
    have hρ : 0 < ρ := lt_min hρ₁ (lt_min hρ₂ hρ₃)
    have hsub1 : Metric.ball x₀ ρ ⊆ Metric.ball x₀ ρ₁ :=
      Metric.ball_subset_ball (min_le_left _ _)
    have hsub2 : Metric.ball x₀ ρ ⊆ Metric.ball x₀ ρ₂ :=
      Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _))
    have hsub3 : Metric.ball x₀ ρ ⊆ Metric.ball x₀ ρ₃ :=
      Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))
    have h2' : ∀ y ∈ Metric.ball x₀ ρ₂,
        -v x₀ + D₂ (y - x₀) - Λ₂ / 2 * ‖y - x₀‖ ^ 2 ≤ -v y := h2
    -- (4): the two subgradients are opposite up to a quadratic error.
    have h4 : ∀ y ∈ Metric.ball x₀ ρ,
        (D₁ + D₂) (y - x₀) ≤ (Λ₁ + Λ₂) / 2 * ‖y - x₀‖ ^ 2 := by
      intro y hy
      have a1 := h1 y (hsub1 hy)
      have a2 := h2' y (hsub2 hy)
      have a3 := h3 y (hsub3 hy)
      simp only [add_apply]
      linarith
    -- Hence `D₁ + D₂ = 0`, by uniqueness of the Fréchet derivative of the zero function.
    have h5 : ∀ y ∈ Metric.ball x₀ ρ,
        |(fun _ : EuclideanSpace ℝ (Fin N) => (0:ℝ)) y
            - (fun _ : EuclideanSpace ℝ (Fin N) => (0:ℝ)) x₀ - (D₁ + D₂) (y - x₀)|
          ≤ (Λ₁ + Λ₂) / 2 * ‖y - x₀‖ ^ 2 := by
      intro y hy
      have hy2 : x₀ - (y - x₀) ∈ Metric.ball x₀ ρ := by
        rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
        have hre : x₀ - (y - x₀) - x₀ = -(y - x₀) := by abel
        rw [hre, norm_neg]
        exact hy
      have b1 := h4 y hy
      have b2 := h4 _ hy2
      have hre : x₀ - (y - x₀) - x₀ = -(y - x₀) := by abel
      rw [hre] at b2
      simp only [map_neg, norm_neg] at b2
      simp only
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hD0 : D₁ + D₂ = 0 := by
      have hdz := quadDeriv (fun _ => (0:ℝ)) x₀ (D₁ + D₂) ρ ((Λ₁ + Λ₂) / 2) hρ (by linarith) h5
      exact hdz.unique (hasFDerivAt_const (0:ℝ) x₀)
    have hDz : ∀ w : EuclideanSpace ℝ (Fin N), D₁ w + D₂ w = 0 := by
      intro w
      have hw : (D₁ + D₂) w = (0 : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) w := by rw [hD0]
      simpa using hw
    refine ⟨D₁, ?_, ?_⟩
    · refine quadDeriv u x₀ D₁ ρ ((Λ₁ + Λ₂) / 2) hρ (by linarith) ?_
      intro y hy
      have a1 := h1 y (hsub1 hy)
      have a2 := h2' y (hsub2 hy)
      have a3 := h3 y (hsub3 hy)
      have a4 := hDz (y - x₀)
      have hq1 : 0 ≤ Λ₁ * ‖y - x₀‖ ^ 2 := by positivity
      have hq2 : 0 ≤ Λ₂ * ‖y - x₀‖ ^ 2 := by positivity
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    · refine quadDeriv v x₀ D₁ ρ ((Λ₁ + Λ₂) / 2) hρ (by linarith) ?_
      intro y hy
      have a1 := h1 y (hsub1 hy)
      have a2 := h2' y (hsub2 hy)
      have a3 := h3 y (hsub3 hy)
      have a4 := hDz (y - x₀)
      have hq1 : 0 ≤ Λ₁ * ‖y - x₀‖ ^ 2 := by positivity
      have hq2 : 0 ≤ Λ₂ * ‖y - x₀‖ ^ 2 := by positivity
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
  refine ⟨part1, ?_⟩
  -- Part (2): the argmax case reduces to part (1), since `Ω` contains a ball around `x₀`.
  intro x₀ hx₀ hmax
  obtain ⟨ρ₀, hρ₀, Λ₀, hΛ₀, hb₀, hc₀⟩ := hu x₀ hx₀
  refine part1 x₀ hx₀ ?_
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ hρ₀) ?_
  intro y hy
  exact hmax (hb₀ hy)
