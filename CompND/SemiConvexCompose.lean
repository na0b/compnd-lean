import CompND.SemiConvexLocLipschitz
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.Compact

/-- subsec:semi(4): local semi-convexity is preserved by composing with a convex
nondecreasing `C²` outer function and by precomposing with a `C²` map. -/
theorem SemiConvexCompose {N : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin N)))
    (w : EuclideanSpace ℝ (Fin N) → ℝ) (hw : LocallySemiConvexOn Ω w) :
    (∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → (∀ s, 1 ≤ deriv ψ s) → (∀ s, 0 ≤ deriv (deriv ψ) s) →
      LocallySemiConvexOn Ω (fun y => ψ (w y))) ∧
    (∀ Θ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N), ContDiff ℝ 2 Θ →
      LocallySemiConvexOn (Θ ⁻¹' Ω) (fun y => w (Θ y))) := by
  -- Step 0: the parallelogram identity.
  have step0 : ∀ (x y : EuclideanSpace ℝ (Fin N)) (t : ℝ),
      ‖t • x + (1 - t) • y‖ ^ 2
        = t * ‖x‖ ^ 2 + (1 - t) * ‖y‖ ^ 2 - t * (1 - t) * ‖x - y‖ ^ 2 := by
    intro x y t
    have e1 := norm_add_sq_real (t • x) ((1 - t) • y)
    rw [real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs] at e1
    have ha : (|t| * ‖x‖) ^ 2 = t ^ 2 * ‖x‖ ^ 2 := by rw [mul_pow, sq_abs]
    have hb : (|1 - t| * ‖y‖) ^ 2 = (1 - t) ^ 2 * ‖y‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [e1, ha, hb, norm_sub_sq_real x y]
    ring
  -- Step 1, (V) ⇒ (C): the chord form follows from convexity of the shifted function.
  have step1V2C : ∀ (S : Set (EuclideanSpace ℝ (Fin N))) (f : EuclideanSpace ℝ (Fin N) → ℝ)
      (L : ℝ), ConvexOn ℝ S (fun y => f y + L / 2 * ‖y‖ ^ 2) →
      ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        f (t • x + (1 - t) • y)
          ≤ t * f x + (1 - t) * f y + L / 2 * (t * (1 - t)) * ‖x - y‖ ^ 2 := by
    intro S f L hV x hx y hy t ht0 ht1
    have h := hV.2 hx hy ht0 (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
    simp only [smul_eq_mul] at h
    rw [step0 x y t] at h
    linarith
  -- Step 1, (C) ⇒ (V): on a convex set the chord form gives convexity of the shift.
  have step1C2V : ∀ (S : Set (EuclideanSpace ℝ (Fin N))) (f : EuclideanSpace ℝ (Fin N) → ℝ)
      (L : ℝ), Convex ℝ S →
      (∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        f (t • x + (1 - t) • y)
          ≤ t * f x + (1 - t) * f y + L / 2 * (t * (1 - t)) * ‖x - y‖ ^ 2) →
      ConvexOn ℝ S (fun y => f y + L / 2 * ‖y‖ ^ 2) := by
    intro S f L hS hC
    refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have h := hC x hx y hy a ha (by linarith)
    simp only [smul_eq_mul]
    rw [step0 x y a]
    linarith
  refine ⟨?_, ?_⟩
  · -- Step 2: the outer composition `ψ ∘ w`.
    intro ψ hψ hψ1 hψ2 x₀ hx₀
    obtain ⟨ρ, hρ, Λ, hΛ, hball, hconv⟩ := hw x₀ hx₀
    have hrpos : (0:ℝ) < ρ / 2 := by linarith
    have hballr : Metric.ball x₀ (ρ / 2) ⊆ Metric.ball x₀ ρ :=
      Metric.ball_subset_ball (by linarith)
    have hclosed : Metric.closedBall x₀ (ρ / 2) ⊆ Metric.ball x₀ ρ := by
      intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      linarith
    -- (2): the chord form for `w` on the smaller ball
    have h2 := step1V2C (Metric.ball x₀ (ρ / 2)) w Λ
      (hconv.subset hballr (convex_ball _ _))
    -- (2a): a compact interval containing all the relevant values
    have hcont : ContinuousOn w Ω := (SemiConvexLocLipschitz Ω w hw).1
    have hcontr : ContinuousOn w (Metric.closedBall x₀ (ρ / 2)) :=
      hcont.mono (hclosed.trans hball)
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall x₀ (ρ / 2)).bddAbove_image
      (continuous_abs.comp_continuousOn hcontr)
    set M : ℝ := max M₀ 0 with hMdef
    have hMb : ∀ y ∈ Metric.closedBall x₀ (ρ / 2), |w y| ≤ M := fun y hy =>
      (hM₀ (Set.mem_image_of_mem _ hy)).trans (le_max_left _ _)
    set lo : ℝ := -M - 1 with hlodef
    set hi : ℝ := M + Λ * (ρ / 2) ^ 2 / 2 + 1 with hhidef
    -- (2b): the local Lipschitz constant of `ψ` on that interval
    have hψc : Continuous (deriv ψ) := hψ.continuous_deriv (by norm_num)
    obtain ⟨L₀, hL₀⟩ := (isCompact_Icc (a := lo) (b := hi)).bddAbove_image
      ((continuous_abs.comp hψc).continuousOn)
    set Lψ : ℝ := max L₀ 1 with hLψdef
    have hLψ1 : (1:ℝ) ≤ Lψ := le_max_right _ _
    have hLψb : ∀ s ∈ Set.Icc lo hi, |deriv ψ s| ≤ Lψ := fun s hs =>
      (hL₀ (Set.mem_image_of_mem _ hs)).trans (le_max_left _ _)
    have hdiff : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
    have hmono : Monotone ψ :=
      (strictMono_of_deriv_pos fun s => lt_of_lt_of_le one_pos (hψ1 s)).monotone
    have hcvx : ConvexOn ℝ Set.univ ψ :=
      convexOn_univ_of_deriv2_nonneg hdiff hψ.differentiable_deriv_two (fun s => by
        simpa [Function.iterate_succ, Function.iterate_one] using hψ2 s)
    -- (3): the one-sided Lipschitz bound of `ψ` on the interval
    have h3 : ∀ s₁ s₂ : ℝ, s₁ ∈ Set.Icc lo hi → s₂ ∈ Set.Icc lo hi → s₁ ≤ s₂ →
        ψ s₂ - ψ s₁ ≤ Lψ * (s₂ - s₁) := by
      intro s₁ s₂ h₁ h₂ h12
      have hsub : Set.Icc s₁ s₂ ⊆ Set.Icc lo hi := Set.Icc_subset_Icc h₁.1 h₂.2
      have hd : ∀ x ∈ Set.Icc s₁ s₂, HasDerivWithinAt ψ (deriv ψ x) (Set.Icc s₁ s₂) x :=
        fun x _ => (hdiff x).hasDerivAt.hasDerivWithinAt
      have hbnd : ∀ x ∈ Set.Ico s₁ s₂, ‖deriv ψ x‖ ≤ Lψ := fun x hx => by
        rw [Real.norm_eq_abs]
        exact hLψb x (hsub (Set.Ico_subset_Icc_self hx))
      have hres := norm_image_sub_le_of_norm_deriv_le_segment' hd hbnd s₂
        (Set.right_mem_Icc.2 h12)
      rw [Real.norm_eq_abs] at hres
      have := abs_le.1 hres
      linarith [this.2]
    -- (2c): the chord inequality for `ψ ∘ w`
    have hC : ∀ y ∈ Metric.ball x₀ (ρ / 2), ∀ z ∈ Metric.ball x₀ (ρ / 2), ∀ t : ℝ,
        0 ≤ t → t ≤ 1 →
        ψ (w (t • y + (1 - t) • z))
          ≤ t * ψ (w y) + (1 - t) * ψ (w z)
            + Lψ * Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2 := by
      intro y hy z hz t ht0 ht1
      have hyc : y ∈ Metric.closedBall x₀ (ρ / 2) := Metric.ball_subset_closedBall hy
      have hzc : z ∈ Metric.closedBall x₀ (ρ / 2) := Metric.ball_subset_closedBall hz
      have hmid : t • y + (1 - t) • z ∈ Metric.ball x₀ (ρ / 2) :=
        convex_ball x₀ (ρ / 2) hy hz ht0 (by linarith) (by ring)
      have hmidc : t • y + (1 - t) • z ∈ Metric.closedBall x₀ (ρ / 2) :=
        Metric.ball_subset_closedBall hmid
      -- the quantities `a` and `h` of the `.tex`
      have hyM := abs_le.1 (hMb y hyc)
      have hzM := abs_le.1 (hMb z hzc)
      have hmM := abs_le.1 (hMb _ hmidc)
      have htt4 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
      have hnn : (0:ℝ) ≤ ‖y - z‖ := norm_nonneg _
      have hyz : ‖y - z‖ ≤ 2 * (ρ / 2) := by
        have h1 : dist y z ≤ dist y x₀ + dist x₀ z := dist_triangle _ _ _
        rw [Metric.mem_ball] at hy hz
        rw [dist_comm x₀ z] at h1
        rw [← dist_eq_norm]
        linarith
      have hhb : Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2 ≤ Λ * (ρ / 2) ^ 2 / 2 := by
        have hsq : ‖y - z‖ ^ 2 ≤ 4 * (ρ / 2) ^ 2 := by
          linarith only [mul_self_le_mul_self hnn hyz]
        have s1 : Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2 ≤ Λ / 2 * (1 / 4) * ‖y - z‖ ^ 2 := by
          have hcc : (0:ℝ) ≤ Λ / 2 * ‖y - z‖ ^ 2 := by positivity
          linarith only [mul_le_mul_of_nonneg_right htt4 hcc]
        have s2 : Λ / 2 * (1 / 4) * ‖y - z‖ ^ 2 ≤ Λ / 2 * (1 / 4) * (4 * (ρ / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        linarith only [s1, s2]
      have hhnn : (0:ℝ) ≤ Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2 := by positivity
      -- memberships in the interval `I`
      have hmemA : t * w y + (1 - t) * w z ∈ Set.Icc lo hi := by
        rw [hlodef, hhidef]
        constructor
        · nlinarith [hyM.1, hzM.1, ht0, ht1]
        · nlinarith [hyM.2, hzM.2, ht0, ht1]
      have hmemAh : t * w y + (1 - t) * w z + Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2
          ∈ Set.Icc lo hi := by
        rw [hlodef, hhidef]
        constructor
        · nlinarith [hyM.1, hzM.1, ht0, ht1, hhnn]
        · nlinarith [hyM.2, hzM.2, ht0, ht1, hhb]
      -- the three displayed inequalities
      have e1 : ψ (w (t • y + (1 - t) • z))
          ≤ ψ (t * w y + (1 - t) * w z + Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2) :=
        hmono (h2 y hy z hz t ht0 ht1)
      have e2 : ψ (t * w y + (1 - t) * w z + Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2)
          - ψ (t * w y + (1 - t) * w z)
          ≤ Lψ * (Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2) := by
        have := h3 (t * w y + (1 - t) * w z)
          (t * w y + (1 - t) * w z + Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2)
          hmemA hmemAh (by linarith)
        linarith
      have e3 : ψ (t * w y + (1 - t) * w z) ≤ t * ψ (w y) + (1 - t) * ψ (w z) := by
        have := hcvx.2 (Set.mem_univ (w y)) (Set.mem_univ (w z)) ht0
          (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
        simpa only [smul_eq_mul] using this
      have hfin : Lψ * (Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2)
          = Lψ * Λ / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2 := by ring
      rw [hfin] at e2
      linarith
    refine ⟨ρ / 2, hrpos, Lψ * Λ, mul_nonneg (by linarith) hΛ, hballr.trans hball, ?_⟩
    exact step1C2V (Metric.ball x₀ (ρ / 2)) (fun y => ψ (w y)) (Lψ * Λ)
      (convex_ball _ _) hC
  · -- Steps 3 and 4: the inner composition `w ∘ Θ`.
    intro Θ hΘ y₀ hy₀
    have hx₀ : Θ y₀ ∈ Ω := hy₀
    obtain ⟨ρ, hρ, Λ, hΛ, hballρ, hconv⟩ := hw (Θ y₀) hx₀
    obtain ⟨r₀, hr₀, C₀, hC₀, hballr₀, hlip⟩ :=
      (SemiConvexLocLipschitz Ω w hw).2.1 (Θ y₀) hx₀
    have hρ' : (0:ℝ) < min ρ r₀ := lt_min hρ hr₀
    have hball' : Metric.ball (Θ y₀) (min ρ r₀) ⊆ Ω :=
      (Metric.ball_subset_ball (min_le_left _ _)).trans hballρ
    -- (6): the chord form for `w` on the smaller ball
    have h6 := step1V2C (Metric.ball (Θ y₀) (min ρ r₀)) w Λ
      (hconv.subset (Metric.ball_subset_ball (min_le_left _ _)) (convex_ball _ _))
    have hlip' : ∀ P ∈ Metric.ball (Θ y₀) (min ρ r₀), ∀ Q ∈ Metric.ball (Θ y₀) (min ρ r₀),
        |w P - w Q| ≤ C₀ * ‖P - Q‖ := fun P hP Q hQ =>
      hlip P (Metric.ball_subset_ball (min_le_right _ _) hP) Q
        (Metric.ball_subset_ball (min_le_right _ _) hQ)
    -- Step 3: the first and second derivative bounds of `Θ` on a compact convex `K`.
    have hΘd : Differentiable ℝ Θ := hΘ.differentiable (by norm_num)
    have hG1 : ContDiff ℝ 1 (fderiv ℝ Θ) := hΘ.fderiv_right (by norm_num)
    have hKcpt : IsCompact (Metric.closedBall y₀ 1) := isCompact_closedBall _ _
    have hKcvx : Convex ℝ (Metric.closedBall y₀ 1) := convex_closedBall _ _
    obtain ⟨k₁, hk₁⟩ := ContDiffOn.exists_lipschitzOnWith
      (hΘ.contDiffOn : ContDiffOn ℝ 2 Θ (Metric.closedBall y₀ 1)) (by norm_num) hKcvx hKcpt
    obtain ⟨k₂, hk₂⟩ := ContDiffOn.exists_lipschitzOnWith
      (hG1.contDiffOn : ContDiffOn ℝ 1 (fderiv ℝ Θ) (Metric.closedBall y₀ 1))
      (by norm_num) hKcvx hKcpt
    set C₁ : ℝ := (k₁ : ℝ) with hC₁def
    set C₂ : ℝ := (k₂ : ℝ) with hC₂def
    have hC₂nn : (0:ℝ) ≤ C₂ := k₂.coe_nonneg
    -- (4): the mean value inequality for `Θ`
    have h4 : ∀ y ∈ Metric.closedBall y₀ 1, ∀ z ∈ Metric.closedBall y₀ 1,
        ‖Θ y - Θ z‖ ≤ C₁ * ‖y - z‖ := by
      intro y hy z hz
      have h := hk₁.dist_le_mul y hy z hz
      rwa [dist_eq_norm, dist_eq_norm] at h
    have hGlip : ∀ a ∈ Metric.closedBall y₀ 1, ∀ b ∈ Metric.closedBall y₀ 1,
        ‖fderiv ℝ Θ b - fderiv ℝ Θ a‖ ≤ C₂ * ‖b - a‖ := by
      intro a ha b hb
      have h := hk₂.dist_le_mul b hb a ha
      rwa [dist_eq_norm, dist_eq_norm] at h
    -- the first-order Taylor bound with Lipschitz derivative
    have htay : ∀ a ∈ Metric.closedBall y₀ 1, ∀ b ∈ Metric.closedBall y₀ 1,
        ‖Θ b - Θ a - fderiv ℝ Θ a (b - a)‖ ≤ C₂ * ‖b - a‖ * ‖b - a‖ := by
      intro a ha b hb
      have hsegK : segment ℝ a b ⊆ Metric.closedBall y₀ 1 := hKcvx.segment_subset ha hb
      have hbound : ∀ x ∈ segment ℝ a b, ‖fderiv ℝ Θ x - fderiv ℝ Θ a‖ ≤ C₂ * ‖b - a‖ := by
        intro x hx
        have h1 : ‖fderiv ℝ Θ x - fderiv ℝ Θ a‖ ≤ C₂ * ‖x - a‖ :=
          hGlip a ha x (hsegK hx)
        have h2 : ‖x - a‖ ≤ ‖b - a‖ := by
          obtain ⟨u, v, hu, hv, huv, hxe⟩ := hx
          have hxa : x - a = v • (b - a) := by
            rw [← hxe, show u = 1 - v by linarith]
            module
          rw [hxa, norm_smul, Real.norm_eq_abs, abs_of_nonneg hv]
          have hv1 : v ≤ 1 := by linarith
          nlinarith only [hv1, norm_nonneg (b - a), hv]
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hC₂nn)
      exact (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le'
        (fun x _ => hΘd x) hbound (left_mem_segment _ _ _) (right_mem_segment _ _ _)
    -- (5): the chord deficit of `Θ`
    have h5 : ∀ y ∈ Metric.closedBall y₀ 1, ∀ z ∈ Metric.closedBall y₀ 1, ∀ t : ℝ,
        0 ≤ t → t ≤ 1 →
        ‖Θ (t • y + (1 - t) • z) - (t • Θ y + (1 - t) • Θ z)‖
          ≤ C₂ * (t * (1 - t)) * ‖y - z‖ ^ 2 := by
      intro y hy z hz t ht0 ht1
      have ht1' : (0:ℝ) ≤ 1 - t := by linarith
      have hmK : t • y + (1 - t) • z ∈ Metric.closedBall y₀ 1 :=
        hKcvx hy hz ht0 ht1' (by ring)
      have e1 := htay _ hmK y hy
      have e2 := htay _ hmK z hz
      have hnym : ‖y - (t • y + (1 - t) • z)‖ = (1 - t) * ‖y - z‖ := by
        rw [show y - (t • y + (1 - t) • z) = (1 - t) • (y - z) from by module,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg ht1']
      have hnzm : ‖z - (t • y + (1 - t) • z)‖ = t * ‖y - z‖ := by
        rw [show z - (t • y + (1 - t) • z) = t • (z - y) from by module,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, norm_sub_rev]
      rw [hnym] at e1
      rw [hnzm] at e2
      -- the exact linear-combination identity
      have hGz : t • (fderiv ℝ Θ (t • y + (1 - t) • z)) (y - (t • y + (1 - t) • z))
          + (1 - t) • (fderiv ℝ Θ (t • y + (1 - t) • z)) (z - (t • y + (1 - t) • z)) = 0 := by
        rw [← map_smul, ← map_smul, ← map_add,
          show t • (y - (t • y + (1 - t) • z)) + (1 - t) • (z - (t • y + (1 - t) • z))
            = (0 : EuclideanSpace ℝ (Fin N)) from by module, map_zero]
      have hid : ‖Θ (t • y + (1 - t) • z) - (t • Θ y + (1 - t) • Θ z)‖
          = ‖t • (Θ y - Θ (t • y + (1 - t) • z)
              - (fderiv ℝ Θ (t • y + (1 - t) • z)) (y - (t • y + (1 - t) • z)))
            + (1 - t) • (Θ z - Θ (t • y + (1 - t) • z)
              - (fderiv ℝ Θ (t • y + (1 - t) • z)) (z - (t • y + (1 - t) • z)))‖ := by
        rw [show t • (Θ y - Θ (t • y + (1 - t) • z)
              - (fderiv ℝ Θ (t • y + (1 - t) • z)) (y - (t • y + (1 - t) • z)))
            + (1 - t) • (Θ z - Θ (t • y + (1 - t) • z)
              - (fderiv ℝ Θ (t • y + (1 - t) • z)) (z - (t • y + (1 - t) • z)))
            = (t • Θ y + (1 - t) • Θ z - Θ (t • y + (1 - t) • z))
              - (t • (fderiv ℝ Θ (t • y + (1 - t) • z)) (y - (t • y + (1 - t) • z))
                + (1 - t) • (fderiv ℝ Θ (t • y + (1 - t) • z))
                    (z - (t • y + (1 - t) • z))) from by module, hGz, sub_zero,
          ← norm_neg]
        congr 1
        abel
      rw [hid]
      have hsplit : ‖t • (Θ y - Θ (t • y + (1 - t) • z)
              - (fderiv ℝ Θ (t • y + (1 - t) • z)) (y - (t • y + (1 - t) • z)))
            + (1 - t) • (Θ z - Θ (t • y + (1 - t) • z)
              - (fderiv ℝ Θ (t • y + (1 - t) • z)) (z - (t • y + (1 - t) • z)))‖
          ≤ t * ‖Θ y - Θ (t • y + (1 - t) • z)
              - (fderiv ℝ Θ (t • y + (1 - t) • z)) (y - (t • y + (1 - t) • z))‖
            + (1 - t) * ‖Θ z - Θ (t • y + (1 - t) • z)
              - (fderiv ℝ Θ (t • y + (1 - t) • z)) (z - (t • y + (1 - t) • z))‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ht0, abs_of_nonneg ht1']
      refine hsplit.trans ?_
      have h1 := mul_le_mul_of_nonneg_left e1 ht0
      have h2 := mul_le_mul_of_nonneg_left e2 ht1'
      have heq : t * (C₂ * ((1 - t) * ‖y - z‖) * ((1 - t) * ‖y - z‖))
          + (1 - t) * (C₂ * (t * ‖y - z‖) * (t * ‖y - z‖))
          = C₂ * (t * (1 - t)) * ‖y - z‖ ^ 2 := by ring
      linarith only [h1, h2, heq]
    -- Step 4: assembly at `y₀`.
    obtain ⟨s₁, hs₁, hs₁b⟩ :=
      Metric.continuous_iff.1 hΘ.continuous y₀ (min ρ r₀ / 2) (by linarith)
    have hspos : (0:ℝ) < min s₁ 1 := lt_min hs₁ one_pos
    have hsK : Metric.ball y₀ (min s₁ 1) ⊆ Metric.closedBall y₀ 1 := by
      intro y hy
      rw [Metric.mem_ball] at hy
      rw [Metric.mem_closedBall]
      have : min s₁ 1 ≤ 1 := min_le_right _ _
      linarith
    have hsΘ : ∀ y ∈ Metric.ball y₀ (min s₁ 1), Θ y ∈ Metric.ball (Θ y₀) (min ρ r₀ / 2) := by
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      have : min s₁ 1 ≤ s₁ := min_le_left _ _
      exact hs₁b y (by linarith)
    have hhalf : Metric.ball (Θ y₀) (min ρ r₀ / 2) ⊆ Metric.ball (Θ y₀) (min ρ r₀) :=
      Metric.ball_subset_ball (by linarith)
    have hsub : Metric.ball y₀ (min s₁ 1) ⊆ Θ ⁻¹' Ω := fun y hy =>
      hball' (hhalf (hsΘ y hy))
    -- the chord inequality for `w ∘ Θ`
    have hCfin : ∀ y ∈ Metric.ball y₀ (min s₁ 1), ∀ z ∈ Metric.ball y₀ (min s₁ 1), ∀ t : ℝ,
        0 ≤ t → t ≤ 1 →
        w (Θ (t • y + (1 - t) • z))
          ≤ t * w (Θ y) + (1 - t) * w (Θ z)
            + (Λ * C₁ ^ 2 + 2 * (C₀ * C₂)) / 2 * (t * (1 - t)) * ‖y - z‖ ^ 2 := by
      intro y hy z hz t ht0 ht1
      have ht1' : (0:ℝ) ≤ 1 - t := by linarith
      have hmball : t • y + (1 - t) • z ∈ Metric.ball y₀ (min s₁ 1) :=
        convex_ball y₀ (min s₁ 1) hy hz ht0 ht1' (by ring)
      have hΘy := hsΘ y hy
      have hΘz := hsΘ z hz
      have hΘm := hsΘ _ hmball
      have hPt : t • Θ y + (1 - t) • Θ z ∈ Metric.ball (Θ y₀) (min ρ r₀ / 2) :=
        convex_ball (Θ y₀) (min ρ r₀ / 2) hΘy hΘz ht0 ht1' (by ring)
      -- (a) the `C₀`-Lipschitz step, fed by (5)
      have ha := (abs_le.1 (hlip' _ (hhalf hΘm) _ (hhalf hPt))).2
      have h5' := h5 y (hsK hy) z (hsK hz) t ht0 ht1
      have haa : w (Θ (t • y + (1 - t) • z)) ≤ w (t • Θ y + (1 - t) • Θ z)
          + C₀ * (C₂ * (t * (1 - t)) * ‖y - z‖ ^ 2) := by
        linarith only [ha, mul_le_mul_of_nonneg_left h5' hC₀]
      -- (b) the chord form for `w` at the images, fed by (4)
      have hb := h6 (Θ y) (hhalf hΘy) (Θ z) (hhalf hΘz) t ht0 ht1
      have hsq : ‖Θ y - Θ z‖ ^ 2 ≤ C₁ ^ 2 * ‖y - z‖ ^ 2 := by
        linarith only [mul_self_le_mul_self (norm_nonneg (Θ y - Θ z))
          (h4 y (hsK hy) z (hsK hz))]
      have hcf : (0:ℝ) ≤ Λ / 2 * (t * (1 - t)) :=
        mul_nonneg (by linarith) (mul_nonneg ht0 ht1')
      have hbb : w (t • Θ y + (1 - t) • Θ z)
          ≤ t * w (Θ y) + (1 - t) * w (Θ z)
            + Λ / 2 * (t * (1 - t)) * (C₁ ^ 2 * ‖y - z‖ ^ 2) := by
        linarith only [hb, mul_le_mul_of_nonneg_left hsq hcf]
      linarith only [haa, hbb]
    refine ⟨min s₁ 1, hspos, Λ * C₁ ^ 2 + 2 * (C₀ * C₂),
      add_nonneg (mul_nonneg hΛ (sq_nonneg C₁)) (by linarith [mul_nonneg hC₀ hC₂nn]),
      hsub, ?_⟩
    exact step1C2V (Metric.ball y₀ (min s₁ 1)) (fun y => w (Θ y))
      (Λ * C₁ ^ 2 + 2 * (C₀ * C₂)) (convex_ball _ _) hCfin
