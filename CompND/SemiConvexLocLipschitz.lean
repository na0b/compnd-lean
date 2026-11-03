import CompND.LocallySemiConvexOn
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Order.Compact

/-- subsec:semi(3): a locally semi-convex function is continuous, locally Lipschitz,
Lipschitz on every compact subset, and has bounded derivative on compact subsets wherever
the derivative exists. -/
theorem SemiConvexLocLipschitz {N : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin N)))
    (w : EuclideanSpace ℝ (Fin N) → ℝ) (hw : LocallySemiConvexOn Ω w) :
    ContinuousOn w Ω ∧
    (∀ x ∈ Ω, ∃ r > 0, ∃ C : ℝ, 0 ≤ C ∧ Metric.ball x r ⊆ Ω ∧
      ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r, |w y - w z| ≤ C * ‖y - z‖) ∧
    (∀ K : Set (EuclideanSpace ℝ (Fin N)), K ⊆ Ω → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ z ∈ K, |w y - w z| ≤ C * ‖y - z‖) ∧
    (∀ K : Set (EuclideanSpace ℝ (Fin N)), K ⊆ Ω → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
        HasFDerivAt w D x → ‖D‖ ≤ C) := by
  -- Step 0: `Ω` is open, since every point of `Ω` carries a ball inside `Ω`.
  have hΩopen : IsOpen Ω := by
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨ρ, hρ, Λ, _, hball, _⟩ := hw x hx
    exact ⟨ρ, hρ, hball⟩
  -- Step 1: the local Lipschitz estimate, i.e. part (2).
  have key : ∀ x ∈ Ω, ∃ r > 0, ∃ C : ℝ, 0 ≤ C ∧ Metric.ball x r ⊆ Ω ∧
      ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r, |w y - w z| ≤ C * ‖y - z‖ := by
    intro x hx
    obtain ⟨ρ, hρ, Λ, hΛ, hball, hconv⟩ := hw x hx
    set g : EuclideanSpace ℝ (Fin N) → ℝ := fun y => w y + Λ / 2 * ‖y‖ ^ 2 with hg
    -- (1a) `g` is bounded on the compact set `closedBall x (3ρ/4) ⊆ ball x ρ`.
    have hsub : Metric.closedBall x (3 * ρ / 4) ⊆ Metric.ball x ρ := by
      intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      linarith
    have hgc : ContinuousOn g (Metric.ball x ρ) := hconv.continuousOn Metric.isOpen_ball
    have habs : ContinuousOn (fun y => |g y|) (Metric.closedBall x (3 * ρ / 4)) :=
      continuous_abs.comp_continuousOn (hgc.mono hsub)
    obtain ⟨M, hM⟩ := (isCompact_closedBall x (3 * ρ / 4)).bddAbove_image habs
    have hMle : ∀ a : EuclideanSpace ℝ (Fin N), dist a x < 3 * ρ / 4 → |g a| ≤ M := by
      intro a ha
      exact hM (Set.mem_image_of_mem _ (Metric.mem_closedBall.2 ha.le))
    -- (1b) Mathlib's chord estimate for convex functions on a ball.
    have hconv' : ConvexOn ℝ (Metric.ball x (3 * ρ / 4)) g :=
      hconv.subset (Metric.ball_subset_ball (by linarith)) (convex_ball _ _)
    have hlipg := hconv'.lipschitzOnWith_of_abs_le (ε := ρ / 4) (by linarith) hMle
    set Cg : ℝ := ((2 * M / (ρ / 4)).toNNReal : ℝ) with hCg
    have hCg0 : 0 ≤ Cg := (2 * M / (ρ / 4)).toNNReal.coe_nonneg
    have hball2 : Metric.ball x (ρ / 2) ⊆ Metric.ball x (3 * ρ / 4 - ρ / 4) :=
      Metric.ball_subset_ball (by linarith)
    have hgest : ∀ y ∈ Metric.ball x (ρ / 2), ∀ z ∈ Metric.ball x (ρ / 2),
        |g y - g z| ≤ Cg * ‖y - z‖ := by
      intro y hy z hz
      have := hlipg.dist_le_mul y (hball2 hy) z (hball2 hz)
      rwa [Real.dist_eq, dist_eq_norm] at this
    -- (1c) subtract the quadratic term.
    set R : ℝ := ‖x‖ + ρ / 2 with hR
    have hR0 : 0 ≤ R := by positivity
    have hnormle : ∀ y ∈ Metric.ball x (ρ / 2), ‖y‖ ≤ R := by
      intro y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      calc ‖y‖ = ‖y - x + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    have hquad : ∀ y ∈ Metric.ball x (ρ / 2), ∀ z ∈ Metric.ball x (ρ / 2),
        |‖y‖ ^ 2 - ‖z‖ ^ 2| ≤ 2 * R * ‖y - z‖ := by
      intro y hy z hz
      have h1 : |‖y‖ - ‖z‖| ≤ ‖y - z‖ := abs_norm_sub_norm_le y z
      have h2 : |‖y‖ + ‖z‖| ≤ 2 * R := by
        rw [abs_of_nonneg (by positivity)]
        linarith [hnormle y hy, hnormle z hz]
      have hfac : ‖y‖ ^ 2 - ‖z‖ ^ 2 = (‖y‖ - ‖z‖) * (‖y‖ + ‖z‖) := by ring
      rw [hfac, abs_mul]
      calc |‖y‖ - ‖z‖| * |‖y‖ + ‖z‖| ≤ ‖y - z‖ * (2 * R) :=
            mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
        _ = 2 * R * ‖y - z‖ := by ring
    refine ⟨ρ / 2, by linarith, Cg + Λ * R, by positivity,
      (Metric.ball_subset_ball (by linarith)).trans hball, ?_⟩
    intro y hy z hz
    have hwg : w y - w z = (g y - g z) - Λ / 2 * (‖y‖ ^ 2 - ‖z‖ ^ 2) := by
      simp only [hg]; ring
    calc |w y - w z| = |(g y - g z) - Λ / 2 * (‖y‖ ^ 2 - ‖z‖ ^ 2)| := by rw [hwg]
      _ ≤ |g y - g z| + |Λ / 2 * (‖y‖ ^ 2 - ‖z‖ ^ 2)| := abs_sub _ _
      _ = |g y - g z| + Λ / 2 * |‖y‖ ^ 2 - ‖z‖ ^ 2| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Λ / 2)]
      _ ≤ Cg * ‖y - z‖ + Λ / 2 * (2 * R * ‖y - z‖) := by
            have := hgest y hy z hz
            have h2 := hquad y hy z hz
            have : Λ / 2 * |‖y‖ ^ 2 - ‖z‖ ^ 2| ≤ Λ / 2 * (2 * R * ‖y - z‖) := by
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
            linarith [hgest y hy z hz]
      _ = (Cg + Λ * R) * ‖y - z‖ := by ring
  -- The `LipschitzOnWith` form of the local estimate.
  have keyLip : ∀ x ∈ Ω, ∃ r > 0, ∃ C : NNReal, Metric.ball x r ⊆ Ω ∧
      LipschitzOnWith C w (Metric.ball x r) := by
    intro x hx
    obtain ⟨r, hr, C, hC, hsub, hest⟩ := key x hx
    refine ⟨r, hr, C.toNNReal, hsub, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro y hy z hz
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC]
    exact hest y hy z hz
  -- Local Lipschitz continuity on any subset of `Ω`.
  have hlocOn : ∀ S : Set (EuclideanSpace ℝ (Fin N)), S ⊆ Ω → LocallyLipschitzOn S w := by
    intro S hS x hx
    obtain ⟨r, hr, C, _, hlip⟩ := keyLip x (hS hx)
    exact ⟨C, Metric.ball x r,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hr), hlip⟩
  -- Step 3: Lipschitz on compact subsets.
  have part3 : ∀ K : Set (EuclideanSpace ℝ (Fin N)), K ⊆ Ω → IsCompact K →
      ∃ C : NNReal, LipschitzOnWith C w K := by
    intro K hKΩ hKc
    exact (hlocOn K hKΩ).exists_lipschitzOnWith_of_compact hKc
  refine ⟨(hlocOn Ω (subset_refl Ω)).continuousOn, key, ?_, ?_⟩
  · intro K hKΩ hKc
    obtain ⟨C, hC⟩ := part3 K hKΩ hKc
    refine ⟨(C : ℝ), C.coe_nonneg, ?_⟩
    intro y hy z hz
    have := hC.dist_le_mul y hy z hz
    rwa [Real.dist_eq, dist_eq_norm] at this
  · intro K hKΩ hKc
    obtain ⟨L, hLc, hKL, hLΩ⟩ := exists_compact_between hKc hΩopen hKΩ
    obtain ⟨C, hC⟩ := part3 L hLΩ hLc
    refine ⟨(C : ℝ), C.coe_nonneg, ?_⟩
    intro x hx D hD
    exact hD.le_of_lipschitzOn (mem_interior_iff_mem_nhds.1 (hKL hx)) hC
