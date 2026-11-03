import CompND.Ellip
import CompND.StructureConditionsES
import CompND.NormalizedAH
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Matrix

/-- eq:ell0: under (E) and the normalization eq:normal the ellipticity function is bounded
below by a positive multiple of `‖ξ‖ ^ 2`, with constant the minimum of `𝓔` over the unit
sphere. -/
theorem EllipticityLowerBound {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ)
    (hAH : StructureConditionsES m A H) (hN : NormalizedAH m A H) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ ∀ ξ : EuclideanSpace ℝ (Fin m), e₀ * ‖ξ‖ ^ 2 ≤ Ellip A ξ := by
  -- Step 1: `Ellip A` is 2-homogeneous along rays, by `NormalizedAH.A_homog`.
  have homog : ∀ (t : ℝ) (η : EuclideanSpace ℝ (Fin m)), 0 < t → η ≠ 0 →
      Ellip A (t • η) = t ^ 2 * Ellip A η := by
    intro t η ht hη
    show (∑ i, ∑ j, A (t • η) i j * (t • η) j * (t • η) i)
      = t ^ 2 * ∑ i, ∑ j, A η i j * η j * η i
    rw [hN.A_homog t η ht hη, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  -- Step 2: `Ellip A 0 = 0`.
  have hzero : Ellip A 0 = 0 := by
    show (∑ i, ∑ j, A 0 i j * (0 : EuclideanSpace ℝ (Fin m)) j * (0 : EuclideanSpace ℝ (Fin m)) i)
      = 0
    simp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- Step 3: the degenerate case `m = 0`.
    subst hm
    refine ⟨1, one_pos, fun ξ => ?_⟩
    have h1 : Ellip A ξ = 0 := by
      show (∑ i, ∑ j, A ξ i j * ξ j * ξ i) = 0
      simp
    have h2 : ‖ξ‖ = 0 := by simp [EuclideanSpace.norm_eq]
    rw [h1, h2]
    norm_num
  -- Step 4: the minimum of `Ellip A` over the unit sphere.
  set S : Set (EuclideanSpace ℝ (Fin m)) := Metric.sphere 0 1 with hSdef
  have hSmem : ∀ ω, ω ∈ S ↔ ‖ω‖ = 1 := by
    intro ω
    rw [hSdef, Metric.mem_sphere, dist_zero_right]
  have hSne : S.Nonempty := by
    refine ⟨PiLp.single 2 (⟨0, hm⟩ : Fin m) (1 : ℝ), ?_⟩
    rw [hSmem]
    simp [PiLp.norm_single]
  have hSne0 : ∀ ω ∈ S, ω ≠ 0 := by
    intro ω hω hc
    rw [hSmem] at hω
    rw [hc] at hω
    simp at hω
  have hScpt : IsCompact S := isCompact_sphere 0 1
  have hSsub : S ⊆ {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := fun ω hω => hSne0 ω hω
  have hA : ContinuousOn A S := hAH.contA.mono hSsub
  have hcont : ContinuousOn (Ellip A) S := by
    show ContinuousOn (fun ξ : EuclideanSpace ℝ (Fin m) => ∑ i, ∑ j, A ξ i j * ξ j * ξ i) S
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    have hentry : ContinuousOn (fun ξ => A ξ i j) S :=
      (continuous_apply_apply i j).comp_continuousOn hA
    have hcj : ContinuousOn (fun ξ : EuclideanSpace ℝ (Fin m) => ξ j) S :=
      (PiLp.continuous_apply 2 _ j).continuousOn
    have hci : ContinuousOn (fun ξ : EuclideanSpace ℝ (Fin m) => ξ i) S :=
      (PiLp.continuous_apply 2 _ i).continuousOn
    exact (hentry.mul hcj).mul hci
  obtain ⟨ω₀, hω₀S, hω₀min⟩ := hScpt.exists_isMinOn hSne hcont
  refine ⟨Ellip A ω₀, hAH.ellipticity ω₀ (hSne0 ω₀ hω₀S), fun ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · -- Step 5: the case `ξ = 0`.
    rw [hzero]
    simp
  · -- Step 6: the case `ξ ≠ 0`.
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    set η : EuclideanSpace ℝ (Fin m) := ‖ξ‖⁻¹ • ξ with hηdef
    have hηnorm : ‖η‖ = 1 := by
      rw [hηdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hn)]
    have hηne : η ≠ 0 := by
      intro hc
      rw [hc] at hηnorm
      simp at hηnorm
    have hηS : η ∈ S := (hSmem η).2 hηnorm
    have hxi : ‖ξ‖ • η = ξ := by
      rw [hηdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]
    have h1 : Ellip A ξ = ‖ξ‖ ^ 2 * Ellip A η := by
      have h := homog ‖ξ‖ η hn hηne
      rwa [hxi] at h
    have h2 : Ellip A ω₀ ≤ Ellip A η := hω₀min hηS
    have h3 : (0:ℝ) ≤ ‖ξ‖ ^ 2 := by positivity
    calc Ellip A ω₀ * ‖ξ‖ ^ 2 ≤ Ellip A η * ‖ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = Ellip A ξ := by rw [h1]; ring
