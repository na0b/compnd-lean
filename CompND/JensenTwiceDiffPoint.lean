import CompND.EuclidCitedResults
import CompND.LocallySemiConvexOn
import CompND.TwiceDiffAt
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-- Jensen's lemma plus Aleksandrov's theorem, applied to BOTH functions: near a strict local
maximum of `u - v` there are linear perturbations `p k → 0` and points `z k → x₁` at which
`u - v + ⟪p k, ·⟫` has a local maximum and both `u` and `v` have second-order jets. -/
theorem JensenTwiceDiffPoint {N : ℕ} (hc : EuclidCitedResults)
    (Ω : Set (EuclideanSpace ℝ (Fin N)))
    (u v : EuclideanSpace ℝ (Fin N) → ℝ)
    (hu : LocallySemiConvexOn Ω u) (hv : LocallySemiConvexOn Ω (fun y => -v y))
    (x₁ : EuclideanSpace ℝ (Fin N))
    (hstrict : ∃ ν > 0, Metric.ball x₁ ν ⊆ Ω ∧
      ∀ y ∈ Metric.ball x₁ ν, y ≠ x₁ → u y - v y < u x₁ - v x₁) :
    ∃ p z : ℕ → EuclideanSpace ℝ (Fin N),
      Filter.Tendsto p Filter.atTop (nhds 0) ∧
      Filter.Tendsto z Filter.atTop (nhds x₁) ∧
      ∀ k, z k ∈ Ω ∧
        IsLocalMax (fun y => u y - v y + ∑ i, (p k) i * y i) (z k) ∧
        (∃ (Du : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
          (Bu : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
          TwiceDiffAt u (z k) Du Bu) ∧
        (∃ (Dv : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
          (Bv : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
          TwiceDiffAt v (z k) Dv Bv) := by
  obtain ⟨ν, hν, hballΩ, hstr⟩ := hstrict
  set W : Set (EuclideanSpace ℝ (Fin N)) := Metric.ball x₁ ν with hW
  have hWopen : IsOpen W := Metric.isOpen_ball
  -- Step 0: local semi-convexity restricts to the open subset `W`.
  have restrict : ∀ g : EuclideanSpace ℝ (Fin N) → ℝ, LocallySemiConvexOn Ω g →
      LocallySemiConvexOn W g := by
    intro g hg x hx
    obtain ⟨ρ₁, hρ₁, Λ, hΛ, hb₁, hcv⟩ := hg x (hballΩ hx)
    obtain ⟨ρ₂, hρ₂, hb₂⟩ := Metric.isOpen_iff.1 hWopen x hx
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, Λ, hΛ,
      (Metric.ball_subset_ball (min_le_right _ _)).trans hb₂,
      hcv.subset (Metric.ball_subset_ball (min_le_left _ _)) (convex_ball _ _)⟩
  have huW : LocallySemiConvexOn W u := restrict u hu
  have hvW : LocallySemiConvexOn W (fun y => -v y) := restrict _ hv
  -- Step 1: `u - v` is locally semi-convex on `W`.
  have hdiffW : LocallySemiConvexOn W (fun y => u y - v y) := by
    intro x hx
    obtain ⟨ρ₁, hρ₁, Λ₁, hΛ₁, hb₁, hc₁⟩ := huW x hx
    obtain ⟨ρ₂, hρ₂, Λ₂, hΛ₂, hb₂, hc₂⟩ := hvW x hx
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, Λ₁ + Λ₂, by linarith,
      (Metric.ball_subset_ball (min_le_left _ _)).trans hb₁, ?_⟩
    have e1 := hc₁.subset (Metric.ball_subset_ball (min_le_left ρ₁ ρ₂)) (convex_ball x _)
    have e2 := hc₂.subset (Metric.ball_subset_ball (min_le_right ρ₁ ρ₂)) (convex_ball x _)
    have heq : (fun y : EuclideanSpace ℝ (Fin N) => u y - v y + (Λ₁ + Λ₂) / 2 * ‖y‖ ^ 2)
        = (fun y : EuclideanSpace ℝ (Fin N) => u y + Λ₁ / 2 * ‖y‖ ^ 2)
          + (fun y : EuclideanSpace ℝ (Fin N) => -v y + Λ₂ / 2 * ‖y‖ ^ 2) := by
      funext y
      simp only [Pi.add_apply]
      ring
    rw [heq]
    exact e1.add e2
  -- Step 2: Jensen's lemma for `u - v` at `x₁`.
  obtain ⟨ρ₀, hρ₀, δ₀, hδ₀, hJ⟩ :=
    hc.jensen N (fun y => u y - v y) x₁ ⟨ν, hν, hdiffW⟩ ⟨ν, hν, hstr⟩
  -- Step 3: Aleksandrov for `u` and for `-v`, and the two null exceptional sets.
  have hau := hc.aleksandrov N W hWopen u huW
  have hav := hc.aleksandrov N W hWopen (fun y => -v y) hvW
  set Nu : Set (EuclideanSpace ℝ (Fin N)) :=
    {x | ¬ (x ∈ W → ∃ (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt u x D B)} with hNu
  set Nv : Set (EuclideanSpace ℝ (Fin N)) :=
    {x | ¬ (x ∈ W → ∃ (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt (fun y => -v y) x D B)} with hNv
  have hNu0 : MeasureTheory.volume Nu = 0 := MeasureTheory.ae_iff.1 hau
  have hNv0 : MeasureTheory.volume Nv = 0 := MeasureTheory.ae_iff.1 hav
  have hUnion : MeasureTheory.volume (Nu ∪ Nv) = 0 :=
    MeasureTheory.measure_union_null hNu0 hNv0
  -- the `-v → v` jet transfer
  have hjet : ∀ (z : EuclideanSpace ℝ (Fin N))
      (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt (fun y => -v y) z D B → TwiceDiffAt v z (-D) (-B) := by
    intro z D B h
    refine ⟨fun a b => ?_, fun ε hε => ?_⟩
    · simp only [neg_apply]
      rw [h.1 a b]
    · obtain ⟨δ, hδ, hb⟩ := h.2 ε hε
      refine ⟨δ, hδ, fun y hy => ?_⟩
      have hb' := hb y hy
      have hre : v y - v z - (-D) (y - z) - 1 / 2 * (-B) (y - z) (y - z)
          = -((-v y) - (-v z) - D (y - z) - 1 / 2 * B (y - z) (y - z)) := by
        simp only [neg_apply]
        ring
      rw [hre, abs_neg]
      exact hb'
  -- Step 4: the per-`k` construction.
  have key : ∀ k : ℕ, ∃ pk zk : EuclideanSpace ℝ (Fin N),
      ‖pk‖ ≤ 1 / (k + 1 : ℝ) ∧ dist zk x₁ ≤ 1 / (k + 1 : ℝ) ∧ zk ∈ Ω ∧
      IsLocalMax (fun y => u y - v y + ∑ i, pk i * y i) zk ∧
      (∃ (Du : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (Bu : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
        TwiceDiffAt u zk Du Bu) ∧
      (∃ (Dv : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (Bv : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
        TwiceDiffAt v zk Dv Bv) := by
    intro k
    have hk : (0:ℝ) < 1 / (k + 1 : ℝ) := by positivity
    set ρk : ℝ := 1 / 2 * min (min ρ₀ ν) (1 / (k + 1 : ℝ)) with hρkdef
    set δk : ℝ := 1 / 2 * min δ₀ (1 / (k + 1 : ℝ)) with hδkdef
    have hm1 : 0 < min (min ρ₀ ν) (1 / (k + 1 : ℝ)) := lt_min (lt_min hρ₀ hν) hk
    have hm2 : 0 < min δ₀ (1 / (k + 1 : ℝ)) := lt_min hδ₀ hk
    have hρkpos : 0 < ρk := by rw [hρkdef]; linarith
    have hδkpos : 0 < δk := by rw [hδkdef]; linarith
    have hρkρ₀ : ρk < ρ₀ := by
      have h1 : min (min ρ₀ ν) (1 / (k + 1 : ℝ)) ≤ ρ₀ :=
        (min_le_left _ _).trans (min_le_left _ _)
      rw [hρkdef]; linarith
    have hρkν : ρk < ν := by
      have h1 : min (min ρ₀ ν) (1 / (k + 1 : ℝ)) ≤ ν :=
        (min_le_left _ _).trans (min_le_right _ _)
      rw [hρkdef]; linarith
    have hρkk : ρk ≤ 1 / (k + 1 : ℝ) := by
      have h1 : min (min ρ₀ ν) (1 / (k + 1 : ℝ)) ≤ 1 / (k + 1 : ℝ) := min_le_right _ _
      rw [hρkdef]; linarith
    have hδkδ₀ : δk < δ₀ := by
      have h1 : min δ₀ (1 / (k + 1 : ℝ)) ≤ δ₀ := min_le_left _ _
      rw [hδkdef]; linarith
    have hδkk : δk ≤ 1 / (k + 1 : ℝ) := by
      have h1 : min δ₀ (1 / (k + 1 : ℝ)) ≤ 1 / (k + 1 : ℝ) := min_le_right _ _
      rw [hδkdef]; linarith
    have hpos := hJ ρk hρkpos hρkρ₀ δk hδkpos hδkδ₀
    have hsubno : ¬ ((⋃ q ∈ {q : EuclideanSpace ℝ (Fin N) | ‖q‖ < δk},
        {x ∈ Metric.ball x₁ ρk |
          IsMaxOn (fun y => u y - v y + ∑ i, q i * y i) (Metric.ball x₁ ρk) x})
        ⊆ Nu ∪ Nv) := by
      intro hsub
      exact (ne_of_gt hpos) (MeasureTheory.measure_mono_null hsub hUnion)
    obtain ⟨zk, hzkJ, hzkN⟩ := Set.not_subset.1 hsubno
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hzkJ
    obtain ⟨pk, hpk, hzkball, hzkmax⟩ := hzkJ
    have hzkW : zk ∈ W := Metric.ball_subset_ball hρkν.le hzkball
    have hzkΩ : zk ∈ Ω := hballΩ hzkW
    have hu' : ∃ (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
        TwiceDiffAt u zk D B := by
      have h : zk ∉ Nu := fun hmem => hzkN (Or.inl hmem)
      rw [hNu, Set.mem_ofPred_eq, not_not] at h
      exact h hzkW
    have hv' : ∃ (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
        TwiceDiffAt (fun y => -v y) zk D B := by
      have h : zk ∉ Nv := fun hmem => hzkN (Or.inr hmem)
      rw [hNv, Set.mem_ofPred_eq, not_not] at h
      exact h hzkW
    obtain ⟨Dv, Bv, hDv⟩ := hv'
    refine ⟨pk, zk, le_trans hpk.le hδkk, ?_, hzkΩ, ?_, hu', ⟨-Dv, -Bv, hjet zk Dv Bv hDv⟩⟩
    · rw [Metric.mem_ball] at hzkball
      linarith
    · refine Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hzkball) ?_
      intro y hy
      exact hzkmax hy
  choose p z hp hz hzΩ hlmax hju hjv using key
  refine ⟨p, z, ?_, ?_, fun k => ⟨hzΩ k, hlmax k, hju k, hjv k⟩⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) hp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg) hz
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
