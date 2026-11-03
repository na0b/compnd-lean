import CompND.SemiConvexLocLipschitz
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-- subsec:semi(2): partial continuity of the gradient. If `w` is locally semi-convex or
locally semi-concave on `Ω` and is differentiable at `x` and at every point of a sequence
`xs k → x` in `Ω`, then the derivatives at `xs k` converge to the derivative at `x`. -/
theorem SemiConvexGradPartialCont {N : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin N)))
    (w : EuclideanSpace ℝ (Fin N) → ℝ)
    (hw : LocallySemiConvexOn Ω w ∨ LocallySemiConvexOn Ω (fun y => -w y))
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ Ω)
    (xs : ℕ → EuclideanSpace ℝ (Fin N)) (hxs : ∀ k, xs k ∈ Ω)
    (hlim : Filter.Tendsto xs Filter.atTop (nhds x))
    (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) (hD : HasFDerivAt w D x)
    (Ds : ℕ → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hDs : ∀ k, HasFDerivAt w (Ds k) (xs k)) :
    Filter.Tendsto Ds Filter.atTop (nhds D) := by
  -- A one-sided slope bound at `0` dominates the derivative at `0`.
  have slopeLe : ∀ (f : ℝ → ℝ) (d B δ : ℝ), 0 < δ → HasDerivAt f d 0 →
      (∀ t, 0 < t → t < δ → (f t - f 0) / t ≤ B) → d ≤ B := by
    intro f d B δ hδ hf hbd
    have hts : Filter.Tendsto (slope f 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds d) :=
      (hasDerivAt_iff_tendsto_slope_left_right.1 hf).2
    refine le_of_tendsto hts ?_
    have hmem : Set.Ioi (0:ℝ) ∩ Set.Iio δ ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      inter_mem_nhdsWithin _ (Iio_mem_nhds hδ)
    filter_upwards [hmem] with t ht
    have hsl : slope f 0 t = (f t - f 0) / t := by
      rw [slope_def_field, sub_zero]
    rw [hsl]
    exact hbd t ht.1 ht.2
  -- The derivative of a convex function at an interior point is a subgradient there.
  have subgradOf : ∀ (U : Set (EuclideanSpace ℝ (Fin N)))
      (g : EuclideanSpace ℝ (Fin N) → ℝ) (p : EuclideanSpace ℝ (Fin N))
      (l : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      ConvexOn ℝ U g → p ∈ U → HasFDerivAt g l p →
      ∀ y ∈ U, g p + l (y - p) ≤ g y := by
    intro U g p l hcv hp hl y hy
    have hc : HasDerivAt (fun t : ℝ => p + t • (y - p)) (y - p) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • (y - p)) (y - p) 0 := by
        simpa using (hasDerivAt_id (0:ℝ)).smul_const (y - p)
      simpa using h1.const_add p
    have hφ : HasDerivAt (fun t : ℝ => g (p + t • (y - p))) (l (y - p)) 0 := by
      have hcz : ((fun t : ℝ => p + t • (y - p)) (0:ℝ)) = p := by simp
      have := (hcz ▸ hl).comp_hasDerivAt (0:ℝ) hc
      exact this
    have hle := slopeLe (fun t : ℝ => g (p + t • (y - p))) (l (y - p)) (g y - g p) 1
      one_pos hφ ?_
    · linarith
    · intro t ht0 ht1
      have hco := hcv.2 hp hy (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      have hpt : (1 - t) • p + t • y = p + t • (y - p) := by
        rw [smul_sub]; abel_nf; module
      rw [hpt] at hco
      simp only [smul_eq_mul] at hco
      simp only [zero_smul, add_zero]
      rw [div_le_iff₀ ht0]
      nlinarith [hco]
  -- The derivative of the quadratic term.
  have hquad : ∀ (Λ : ℝ) (z : EuclideanSpace ℝ (Fin N)),
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin N) => Λ / 2 * ‖y‖ ^ 2)
        (Λ • innerSL ℝ z) z := by
    intro Λ z
    have h1 := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (Λ / 2)
    refine h1.congr_fderiv ?_
    ext y
    simp [two_smul]
    ring
  -- The semi-convex case.
  have main : ∀ (W : EuclideanSpace ℝ (Fin N) → ℝ), LocallySemiConvexOn Ω W →
      ∀ (p : EuclideanSpace ℝ (Fin N)), p ∈ Ω → ∀ (ps : ℕ → EuclideanSpace ℝ (Fin N)),
      Filter.Tendsto ps Filter.atTop (nhds p) →
      ∀ (E₀ : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ), HasFDerivAt W E₀ p →
      ∀ (Es : ℕ → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      (∀ k, HasFDerivAt W (Es k) (ps k)) →
      Filter.Tendsto Es Filter.atTop (nhds E₀) := by
    intro W hW p hp ps hps E₀ hE₀ Es hEs
    obtain ⟨ρ, hρ, Λ, hΛ, hbρ, hconv⟩ := hW p hp
    set g : EuclideanSpace ℝ (Fin N) → ℝ := fun y => W y + Λ / 2 * ‖y‖ ^ 2 with hgdef
    set q : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := E₀ + Λ • innerSL ℝ p with hqdef
    set qs : ℕ → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
      fun k => Es k + Λ • innerSL ℝ (ps k) with hqsdef
    have hgq : HasFDerivAt g q p := hE₀.add (hquad Λ p)
    have hgqs : ∀ k, HasFDerivAt g (qs k) (ps k) := fun k => (hEs k).add (hquad Λ (ps k))
    -- The key estimate: `qs k → q` in operator norm.
    have hmainlim : Filter.Tendsto qs Filter.atTop (nhds q) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hlo : (fun z => g z - g p - q (z - p)) =o[nhds p] (fun z => z - p) :=
        hasFDerivAt_iff_isLittleO.1 hgq
      obtain ⟨δ₀, hδ₀, hδ₀b⟩ := Metric.eventually_nhds_iff_ball.1
        (Asymptotics.isLittleO_iff.1 hlo (c := ε / 4) (by positivity))
      set δ : ℝ := min δ₀ ρ with hδdef
      have hδ : 0 < δ := lt_min hδ₀ hρ
      have hδρ : δ ≤ ρ := min_le_right _ _
      have hbd : ∀ z ∈ Metric.ball p δ, |g z - g p - q (z - p)| ≤ ε / 4 * ‖z - p‖ := by
        intro z hz
        have hz' := hδ₀b z (Metric.ball_subset_ball (min_le_left _ _) hz)
        simpa [Real.norm_eq_abs] using hz'
      rw [Metric.tendsto_atTop] at hps
      obtain ⟨n₀, hn₀⟩ := hps (δ / 8) (by positivity)
      refine ⟨n₀, fun k hk => ?_⟩
      have hpk : ‖ps k - p‖ < δ / 8 := by
        have h := hn₀ k hk
        rwa [dist_eq_norm] at h
      have hpkρ : ps k ∈ Metric.ball p ρ := by
        rw [Metric.mem_ball, dist_eq_norm]; linarith
      have hpkδ : ps k ∈ Metric.ball p δ := by
        rw [Metric.mem_ball, dist_eq_norm]; linarith
      have hbk := hbd (ps k) hpkδ
      rw [abs_le] at hbk
      have onesided : ∀ e : EuclideanSpace ℝ (Fin N), (qs k - q) e ≤ ε / 2 * ‖e‖ := by
        intro e
        rcases eq_or_ne e 0 with rfl | he
        · simp
        have hen : 0 < ‖e‖ := norm_pos_iff.2 he
        set τ : ℝ := (δ / 4) / ‖e‖ with hτdef
        have hτ : 0 < τ := by positivity
        have hτe : τ * ‖e‖ = δ / 4 := by rw [hτdef]; field_simp
        have hyd : (ps k + τ • e) - ps k = τ • e := by abel
        have hydp : (ps k + τ • e) - p - (ps k - p) = τ • e := by abel
        have hynorm : ‖(ps k + τ • e) - p‖ ≤ ‖ps k - p‖ + δ / 4 := by
          have hre : (ps k + τ • e) - p = (ps k - p) + τ • e := by abel
          rw [hre]
          calc ‖(ps k - p) + τ • e‖ ≤ ‖ps k - p‖ + ‖τ • e‖ := norm_add_le _ _
            _ = ‖ps k - p‖ + δ / 4 := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ, hτe]
        have hyρ : (ps k + τ • e) ∈ Metric.ball p ρ := by
          rw [Metric.mem_ball, dist_eq_norm]; linarith
        have hyδ : (ps k + τ • e) ∈ Metric.ball p δ := by
          rw [Metric.mem_ball, dist_eq_norm]; linarith
        have hsg := subgradOf (Metric.ball p ρ) g (ps k) (qs k) hconv hpkρ (hgqs k)
          (ps k + τ • e) hyρ
        rw [hyd, map_smul, smul_eq_mul] at hsg
        have hby := hbd (ps k + τ • e) hyδ
        rw [abs_le] at hby
        have hqlin : q ((ps k + τ • e) - p) - q (ps k - p) = τ * q e := by
          rw [← map_sub, hydp, map_smul, smul_eq_mul]
        have hp1 : ε / 4 * ‖(ps k + τ • e) - p‖ ≤ ε / 4 * (‖ps k - p‖ + δ / 4) :=
          mul_le_mul_of_nonneg_left hynorm (by positivity)
        have hp2 : ε / 4 * ‖ps k - p‖ ≤ ε / 4 * (δ / 8) :=
          mul_le_mul_of_nonneg_left hpk.le (by positivity)
        have hb1 : τ * ((qs k) e - q e) ≤ ε * δ / 8 := by
          linarith [hsg, hby.1, hby.2, hbk.1, hbk.2, hqlin, hp1, hp2]
        have hb2 : τ * ((qs k) e - q e) ≤ τ * (ε / 2 * ‖e‖) := by
          have heq : τ * (ε / 2 * ‖e‖) = ε * δ / 8 := by
            rw [hτdef]; field_simp; ring
          rw [heq]; exact hb1
        have hb3 := le_of_mul_le_mul_left hb2 hτ
        simpa using hb3
      have habs : ∀ e : EuclideanSpace ℝ (Fin N), ‖(qs k - q) e‖ ≤ ε / 2 * ‖e‖ := by
        intro e
        have h1 := onesided e
        have h2 := onesided (-e)
        rw [map_neg, norm_neg] at h2
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith, h1⟩
      have hop : ‖qs k - q‖ ≤ ε / 2 :=
        (qs k - q).opNorm_le_bound (by positivity) habs
      rw [dist_eq_norm]
      linarith
    -- Transfer back from `g` to `W`.
    have hinner : Filter.Tendsto (fun k => Λ • (innerSL ℝ) (ps k)) Filter.atTop
        (nhds (Λ • (innerSL ℝ) p)) := by
      have h1 : Filter.Tendsto (fun k => (innerSL ℝ) (ps k)) Filter.atTop
          (nhds ((innerSL ℝ) p)) := ((innerSL ℝ).continuous.tendsto p).comp hps
      exact h1.const_smul Λ
    have hEseq : Es = fun k => qs k - Λ • (innerSL ℝ) (ps k) := by
      funext k
      simp only [hqsdef]
      abel
    have hE0eq : E₀ = q - Λ • (innerSL ℝ) p := by
      simp only [hqdef]
      abel
    rw [hEseq, hE0eq]
    exact hmainlim.sub hinner
  rcases hw with hw1 | hw2
  · exact main w hw1 x hx xs hlim D hD Ds hDs
  · have h := main (fun y => -w y) hw2 x hx xs hlim (-D) hD.neg (fun k => -(Ds k))
      (fun k => (hDs k).neg)
    simpa using h.neg
