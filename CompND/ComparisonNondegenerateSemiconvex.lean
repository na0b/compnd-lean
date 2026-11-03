import CompND.AddConstPreservesSubsol
import CompND.CitedResults
import CompND.ClassicalAtTwiceDiff
import CompND.ExpRelabelling
import CompND.JensenTwiceDiffPoint
import CompND.RelabellingGradientBound
import CompND.SemiConvexCompose
import CompND.SemiConvexDiffAtMax
import CompND.StrictSubsolutionPerturbation
import CompND.TraceMonotone
import CompND.SecondOrderJetCalculus
import CompND.ExpRelabellingJetDescent
import CompND.QuarticPenaltyCalculus
import CompND.JetHessianLowerBoundOfConvex
import CompND.HgradTendstoOfTendsto
import CompND.ExpRelabelledMaxDifferentiability
set_option maxHeartbeats 1000000

/-- prop:comp0, the non-degenerate case: on a bounded open `Ω`, not necessarily connected,
a semi-convex viscosity sub-solution `u` and a semi-concave viscosity super-solution `v`,
both in `C(closure Ω)`, with `u ≤ v` on `∂Ω` and `𝔛u` non-vanishing on
`argmax_Ω (u - v)`, satisfy `u ≤ v` in `Ω`. -/
theorem ComparisonNondegenerateSemiconvex (G : CarnotSetting) (hc : CitedResults G)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (hAH : StructureConditionsES G.m A H) (hN : NormalizedAH G.m A H)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (husc : LocallySemiConvexOn Ω u) (hvsc : LocallySemiConvexOn Ω (fun y => -v y))
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x)
    (hsub : IsViscSubsol G A H Ω u) (hsup : IsViscSupersol G A H Ω v)
    (hnd : ∀ x ∈ Ω, IsMaxOn (fun y => u y - v y) Ω x →
      ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ, HasFDerivAt u D x →
        hgrad G.sig x D ≠ 0) :
    ∀ x ∈ Ω, u x ≤ v x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨xstar, hxstar, hstar⟩ := hcon
  -- `closure Ω` is compact, and `u - v` is continuous on it, so the max `M₀` is attained.
  have hclcpt : IsCompact (closure Ω) := hΩb.isCompact_closure
  have hdc : ContinuousOn (fun y => u y - v y) (closure Ω) := hucont.sub hvcont
  have hclne : (closure Ω).Nonempty := ⟨xstar, subset_closure hxstar⟩
  obtain ⟨x₀, hx₀cl, hx₀max⟩ := hclcpt.exists_isMaxOn hclne hdc
  have hmaxval : ∀ y ∈ closure Ω, u y - v y ≤ u x₀ - v x₀ := fun y hy => hx₀max hy
  have hM₀pos : 0 < u x₀ - v x₀ := by
    have h := hmaxval xstar (subset_closure hxstar)
    linarith
  set M₀ : ℝ := u x₀ - v x₀ with hM₀def
  -- `u - v ≤ 0 < M₀` on `∂Ω`, so every maximum point lies in `Ω`.
  have hfr : frontier Ω = closure Ω \ Ω := hΩo.frontier_eq
  have hinΩ : ∀ x ∈ closure Ω, u x - v x = M₀ → x ∈ Ω := by
    intro x hx hval
    by_contra hxn
    have hxfr : x ∈ frontier Ω := by rw [hfr]; exact ⟨hx, hxn⟩
    have hb := hbdry x hxfr
    linarith [hM₀pos, hval, hb]
  have hx₀Ω : x₀ ∈ Ω := hinΩ x₀ hx₀cl rfl
  -- `E := argmax_Ω (u - v)` is a non-empty compact subset of `Ω`.
  set E : Set (EuclideanSpace ℝ (Fin G.n)) := {x ∈ closure Ω | u x - v x = M₀} with hEdef
  have hEΩ : E ⊆ Ω := fun x hx => hinΩ x hx.1 hx.2
  have hEcl : IsClosed E := by
    have hrw : E = closure Ω ∩ (fun y => u y - v y) ⁻¹' {M₀} := by rw [hEdef]; rfl
    rw [hrw]
    exact hdc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  have hEcpt : IsCompact E := hclcpt.of_isClosed_subset hEcl fun x hx => hx.1
  have hEmax : ∀ x ∈ E, IsMaxOn (fun y => u y - v y) Ω x := by
    intro x hx y hy
    show u y - v y ≤ u x - v x
    have h1 := hmaxval y (subset_closure hy)
    have h2 : u x - v x = M₀ := hx.2
    linarith
  -- Replace `v` by `v₁ := v + τ` with `0 < τ < M₀`; this is display (0).
  set τ : ℝ := M₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτlt : τ < M₀ := by rw [hτdef]; linarith
  set v₁ : EuclideanSpace ℝ (Fin G.n) → ℝ := fun y => v y + τ with hv₁def
  have hdiff1 : ∀ y, u y - v₁ y = u y - v y - τ := by
    intro y; simp only [hv₁def]; ring
  have hv₁cont : ContinuousOn v₁ (closure Ω) := hvcont.add continuousOn_const
  have hv₁sc : LocallySemiConvexOn Ω (fun y => -v₁ y) := by
    intro x hx
    obtain ⟨ρ, hρ, Λ, hΛ, hball, hcv⟩ := hvsc x hx
    refine ⟨ρ, hρ, Λ, hΛ, hball, ?_⟩
    refine ⟨hcv.1, fun p hp q hq a b ha hb hab => ?_⟩
    have h := hcv.2 hp hq ha hb hab
    have hab' : a * τ + b * τ = τ := by rw [← add_mul, hab, one_mul]
    simp only [hv₁def, smul_eq_mul] at h ⊢
    linarith only [h, hab']
  have hv₁sup : IsViscSupersol G A H Ω v₁ := (AddConstPreservesSubsol G A H Ω v τ).2 hsup
  have h0max : ∀ y ∈ closure Ω, u y - v₁ y ≤ M₀ - τ := by
    intro y hy
    rw [hdiff1]
    linarith [hmaxval y hy]
  have h0att : u x₀ - v₁ x₀ = M₀ - τ := by rw [hdiff1, hM₀def]
  have hM₁pos : 0 < M₀ - τ := by rw [hτdef]; linarith
  have h0bdry : ∀ x ∈ frontier Ω, u x - v₁ x ≤ -τ := by
    intro x hx
    rw [hdiff1]
    linarith [hbdry x hx]
  have hEmax1 : ∀ x ∈ E, IsMaxOn (fun y => u y - v₁ y) Ω x := by
    intro x hx y hy
    show u y - v₁ y ≤ u x - v₁ x
    rw [hdiff1, hdiff1]
    have h1 := hmaxval y (subset_closure hy)
    have h2 : u x - v x = M₀ := hx.2
    linarith
  -- Step 1(a): `u` is differentiable on `E`, and `θ := min_E ‖𝔛u‖ > 0`.
  have hEdiff : ∀ x ∈ E, ∃ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ, HasFDerivAt u D x := by
    intro x hx
    obtain ⟨D, hDu, _⟩ :=
      (SemiConvexDiffAtMax Ω u v₁ husc hv₁sc).2 x (hEΩ hx) (hEmax1 x hx)
    exact ⟨D, hDu⟩
  have hEnz : ∀ x ∈ E, ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
      HasFDerivAt u D x → hgrad G.sig x D ≠ 0 := fun x hx D hD =>
    hnd x (hEΩ hx) (hEmax x hx) D hD
  have hgradeq : ∀ (y : EuclideanSpace ℝ (Fin G.n))
      (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      hgrad G.sig y D = (EuclideanSpace.equiv (Fin G.m) ℝ).symm (fun i => D (G.sig y i)) :=
    fun _ _ => rfl
  have hsigc : ∀ i, Continuous fun x => G.sig x i := fun i => (G.sig_smooth i).continuous
  have htheta : ∃ θ : ℝ, 0 < θ ∧ ∀ x ∈ E, ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
      HasFDerivAt u D x → θ ≤ ‖hgrad G.sig x D‖ := by
    by_contra hc2
    push Not at hc2
    have hstep : ∀ k : ℕ, ∃ (xk : EuclideanSpace ℝ (Fin G.n))
        (Dk : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
        xk ∈ E ∧ HasFDerivAt u Dk xk ∧ ‖hgrad G.sig xk Dk‖ < 1 / (k + 1 : ℝ) := by
      intro k
      obtain ⟨xk, hxk, Dk, hDk, hlt⟩ := hc2 (1 / (k + 1 : ℝ)) (by positivity)
      exact ⟨xk, Dk, hxk, hDk, hlt⟩
    choose xs Ds hxsE hDs hbd using hstep
    obtain ⟨xhat, hxhatE, φ, hφmono, hφlim⟩ := hEcpt.tendsto_subseq hxsE
    obtain ⟨Dhat, hDhat⟩ := hEdiff xhat hxhatE
    have hpc : Filter.Tendsto (fun j => Ds (φ j)) Filter.atTop (nhds Dhat) :=
      SemiConvexGradPartialCont Ω u (Or.inl husc) xhat (hEΩ hxhatE) (fun j => xs (φ j))
        (fun j => hEΩ (hxsE (φ j))) hφlim Dhat hDhat (fun j => Ds (φ j))
        (fun j => hDs (φ j))
    -- the same two-term split as `HgradTendstoOfTendsto`, which this now simply applies;
    -- before the extraction this argument had to be written out here as well, because the
    -- parent-local version was introduced only later in the proof
    have hconv : Filter.Tendsto (fun j => hgrad G.sig (xs (φ j)) (Ds (φ j))) Filter.atTop
        (nhds (hgrad G.sig xhat Dhat)) :=
      HgradTendstoOfTendsto G.sig hsigc (fun j => xs (φ j)) xhat (fun j => Ds (φ j)) Dhat
        hφlim hpc
    have hlim0 : ‖hgrad G.sig xhat Dhat‖ ≤ 0 := by
      refine le_of_tendsto_of_tendsto hconv.norm
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_
      filter_upwards with j
      have hj : (j : ℝ) ≤ ((φ j : ℕ) : ℝ) := by exact_mod_cast hφmono.le_apply
      have h2 : 1 / (((φ j : ℕ) : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [hbd (φ j)]
    exact hEnz xhat hxhatE Dhat hDhat
      (norm_eq_zero.1 (le_antisymm hlim0 (norm_nonneg _)))
  obtain ⟨θ, hθpos, hθE⟩ := htheta
  -- the sup bound `|u| ≤ M` on the compact `closure Ω`, which (1b) feeds to `ExpRelabelling`
  obtain ⟨M, hMnn, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ closure Ω, |u y| ≤ M := by
    obtain ⟨Mb, hMb⟩ := hclcpt.bddAbove_image (continuous_abs.comp_continuousOn hucont)
    exact ⟨max Mb 0, le_max_right _ _, fun y hy =>
      (hMb (Set.mem_image_of_mem _ hy)).trans (le_max_left _ _)⟩
  -- Step 1(b): the exponential relabelling `ψ_λ(s) = s + λ e^s` (pm-0014), from
  -- `ExpRelabelling`; `u_λ` is locally semi-convex by the first clause of `SemiConvexCompose`.
  set psi : ℝ → ℝ → ℝ := fun lam s => s + lam * Real.exp s with hpsidef
  have hpsiC2 : ∀ lam : ℝ, 0 < lam → ContDiff ℝ 2 (psi lam) := fun lam hlam =>
    (ExpRelabelling lam M hlam).1
  have hpsid1 : ∀ lam : ℝ, 0 < lam → ∀ s, 1 ≤ deriv (psi lam) s := fun lam hlam =>
    (ExpRelabelling lam M hlam).2.2.1
  have hpsid2 : ∀ lam : ℝ, 0 < lam → ∀ s, 0 ≤ deriv (deriv (psi lam)) s := fun lam hlam =>
    (ExpRelabelling lam M hlam).2.2.2.2.1
  have hpsiclose : ∀ lam : ℝ, 0 < lam → ∀ s, |s| ≤ M → |psi lam s - s| ≤ lam * Real.exp M :=
    fun lam hlam => (ExpRelabelling lam M hlam).2.2.2.2.2.2.2
  have hulamsc : ∀ lam : ℝ, 0 < lam → LocallySemiConvexOn Ω (fun y => psi lam (u y)) :=
    fun lam hlam => (SemiConvexCompose Ω u husc).1 (psi lam) (hpsiC2 lam hlam)
      (hpsid1 lam hlam) (hpsid2 lam hlam)
  have hpsicont : ∀ lam : ℝ, Continuous (psi lam) := by
    intro lam
    simp only [hpsidef]
    exact continuous_id.add (continuous_const.mul Real.continuous_exp)
  have hulamcont : ∀ lam : ℝ, ContinuousOn (fun y => psi lam (u y)) (closure Ω) :=
    fun lam => (hpsicont lam).comp_continuousOn hucont
  have hclose : ∀ lam : ℝ, 0 < lam → ∀ y ∈ closure Ω,
      |psi lam (u y) - u y| ≤ lam * Real.exp M := fun lam hlam y hy =>
    hpsiclose lam hlam (u y) (hMb y hy)
  -- the family `E_λ`, with `Ω`-membership built in so that `RelabellingGradientBound`'s
  -- `hElamΩ` holds for every positive `λ` with no case split.
  set Elam : ℝ → Set (EuclideanSpace ℝ (Fin G.n)) :=
    fun lam => {x ∈ Ω | ∀ y ∈ Ω, psi lam (u y) - v₁ y ≤ psi lam (u x) - v₁ x} with hElamdef
  have hElamΩ : ∀ lam : ℝ, 0 < lam → Elam lam ⊆ Ω := fun lam _ x hx => hx.1
  -- display (3), in the form 1(d) consumes: this needs no smallness of `λ` at all.
  have h1cval : ∀ lam : ℝ, 0 < lam → ∀ x ∈ Elam lam,
      M₀ - τ - 2 * (lam * Real.exp M) ≤ u x - v₁ x ∧ u x - v₁ x ≤ M₀ - τ := by
    intro lam hlam x hx
    have hxcl : x ∈ closure Ω := subset_closure hx.1
    have h1 := hx.2 x₀ hx₀Ω
    have h2 := abs_le.1 (hclose lam hlam x hxcl)
    have h3 := abs_le.1 (hclose lam hlam x₀ hx₀cl)
    exact ⟨by linarith only [h1, h2.1, h2.2, h3.1, h3.2, h0att], h0max x hxcl⟩
  -- Step 1(c): for `λ` satisfying display (2), `E_λ` is non-empty, and its points are
  -- maximisers over all of `closure Ω`.
  have h1cne : ∀ lam : ℝ, 0 < lam → lam * Real.exp M ≤ τ / 2 →
      lam * Real.exp M ≤ (M₀ - τ) / 2 →
      ∃ xl ∈ Elam lam, ∀ y ∈ closure Ω,
        psi lam (u y) - v₁ y ≤ psi lam (u xl) - v₁ xl := by
    intro lam hlam h2a h2b
    have hcont : ContinuousOn (fun y => psi lam (u y) - v₁ y) (closure Ω) :=
      (hulamcont lam).sub hv₁cont
    obtain ⟨xl, hxlcl, hxlmax⟩ := hclcpt.exists_isMaxOn hclne hcont
    have hmax' : ∀ y ∈ closure Ω, psi lam (u y) - v₁ y ≤ psi lam (u xl) - v₁ xl :=
      fun y hy => hxlmax hy
    have hpos : 0 < psi lam (u xl) - v₁ xl := by
      have h1 := hmax' x₀ hx₀cl
      have h3 := abs_le.1 (hclose lam hlam x₀ hx₀cl)
      linarith only [h1, h3.1, h3.2, h0att, h2b, hM₁pos]
    have hxlΩ : xl ∈ Ω := by
      by_contra hc
      have hfrx : xl ∈ frontier Ω := by rw [hfr]; exact ⟨hxlcl, hc⟩
      have h4 := abs_le.1 (hclose lam hlam xl hxlcl)
      linarith only [hpos, h4.1, h4.2, h0bdry xl hfrx, h2a, hτpos]
    exact ⟨xl, ⟨hxlΩ, fun y hy => hmax' y (subset_closure hy)⟩, hmax'⟩
  -- Step 1(d): `sup_{E_λ} dist(·, E) → 0` as `λ → 0⁺`.
  have hdc1 : ContinuousOn (fun y => u y - v₁ y) (closure Ω) := hucont.sub hv₁cont
  have h1d : ∀ η : ℝ, 0 < η → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ x ∈ Elam lam, ∃ z ∈ E, dist x z ≤ η := by
    intro η hη
    by_contra hcd
    push Not at hcd
    have hstep : ∀ k : ℕ, ∃ (lamk : ℝ) (xk : EuclideanSpace ℝ (Fin G.n)),
        0 < lamk ∧ lamk < 1 / (k + 1 : ℝ) ∧ xk ∈ Elam lamk ∧ ∀ z ∈ E, η < dist xk z := by
      intro k
      obtain ⟨lamk, hlamk0, hlamklt, xk, hxk, hfar⟩ := hcd (1 / (k + 1 : ℝ)) (by positivity)
      exact ⟨lamk, xk, hlamk0, hlamklt, hxk, hfar⟩
    choose lams xs hlams0 hlamslt hxsE hfar using hstep
    have hxscl : ∀ k, xs k ∈ closure Ω := fun k => subset_closure (hxsE k).1
    obtain ⟨xhat, hxhatcl, φ, hφmono, hφlim⟩ := hclcpt.tendsto_subseq hxscl
    have hexpos : (0:ℝ) < Real.exp M := Real.exp_pos M
    have hbnd : Filter.Tendsto (fun j : ℕ => 2 * Real.exp M * (1 / ((j : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (2 * Real.exp M)
      simpa using h
    have hvals : Filter.Tendsto (fun j => u (xs (φ j)) - v₁ (xs (φ j))) Filter.atTop
        (nhds (M₀ - τ)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hbnd
      rw [Real.dist_eq]
      have hv := h1cval (lams (φ j)) (hlams0 (φ j)) (xs (φ j)) (hxsE (φ j))
      have hj : (j : ℝ) ≤ ((φ j : ℕ) : ℝ) := by exact_mod_cast hφmono.le_apply
      have hle : lams (φ j) ≤ 1 / ((j : ℝ) + 1) := by
        have h1 : 1 / (((φ j : ℕ) : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith only [hlamslt (φ j), h1]
      have hprod : lams (φ j) * Real.exp M ≤ 1 / ((j : ℝ) + 1) * Real.exp M :=
        mul_le_mul_of_nonneg_right hle hexpos.le
      have hnn : (0:ℝ) ≤ 2 * Real.exp M * (1 / ((j : ℝ) + 1)) := by positivity
      rw [abs_le]
      exact ⟨by linarith only [hv.1, hprod], by linarith only [hv.2, hnn]⟩
    have hw : Filter.Tendsto (fun j => xs (φ j)) Filter.atTop
        (nhdsWithin xhat (closure Ω)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφlim
        (Filter.Eventually.of_forall fun j => hxscl (φ j))
    have hcts : Filter.Tendsto (fun j => u (xs (φ j)) - v₁ (xs (φ j))) Filter.atTop
        (nhds (u xhat - v₁ xhat)) := Filter.Tendsto.comp (hdc1 xhat hxhatcl) hw
    have hval : u xhat - v₁ xhat = M₀ - τ := tendsto_nhds_unique hcts hvals
    have hxhatΩ : xhat ∈ Ω := by
      by_contra hc
      have hfrx : xhat ∈ frontier Ω := by rw [hfr]; exact ⟨hxhatcl, hc⟩
      linarith only [h0bdry xhat hfrx, hval, hM₁pos, hτpos]
    have hxhatE : xhat ∈ E := ⟨hxhatcl, by linarith only [hval, hdiff1 xhat]⟩
    obtain ⟨Nn, hNn⟩ := Metric.tendsto_atTop.1 hφlim η hη
    have hclose1 : dist (xs (φ Nn)) xhat < η := hNn Nn le_rfl
    linarith only [hclose1, hfar (φ Nn) xhat hxhatE]
  -- Step 1(e): display (4), eq:thetahalf on `E_λ`.
  obtain ⟨lam₀, hlam₀pos, h1e⟩ :=
    RelabellingGradientBound G.sig hsigc Ω u husc E hEcpt hEΩ hEdiff θ hθpos hθE
      Elam hElamΩ h1d
  -- "Fix λ": small enough for display (2) and below `lam₀`.
  have hexpM : (0:ℝ) < Real.exp M := Real.exp_pos M
  have hcancel : ∀ b : ℝ, b / (2 * Real.exp M) * Real.exp M = b / 2 := by
    intro b; field_simp
  obtain ⟨lam, hlam0, hlamlt, hlam2a, hlam2b⟩ :
      ∃ lam : ℝ, 0 < lam ∧ lam < lam₀ ∧ lam * Real.exp M ≤ τ / 2 ∧
        lam * Real.exp M ≤ (M₀ - τ) / 2 := by
    refine ⟨min (lam₀ / 2) (min (τ / (2 * Real.exp M)) ((M₀ - τ) / (2 * Real.exp M))),
      lt_min (by linarith) (lt_min (by positivity) (by positivity)), ?_, ?_, ?_⟩
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · have h1 : min (lam₀ / 2) (min (τ / (2 * Real.exp M)) ((M₀ - τ) / (2 * Real.exp M)))
          ≤ τ / (2 * Real.exp M) := (min_le_right _ _).trans (min_le_left _ _)
      have h2 := mul_le_mul_of_nonneg_right h1 hexpM.le
      rw [hcancel] at h2
      exact h2
    · have h1 : min (lam₀ / 2) (min (τ / (2 * Real.exp M)) ((M₀ - τ) / (2 * Real.exp M)))
          ≤ (M₀ - τ) / (2 * Real.exp M) := (min_le_right _ _).trans (min_le_right _ _)
      have h2 := mul_le_mul_of_nonneg_right h1 hexpM.le
      rw [hcancel] at h2
      exact h2
  -- `ũ := u_λ`, `M̃`, and `E_λ` a non-empty compact subset of `Ω`.
  obtain ⟨xl, hxlE, hxlmax⟩ := h1cne lam hlam0 hlam2a hlam2b
  set Mtilde : ℝ := psi lam (u xl) - v₁ xl with hMtildedef
  have hMtildepos : 0 < Mtilde := by
    have h1 := hxlmax x₀ hx₀cl
    have h3 := abs_le.1 (hclose lam hlam0 x₀ hx₀cl)
    rw [hMtildedef]
    linarith only [h1, h3.1, h3.2, h0att, hlam2b, hM₁pos]
  have hElamval : ∀ x ∈ Elam lam, psi lam (u x) - v₁ x = Mtilde := by
    intro x hx
    have h1 := hx.2 xl hxlE.1
    have h2 := hxlmax x (subset_closure hx.1)
    rw [hMtildedef]
    linarith only [h1, h2]
  have hElameq : Elam lam = {x ∈ closure Ω | psi lam (u x) - v₁ x = Mtilde} := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      exact ⟨subset_closure hx.1, hElamval x hx⟩
    · intro x hx
      refine ⟨?_, fun y hy => ?_⟩
      · by_contra hc
        have hfrx : x ∈ frontier Ω := by rw [hfr]; exact ⟨hx.1, hc⟩
        have h4 := abs_le.1 (hclose lam hlam0 x hx.1)
        have h5 := hx.2
        linarith only [hMtildepos, h4.1, h4.2, h0bdry x hfrx, hlam2a, hτpos, h5]
      · rw [hx.2]
        exact hxlmax y (subset_closure hy)
  -- display (4): eq:thetahalf on `E_λ`
  have h4 : ∀ x ∈ Elam lam, ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
      HasFDerivAt u D x → θ / 2 ≤ ‖hgrad G.sig x D‖ := h1e lam hlam0 hlamlt
  -- `λ' = λ e^{-M}`, the ellipticity constant `e₀`, and `γ = λ' e₀ (θ/4)²`
  set lamp : ℝ := lam * Real.exp (-M) with hlampdef
  have hlamppos : 0 < lamp := by rw [hlampdef]; positivity
  obtain ⟨e₀, he₀pos, he₀⟩ := EllipticityLowerBound A H hAH hN
  set gam : ℝ := lamp * e₀ * (θ / 4) ^ 2 with hgamdef
  have hgampos : 0 < gam := by rw [hgamdef]; positivity
  -- the differentiability side-claim of 1(e): every point of `E_λ` is a differentiability
  -- point of `u`, so display (4) is not vacuous.  This is
  -- `ExpRelabelledMaxDifferentiability`, applied at the single point `xl` below; the
  -- expanding-relabelling argument it runs on lives in that node.
  -- The second-order jet calculus (J1)/(J2) and the jet of a linear functional, all five
  -- facts lifted out of this proof.
  obtain ⟨jetOfCubicBound, jetAdd, jetNeg, jetSub, jetLinear⟩ :=
    SecondOrderJetCalculus (N := G.n)
  -- Step 2: the quartic penalization `P(x) = μ‖x - x₁‖⁴`, kept parametric in `(μ, x₁)`
  -- because `μ` is only constrained later.
  set Pf : ℝ → EuclideanSpace ℝ (Fin G.n) → EuclideanSpace ℝ (Fin G.n) → ℝ :=
    fun mu c x => mu * ‖x - c‖ ^ 4 with hPfdef
  set DPf : ℝ → EuclideanSpace ℝ (Fin G.n) → EuclideanSpace ℝ (Fin G.n) →
      (EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ) :=
    fun mu c x => (4 * mu * ‖x - c‖ ^ 2) • innerSL ℝ (x - c) with hDPfdef
  obtain ⟨Bi, hBiapp⟩ : ∃ Bi : EuclideanSpace ℝ (Fin G.n) →L[ℝ]
      EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ, ∀ a b, Bi a b = (inner ℝ a b : ℝ) :=
    ⟨innerSL ℝ, fun _ _ => rfl⟩
  set D2Pf : ℝ → EuclideanSpace ℝ (Fin G.n) → EuclideanSpace ℝ (Fin G.n) →
      (EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ) :=
    fun mu c x => (4 * mu * ‖x - c‖ ^ 2) • Bi
      + (8 * mu) • ((innerSL ℝ (x - c)).smulRight (innerSL ℝ (x - c))) with hD2Pfdef
  -- the calculus of the quartic penalty, all of `QuarticPenaltyCalculus`: symmetry of the
  -- second differential, the two operator-norm bounds of display (6), the second-order jet
  -- of `P` (by (J1), the remainder of a quartic being cubic), the vanishing of `P` at its
  -- centre and its positivity elsewhere, the parallelogram identity, and the chord-form
  -- convexity defect `6 μ R² t(1-t)|x-y|²` that semi-convexity of `-P` runs on.
  obtain ⟨hD2Pfsymm, hDPfbound, hD2Pfbound, hPfjet, hPfzero, hPfpos, hpara, hPfdefect⟩ :=
    QuarticPenaltyCalculus Pf DPf D2Pf Bi (fun mu c x => by simp only [hPfdef])
      (fun mu c x => by simp only [hDPfdef]) hBiapp
      (fun mu c x => by simp only [hD2Pfdef])
  -- `-P` is locally semi-convex on `Ω`, with `Λ = 12 μ (|x - c| + ρ)²` on `B(x, ρ)`
  have hnPfsc : ∀ mu : ℝ, 0 ≤ mu → ∀ c : EuclideanSpace ℝ (Fin G.n),
      LocallySemiConvexOn Ω (fun y => -Pf mu c y) := by
    intro mu hmu c x hx
    obtain ⟨ρ, hρpos, hball⟩ := Metric.isOpen_iff.1 hΩo x hx
    refine ⟨ρ, hρpos, 12 * mu * (‖x - c‖ + ρ) ^ 2, by positivity, hball, ?_⟩
    refine ⟨convex_ball x ρ, fun p hp q hq a b ha hb hab => ?_⟩
    have hbe : b = 1 - a := by linarith only [hab]
    subst hbe
    have hRnn : (0:ℝ) ≤ ‖x - c‖ + ρ := by positivity
    have hpR : ‖p - c‖ ≤ ‖x - c‖ + ρ := by
      have h1 : ‖p - x‖ < ρ := by
        have h := Metric.mem_ball.1 hp
        rwa [dist_eq_norm] at h
      have h2 : ‖p - c‖ ≤ ‖p - x‖ + ‖x - c‖ := by
        rw [show p - c = p - x + (x - c) from by abel]
        exact norm_add_le _ _
      linarith only [h1, h2]
    have hqR : ‖q - c‖ ≤ ‖x - c‖ + ρ := by
      have h1 : ‖q - x‖ < ρ := by
        have h := Metric.mem_ball.1 hq
        rwa [dist_eq_norm] at h
      have h2 : ‖q - c‖ ≤ ‖q - x‖ + ‖x - c‖ := by
        rw [show q - c = q - x + (x - c) from by abel]
        exact norm_add_le _ _
      linarith only [h1, h2]
    have hdef := hPfdefect mu hmu c (‖x - c‖ + ρ) hRnn p q hpR hqR a ha
      (by linarith only [hb])
    have hpar := hpara p q a
    simp only [smul_eq_mul]
    rw [hpar]
    linarith only [hdef]
  -- sums of locally semi-convex functions are locally semi-convex
  have scAdd : ∀ f g : EuclideanSpace ℝ (Fin G.n) → ℝ,
      LocallySemiConvexOn Ω f → LocallySemiConvexOn Ω g →
      LocallySemiConvexOn Ω (fun y => f y + g y) := by
    intro f g hf hg x hx
    obtain ⟨ρ₁, hρ₁, Λ₁, hΛ₁, hb₁, hc₁⟩ := hf x hx
    obtain ⟨ρ₂, hρ₂, Λ₂, hΛ₂, hb₂, hc₂⟩ := hg x hx
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, Λ₁ + Λ₂, by linarith only [hΛ₁, hΛ₂],
      (Metric.ball_subset_ball (min_le_left _ _)).trans hb₁, ?_⟩
    refine ⟨convex_ball x _, fun p hp q hq a b ha hb hab => ?_⟩
    have h1 := hc₁.2 (Metric.ball_subset_ball (min_le_left ρ₁ ρ₂) hp)
      (Metric.ball_subset_ball (min_le_left ρ₁ ρ₂) hq) ha hb hab
    have h2 := hc₂.2 (Metric.ball_subset_ball (min_le_right ρ₁ ρ₂) hp)
      (Metric.ball_subset_ball (min_le_right ρ₁ ρ₂) hq) ha hb hab
    simp only [smul_eq_mul] at h1 h2 ⊢
    linarith only [h1, h2]
  -- `ṽ := v₁ + P` is locally semi-concave in `Ω` and continuous on `closure Ω`
  have hvtsc : ∀ mu : ℝ, 0 ≤ mu → ∀ c : EuclideanSpace ℝ (Fin G.n),
      LocallySemiConvexOn Ω (fun y => -(v₁ y + Pf mu c y)) := by
    intro mu hmu c
    have h := scAdd (fun y => -v₁ y) (fun y => -Pf mu c y) hv₁sc (hnPfsc mu hmu c)
    intro x hx
    obtain ⟨ρ, hρ, Λ, hΛ, hball, hcv⟩ := h x hx
    refine ⟨ρ, hρ, Λ, hΛ, hball, ⟨hcv.1, fun p hp q hq a b ha hb hab => ?_⟩⟩
    have h2 := hcv.2 hp hq ha hb hab
    simp only [smul_eq_mul] at h2 ⊢
    linarith only [h2]
  -- `x₁ := xl ∈ E_λ ⊆ Ω`, so some ball around it sits inside `Ω`
  have hxlΩ : xl ∈ Ω := hElamΩ lam hlam0 hxlE
  obtain ⟨nu, hnupos, hnuball⟩ := Metric.isOpen_iff.1 hΩo xl hxlΩ
  -- `x₁` is the *unique* maximum point of `ũ - ṽ` on `closure Ω` ...
  have h7cl : ∀ mu : ℝ, 0 < mu → ∀ y ∈ closure Ω, y ≠ xl →
      psi lam (u y) - (v₁ y + Pf mu xl y)
        < psi lam (u xl) - (v₁ xl + Pf mu xl xl) := by
    intro mu hmu y hy hne
    linarith only [hxlmax y hy, hPfpos mu hmu xl y hne, hPfzero mu xl]
  -- ... hence display (7): a strict maximum on `B(x₁, ν) ⊆ Ω`
  have h7 : ∀ mu : ℝ, 0 < mu → ∀ y ∈ Metric.ball xl nu, y ≠ xl →
      psi lam (u y) - (v₁ y + Pf mu xl y)
        < psi lam (u xl) - (v₁ xl + Pf mu xl xl) := fun mu hmu y hy hne =>
    h7cl mu hmu y (subset_closure (hnuball hy)) hne
  -- Step 2 fixes `x₁ := xl ∈ E_λ` and an arbitrary `μ > 0`; `μ` is never specialised
  -- later, so we fix it opaquely here.
  obtain ⟨mu, hmupos⟩ : ∃ mu : ℝ, 0 < mu := ⟨1, one_pos⟩
  have hmunn : (0:ℝ) ≤ mu := hmupos.le
  -- a second-order jet transfers along a pointwise equality of the functions
  have jetCongr : ∀ (w w' : EuclideanSpace ℝ (Fin G.n) → ℝ)
      (zz : EuclideanSpace ℝ (Fin G.n)) (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (Bq : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      (∀ y, w y = w' y) → TwiceDiffAt w zz D Bq → TwiceDiffAt w' zz D Bq := by
    intro w w' zz D Bq heq h
    rw [show w' = w from funext fun y => (heq y).symm]
    exact h
  -- Step 3: Jensen's lemma together with Aleksandrov's theorem, applied to the pair
  -- `(ũ, ṽ)` at the strict maximum `x₁`.  `CitedResults G` extends the Euclidean package,
  -- so its cited-results hypothesis is discharged by `hc.toEuclidCitedResults`.
  obtain ⟨pseq, zseq, hptend, hztend, hzk⟩ :=
    JensenTwiceDiffPoint hc.toEuclidCitedResults Ω (fun y => psi lam (u y))
      (fun y => v₁ y + Pf mu xl y) (hulamsc lam hlam0) (hvtsc mu hmunn xl) xl
      ⟨nu, hnupos, hnuball, fun y hy hne => h7 mu hmupos y hy hne⟩
  have hzkΩ : ∀ k, zseq k ∈ Ω := fun k => (hzk k).1
  have hzkmax : ∀ k, IsLocalMax
      (fun y => psi lam (u y) - (v₁ y + Pf mu xl y) + ∑ i, pseq k i * y i) (zseq k) :=
    fun k => (hzk k).2.1
  -- the jets of `ũ` and of `ṽ` at `z_k`
  obtain ⟨Dk, Bk, hjetu⟩ : ∃ (Dk : ℕ → EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (Bk : ℕ → EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      ∀ k, TwiceDiffAt (fun y => psi lam (u y)) (zseq k) (Dk k) (Bk k) := by
    choose Dk Bk h using fun k => (hzk k).2.2.1
    exact ⟨Dk, Bk, h⟩
  obtain ⟨Dtk, Btk, hjetv⟩ : ∃ (Dtk : ℕ → EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (Btk : ℕ → EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      ∀ k, TwiceDiffAt (fun y => v₁ y + Pf mu xl y) (zseq k) (Dtk k) (Btk k) := by
    choose Dtk Btk h using fun k => (hzk k).2.2.2
    exact ⟨Dtk, Btk, h⟩
  -- `δ_k := |p_k| + |z_k - x₁| → 0`, the role of the paper's `1/k`
  set del : ℕ → ℝ := fun k => ‖pseq k‖ + ‖zseq k - xl‖ with hdeldef
  have hpnorm : ∀ k, ‖pseq k‖ ≤ del k := fun k => by
    rw [hdeldef]; exact le_add_of_nonneg_right (norm_nonneg _)
  have hznorm : ∀ k, ‖zseq k - xl‖ ≤ del k := fun k => by
    rw [hdeldef]; exact le_add_of_nonneg_left (norm_nonneg _)
  have hdeltend : Filter.Tendsto del Filter.atTop (nhds 0) := by
    have hpn : Filter.Tendsto (fun k => ‖pseq k‖) Filter.atTop (nhds 0) := by
      simpa using hptend.norm
    have hzn : Filter.Tendsto (fun k => ‖zseq k - xl‖) Filter.atTop (nhds 0) := by
      simpa using (hztend.sub (tendsto_const_nhds (x := xl))).norm
    rw [hdeldef]
    simpa using hpn.add hzn
  -- `ρ := ν/2`, so that `K := closedBall x₁ ρ` is a compact subset of `Ω` containing
  -- `x₁`, and `z_k ∈ ball x₁ ρ` for all large `k`.  (Departure from the `.tex`: rather
  -- than discarding finitely many `k` we keep the full sequence and carry the
  -- `Filter.Eventually` statement, which is what every later use needs.)
  set rho : ℝ := nu / 2 with hrhodef
  have hrhopos : 0 < rho := by rw [hrhodef]; linarith only [hnupos]
  have hKsub : Metric.closedBall xl rho ⊆ Ω :=
    (Metric.closedBall_subset_ball (by rw [hrhodef]; linarith only [hnupos])).trans hnuball
  have hKcpt : IsCompact (Metric.closedBall xl rho) := isCompact_closedBall _ _
  have hzev : ∀ᶠ k in Filter.atTop, zseq k ∈ Metric.ball xl rho :=
    hztend.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrhopos))
  -- (3a), display: `(D^v_k, B^v_k) := (D̃_k - DP(z_k), B̃_k - D²P(z_k))` is a jet of
  -- `v₁ = ṽ - P` at `z_k`, by (J1) for the quartic `P` and (J2).
  have hjetv1 : ∀ k, TwiceDiffAt v₁ (zseq k)
      (Dtk k - DPf mu xl (zseq k)) (Btk k - D2Pf mu xl (zseq k)) := by
    intro k
    refine jetCongr (fun y => (v₁ y + Pf mu xl y) - Pf mu xl y) v₁ (zseq k) _ _
      (fun y => by ring) ?_
    exact jetSub (fun y => v₁ y + Pf mu xl y) (Pf mu xl) (zseq k) (Dtk k)
      (DPf mu xl (zseq k)) (Btk k) (D2Pf mu xl (zseq k)) (hjetv k)
      (hPfjet mu hmunn xl (zseq k))
  -- and `(D̃_k - p_k, B̃_k)` is a jet of `ṽ - ⟪p_k, ·⟫` at `z_k`, by (J1) for the linear
  -- functional and (J2).
  have hjetvp : ∀ k, TwiceDiffAt (fun y => v₁ y + Pf mu xl y - ∑ i, pseq k i * y i)
      (zseq k) (Dtk k - innerSL ℝ (pseq k)) (Btk k) := by
    intro k
    have h := jetSub (fun y => v₁ y + Pf mu xl y) (fun y => ∑ i, pseq k i * y i)
      (zseq k) (Dtk k) (innerSL ℝ (pseq k)) (Btk k) 0 (hjetv k) (jetLinear (pseq k) (zseq k))
    have he : Btk k - (0 : EuclideanSpace ℝ (Fin G.n) →L[ℝ]
        EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ) = Btk k := by
      ext a b
      simp
    rw [he] at h
    exact h
  -- (3a), first-order fact: a function with a second-order jet at `z` is Fréchet
  -- differentiable there, with the jet's linear part as derivative.  (Accuracy `ε = 1`
  -- in `TwiceDiffAt` plus the bound `|B(h,h)| ≤ ‖B‖|h|²` make the remainder `O(|h|²)`.)
  have jetFDeriv : ∀ (w : EuclideanSpace ℝ (Fin G.n) → ℝ)
      (zz : EuclideanSpace ℝ (Fin G.n)) (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (Bq : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      TwiceDiffAt w zz D Bq → HasFDerivAt w D zz := by
    intro w zz D Bq h
    rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := h.2 1 one_pos
    have hc1 : (0:ℝ) < 1 + ‖Bq‖ / 2 := by positivity
    have hnb : ∀ᶠ y in nhds zz, ‖y - zz‖ < min δ (ε / (1 + ‖Bq‖ / 2)) := by
      refine Metric.eventually_nhds_iff.2 ⟨min δ (ε / (1 + ‖Bq‖ / 2)),
        lt_min hδ (by positivity), fun y hy => ?_⟩
      rwa [dist_eq_norm] at hy
    filter_upwards [hnb] with y hy
    have h1 : ‖y - zz‖ < δ := lt_of_lt_of_le hy (min_le_left _ _)
    have h2 : ‖y - zz‖ < ε / (1 + ‖Bq‖ / 2) := lt_of_lt_of_le hy (min_le_right _ _)
    have h3 := hb y h1
    have h4 : |(Bq (y - zz) (y - zz) : ℝ)| ≤ ‖Bq‖ * ‖y - zz‖ * ‖y - zz‖ := by
      have ha := (Bq (y - zz)).le_opNorm (y - zz)
      have hbb := Bq.le_opNorm (y - zz)
      rw [Real.norm_eq_abs] at ha
      calc |(Bq (y - zz) (y - zz) : ℝ)| ≤ ‖Bq (y - zz)‖ * ‖y - zz‖ := ha
        _ ≤ ‖Bq‖ * ‖y - zz‖ * ‖y - zz‖ :=
            mul_le_mul_of_nonneg_right hbb (norm_nonneg _)
    have hcN : (1 + ‖Bq‖ / 2) * ‖y - zz‖ ≤ ε := by
      have h5 : (1 + ‖Bq‖ / 2) * ‖y - zz‖
          ≤ (1 + ‖Bq‖ / 2) * (ε / (1 + ‖Bq‖ / 2)) :=
        mul_le_mul_of_nonneg_left h2.le hc1.le
      rw [mul_div_cancel₀ _ (ne_of_gt hc1)] at h5
      exact h5
    have h6 : |w y - w zz - D (y - zz)|
        ≤ |w y - w zz - D (y - zz) - 1 / 2 * (Bq (y - zz) (y - zz) : ℝ)|
          + |1 / 2 * (Bq (y - zz) (y - zz) : ℝ)| := by
      have h8 := abs_add_le (w y - w zz - D (y - zz) - 1 / 2 * (Bq (y - zz) (y - zz) : ℝ))
        (1 / 2 * (Bq (y - zz) (y - zz) : ℝ))
      rwa [show w y - w zz - D (y - zz) - 1 / 2 * (Bq (y - zz) (y - zz) : ℝ)
          + 1 / 2 * (Bq (y - zz) (y - zz) : ℝ) = w y - w zz - D (y - zz) from by ring] at h8
    have h7 : |1 / 2 * (Bq (y - zz) (y - zz) : ℝ)|
        = 1 / 2 * |(Bq (y - zz) (y - zz) : ℝ)| := by
      rw [abs_mul]
      norm_num
    have hsplit : |w y - w zz - D (y - zz)| ≤ (1 + ‖Bq‖ / 2) * ‖y - zz‖ ^ 2 := by
      linarith only [h3, h4, h6, h7]
    rw [Real.norm_eq_abs]
    calc |w y - w zz - D (y - zz)| ≤ (1 + ‖Bq‖ / 2) * ‖y - zz‖ ^ 2 := hsplit
      _ = (1 + ‖Bq‖ / 2) * ‖y - zz‖ * ‖y - zz‖ := by ring
      _ ≤ ε * ‖y - zz‖ := mul_le_mul_of_nonneg_right hcN (norm_nonneg _)
  -- so `ũ` is Fréchet differentiable at `z_k` with derivative `D_k`
  have hutildeFD : ∀ k, HasFDerivAt (fun y => psi lam (u y)) (Dk k) (zseq k) :=
    fun k => jetFDeriv _ (zseq k) (Dk k) (Bk k) (hjetu k)
  -- (3b), display (9): `z_k` is a local maximum of `ũ - (ṽ - ⟪p_k, ·⟫)` and both
  -- functions have second-order jets there, so `LocalMaxSecondOrder` applies.
  have h9 : ∀ k, Dk k = Dtk k - innerSL ℝ (pseq k) ∧
      (∀ h : EuclideanSpace ℝ (Fin G.n), Bk k h h ≤ Btk k h h) ∧
      hgrad G.sig (zseq k) (Dk k)
        = hgrad G.sig (zseq k) (Dtk k - innerSL ℝ (pseq k)) ∧
      MatLe (hhessS G.sig (zseq k) (Dk k) (Bk k))
        (hhessS G.sig (zseq k) (Dtk k - innerSL ℝ (pseq k)) (Btk k)) := by
    intro k
    refine LocalMaxSecondOrder G.sig (fun y => psi lam (u y))
      (fun y => v₁ y + Pf mu xl y - ∑ i, pseq k i * y i) (zseq k) (Dk k)
      (Dtk k - innerSL ℝ (pseq k)) (Bk k) (Btk k) (hjetu k) (hjetvp k) ?_
    have hfe : (fun y => psi lam (u y) - (v₁ y + Pf mu xl y - ∑ i, pseq k i * y i))
        = (fun y => psi lam (u y) - (v₁ y + Pf mu xl y) + ∑ i, pseq k i * y i) :=
      funext fun y => by ring
    rw [hfe]
    exact hzkmax k
  -- the three consequences of (9), named after the `.tex` displays
  have h9b : ∀ k, hgrad G.sig (zseq k) (Dk k)
      = hgrad G.sig (zseq k) (Dtk k - innerSL ℝ (pseq k)) := fun k => (h9 k).2.2.1
  have h9c : ∀ k, MatLe (hhessS G.sig (zseq k) (Dk k) (Bk k))
      (hhessS G.sig (zseq k) (Dtk k - innerSL ℝ (pseq k)) (Btk k)) :=
    fun k => (h9 k).2.2.2
  -- `hgrad` is linear in the 1-jet: its `i`-th component is `D ↦ D (σⁱ(x))`
  have hgradAdd : ∀ (y : EuclideanSpace ℝ (Fin G.n))
      (D D' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      hgrad G.sig y (D + D') = hgrad G.sig y D + hgrad G.sig y D' := by
    intro y D D'
    ext i
    simp [hgradeq]
  -- display (10): `𝔛ũ(z_k) = ξ_k + η_k` with `ξ_k := 𝔛v₁(z_k)`
  set xik : ℕ → EuclideanSpace ℝ (Fin G.m) :=
    fun k => hgrad G.sig (zseq k) (Dtk k - DPf mu xl (zseq k)) with hxikdef
  set etak : ℕ → EuclideanSpace ℝ (Fin G.m) :=
    fun k => hgrad G.sig (zseq k) (DPf mu xl (zseq k) - innerSL ℝ (pseq k)) with hetakdef
  have h10 : ∀ k, hgrad G.sig (zseq k) (Dk k) = xik k + etak k := by
    intro k
    have he : Dtk k - innerSL ℝ (pseq k)
        = (Dtk k - DPf mu xl (zseq k))
          + (DPf mu xl (zseq k) - innerSL ℝ (pseq k)) := by abel
    rw [h9b k, he, hgradAdd, hxikdef, hetakdef]
  -- the two norm bounds that (12) runs on: `|DP(z_k) - p_k| ≤ (4μρ² + 1)δ_k` and
  -- `‖D²P(z_k)‖_op ≤ 12μρ δ_k`, for all `k` with `z_k ∈ B(x₁, ρ)`.
  have hDPfpk : ∀ᶠ k in Filter.atTop,
      ‖DPf mu xl (zseq k) - innerSL ℝ (pseq k)‖ ≤ (4 * mu * rho ^ 2 + 1) * del k := by
    filter_upwards [hzev] with k hk
    have hzr : ‖zseq k - xl‖ ≤ rho := by
      have h := Metric.mem_ball.1 hk
      rw [dist_eq_norm] at h
      exact h.le
    have hzd : ‖zseq k - xl‖ ≤ del k := hznorm k
    have hz0 : (0:ℝ) ≤ ‖zseq k - xl‖ := norm_nonneg _
    have hsq : ‖zseq k - xl‖ ^ 2 ≤ rho ^ 2 := by
      have h := mul_self_le_mul_self hz0 hzr
      linarith only [h]
    have hcube : ‖zseq k - xl‖ ^ 3 ≤ rho ^ 2 * del k := by
      calc ‖zseq k - xl‖ ^ 3 = ‖zseq k - xl‖ ^ 2 * ‖zseq k - xl‖ := by ring
        _ ≤ rho ^ 2 * del k := mul_le_mul hsq hzd hz0 (by positivity)
    have h1 : ‖DPf mu xl (zseq k)‖ ≤ 4 * mu * (rho ^ 2 * del k) := by
      refine (hDPfbound mu hmunn xl (zseq k)).trans ?_
      have h := mul_le_mul_of_nonneg_left hcube (by linarith only [hmunn] : (0:ℝ) ≤ 4 * mu)
      linarith only [h]
    have h2 : ‖innerSL ℝ (pseq k)‖ ≤ del k := by
      rw [innerSL_apply_norm]
      exact hpnorm k
    calc ‖DPf mu xl (zseq k) - innerSL ℝ (pseq k)‖
        ≤ ‖DPf mu xl (zseq k)‖ + ‖innerSL ℝ (pseq k)‖ := norm_sub_le _ _
      _ ≤ 4 * mu * (rho ^ 2 * del k) + del k := by linarith only [h1, h2]
      _ = (4 * mu * rho ^ 2 + 1) * del k := by ring
  have hD2Pfk : ∀ᶠ k in Filter.atTop,
      ‖D2Pf mu xl (zseq k)‖ ≤ 12 * mu * rho * del k := by
    filter_upwards [hzev] with k hk
    have hzr : ‖zseq k - xl‖ ≤ rho := by
      have h := Metric.mem_ball.1 hk
      rw [dist_eq_norm] at h
      exact h.le
    have hzd : ‖zseq k - xl‖ ≤ del k := hznorm k
    have hz0 : (0:ℝ) ≤ ‖zseq k - xl‖ := norm_nonneg _
    have hsq : ‖zseq k - xl‖ ^ 2 ≤ rho * del k := by
      have h := mul_le_mul hzr hzd hz0 (le_trans hz0 hzr)
      linarith only [h]
    refine (hD2Pfbound mu hmunn xl (zseq k)).trans ?_
    have h := mul_le_mul_of_nonneg_left hsq (by linarith only [hmunn] : (0:ℝ) ≤ 12 * mu)
    linarith only [h]
  -- (3c′) BACKWARD, with no use of `ψ_λ⁻¹`: wherever `ũ = ψ_λ ∘ u` has a second-order jet
  -- `(Dⱼ, Bⱼ)`, `u` has the second-order jet `(t⁻¹ Dⱼ, t⁻¹(Bⱼ - c Dᵘ ⊗ Dᵘ))` with
  -- `t = ψ_λ′(u z)` and `c = ψ_λ″(u z)`.  This is `ExpRelabellingJetDescent`, together
  -- with the cubic Taylor bound for `ψ_λ` that its proof runs on.
  -- `t_k = ψ_λ'(u(z_k)) ≥ 1` and `c_k = ψ_λ''(u(z_k)) > 0`
  obtain ⟨tk, htkdef⟩ : ∃ tk : ℕ → ℝ, ∀ k, tk k = 1 + lam * Real.exp (u (zseq k)) :=
    ⟨fun k => 1 + lam * Real.exp (u (zseq k)), fun _ => rfl⟩
  obtain ⟨ck, hckdef⟩ : ∃ ck : ℕ → ℝ, ∀ k, ck k = lam * Real.exp (u (zseq k)) :=
    ⟨fun k => lam * Real.exp (u (zseq k)), fun _ => rfl⟩
  have hck0 : ∀ k, 0 < ck k := fun k => by rw [hckdef]; positivity
  have htk1 : ∀ k, 1 ≤ tk k := fun k => by
    rw [htkdef, ← hckdef]
    linarith only [hck0 k]
  have htkpos : ∀ k, 0 < tk k := fun k => by linarith only [htk1 k]
  have htkne : ∀ k, tk k ≠ 0 := fun k => ne_of_gt (htkpos k)
  have htkderiv : ∀ k, deriv (psi lam) (u (zseq k)) = tk k := fun k => by
    rw [htkdef]
    exact (ExpRelabelling lam M hlam0).2.1 (u (zseq k))
  have htkderiv2 : ∀ k, deriv (deriv (psi lam)) (u (zseq k)) = ck k := fun k => by
    rw [hckdef]
    exact (ExpRelabelling lam M hlam0).2.2.2.1 (u (zseq k))
  -- the jet of `u` at `z_k` produced by (3c′) Backward
  obtain ⟨Duk, hDukdef⟩ : ∃ Duk : ℕ → (EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      ∀ k, Duk k = (tk k)⁻¹ • Dk k :=
    ⟨fun k => (tk k)⁻¹ • Dk k, fun _ => rfl⟩
  have hDukapp : ∀ k h, Duk k h = (tk k)⁻¹ * Dk k h := by
    intro k h
    rw [hDukdef]
    simp
  obtain ⟨Buk, hBukdef⟩ : ∃ Buk : ℕ → (EuclideanSpace ℝ (Fin G.n) →L[ℝ]
        EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      ∀ k, Buk k = (tk k)⁻¹ • (Bk k - ck k • (Duk k).smulRight (Duk k)) :=
    ⟨fun k => (tk k)⁻¹ • (Bk k - ck k • (Duk k).smulRight (Duk k)), fun _ => rfl⟩
  have hBukapp : ∀ k h h', Buk k h h'
      = (tk k)⁻¹ * (Bk k h h' - ck k * (Duk k h * Duk k h')) := by
    intro k h h'
    rw [hBukdef]
    simp
  have hBuksymm : ∀ k a b, Buk k a b = Buk k b a := by
    intro k a b
    rw [hBukapp, hBukapp, (hjetu k).1 a b]
    ring
  -- the jet hypothesis of `ExpRelabellingJetDescent` is stated on the explicit
  -- relabelling `y ↦ u y + λ e^{u y}`, which is `ψ_λ ∘ u` unfolded
  have hjetuexp : ∀ k, TwiceDiffAt (fun y => u y + lam * Real.exp (u y))
      (zseq k) (Dk k) (Bk k) := by
    intro k
    have hfe : (fun y => u y + lam * Real.exp (u y)) = fun y => psi lam (u y) := by
      funext y
      simp only [hpsidef]
    rw [hfe]
    exact hjetu k
  have hjetu1 : ∀ k, TwiceDiffAt u (zseq k) (Duk k) (Buk k) := fun k =>
    ExpRelabellingJetDescent lam hlam0 u (zseq k) (tk k) (ck k) (Dk k) (Bk k)
      (Duk k) (Buk k) (htkdef k) (hckdef k) (hDukapp k) (hBukapp k) (hBuksymm k)
      (hjetuexp k)
  have huFD : ∀ k, HasFDerivAt u (Duk k) (zseq k) := fun k =>
    jetFDeriv u (zseq k) (Duk k) (Buk k) (hjetu1 k)
  -- the identification of `(D_k, B_k)` from (3c′) Forward.  Because `(Dᵘ_k, Bᵘ_k)` was
  -- DEFINED by solving the relabelling equation, the identification is an identity and no
  -- appeal to jet uniqueness (0a) is needed.
  have hDkeq2 : ∀ k, Dk k = tk k • Duk k := by
    intro k
    rw [hDukdef, smul_smul, mul_inv_cancel₀ (htkne k), one_smul]
  have hBkeq2 : ∀ k, tk k • Buk k + ck k • (Duk k).smulRight (Duk k) = Bk k := by
    intro k
    rw [hBukdef, smul_smul, mul_inv_cancel₀ (htkne k), one_smul]
    abel
  have hgradSmul : ∀ (x : EuclideanSpace ℝ (Fin G.n)) (r : ℝ)
      (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      hgrad G.sig x (r • D) = r • hgrad G.sig x D := by
    intro x r D
    ext i
    simp [hgradeq]
  -- (3c), display (13): `‖𝔛u(z_k)‖ ≥ θ/4` eventually, by partial continuity of the
  -- gradient along `z_k → x₁` together with display (4) at `x₁ ∈ E_λ`.
  -- the node states its two hypotheses on the explicit relabelling `y ↦ u y + λ e^{u y}`,
  -- which is `ψ_λ ∘ u` unfolded; `hxlE` splits into `xl ∈ Ω` and the `IsMaxOn` clause
  have hulamscE : LocallySemiConvexOn Ω (fun y => u y + lam * Real.exp (u y)) := by
    have hfe : (fun y => u y + lam * Real.exp (u y)) = fun y => psi lam (u y) := by
      funext y
      simp only [hpsidef]
    rw [hfe]
    exact hulamsc lam hlam0
  have hxlmaxE : IsMaxOn (fun y => (u y + lam * Real.exp (u y)) - v₁ y) Ω xl := by
    have hfe : (fun y => (u y + lam * Real.exp (u y)) - v₁ y)
        = fun y => psi lam (u y) - v₁ y := by
      funext y
      simp only [hpsidef]
    rw [hfe]
    exact hxlE.2
  obtain ⟨Dx1, hDx1⟩ := ExpRelabelledMaxDifferentiability Ω lam hlam0 u v₁
    hulamscE hv₁sc xl hxlE.1 hxlmaxE
  have hDukconv : Filter.Tendsto Duk Filter.atTop (nhds Dx1) :=
    SemiConvexGradPartialCont Ω u (Or.inl husc) xl hxlΩ zseq hzkΩ hztend Dx1 hDx1 Duk huFD
  have hXuconv : Filter.Tendsto (fun k => hgrad G.sig (zseq k) (Duk k)) Filter.atTop
      (nhds (hgrad G.sig xl Dx1)) :=
    HgradTendstoOfTendsto G.sig hsigc zseq xl Duk Dx1 hztend hDukconv
  have hX1theta : θ / 2 ≤ ‖hgrad G.sig xl Dx1‖ := h4 xl hxlE Dx1 hDx1
  have h13 : ∀ᶠ k in Filter.atTop, θ / 4 < ‖hgrad G.sig (zseq k) (Duk k)‖ :=
    hXuconv.norm.eventually
      (eventually_gt_nhds (by linarith only [hX1theta, hθpos]))
  -- display (14): `‖𝔛ũ(z_k)‖ = t_k ‖𝔛u(z_k)‖ ≥ θ/4`, since `t_k ≥ 1`
  have h14 : ∀ᶠ k in Filter.atTop, θ / 4 < ‖hgrad G.sig (zseq k) (Dk k)‖ := by
    filter_upwards [h13] with k hk
    rw [hDkeq2 k, hgradSmul, norm_smul, Real.norm_eq_abs, abs_of_pos (htkpos k)]
    have h1 : 1 * ‖hgrad G.sig (zseq k) (Duk k)‖
        ≤ tk k * ‖hgrad G.sig (zseq k) (Duk k)‖ :=
      mul_le_mul_of_nonneg_right (htk1 k) (norm_nonneg _)
    linarith only [hk, h1]
  -- (3d) for `u`, display (16) left half: the sub-solution inequality holds classically
  have h16u : ∀ᶠ k in Filter.atTop, Lop G.sig A H (zseq k) (Duk k) (Buk k) ≤ 0 := by
    filter_upwards [h13] with k hk
    refine (ClassicalAtTwiceDiff G A H Ω hΩo hΩb u hucont (zseq k) (hzkΩ k)
      (Duk k) (Buk k) (hjetu1 k) ?_).1 hsub
    intro hz
    rw [hz, norm_zero] at hk
    linarith only [hk, hθpos]
  -- (3e), display (17) = eq:gamsoln: `ℒũ(z_k) ≤ -γ` with `γ = λ' e₀ (θ/4)²`
  have h17 : ∀ᶠ k in Filter.atTop, Lop G.sig A H (zseq k) (Dk k) (Bk k) ≤ -gam := by
    filter_upwards [h13, h16u] with k hk hsubk
    have hMz : |u (zseq k)| ≤ M := hMb (zseq k) (subset_closure (hzkΩ k))
    have hcbound : lamp ≤ deriv (deriv (psi lam)) (u (zseq k)) := by
      rw [hlampdef]
      exact (ExpRelabelling lam M hlam0).2.2.2.2.2.2.1 (u (zseq k)) hMz
    have h := (StrictSubsolutionPerturbation G.sig A H hN e₀ he₀pos he₀ (psi lam)
      (hpsiC2 lam hlam0) u (zseq k) (Duk k) (Buk k) (hjetu1 k) (θ / 4)
      (by linarith only [hθpos]) (le_of_lt hk) lamp hlamppos
      (by rw [htkderiv k]; exact htkpos k) hcbound hsubk).2
    rw [htkderiv k, htkderiv2 k, hBkeq2 k, ← hDkeq2 k] at h
    rw [hgamdef]
    exact h
  have hgradZero : ∀ x : EuclideanSpace ℝ (Fin G.n), hgrad G.sig x 0 = 0 := by
    intro x
    ext i
    simp [hgradeq]
  -- display (12) for `η_k`, in the eventual form the rest of the proof uses: `η_k → 0`.
  -- (Departure from the `.tex`: the quantitative constant `c = c(𝔾, K, μ)` is never used
  -- as a number -- (15) only needs `c δ_k ≤ θ/8` for large `k` -- so we carry `η_k → 0`,
  -- which follows from the operator-norm bound of (12) and `δ_k → 0` without the `σ`,
  -- `Dσ` sup bounds on `K`.)
  have hetatend : Filter.Tendsto etak Filter.atTop (nhds 0) := by
    have hdeltendc : Filter.Tendsto (fun k => (4 * mu * rho ^ 2 + 1) * del k)
        Filter.atTop (nhds 0) := by
      simpa using hdeltend.const_mul (4 * mu * rho ^ 2 + 1)
    have hD0 : Filter.Tendsto (fun k => DPf mu xl (zseq k) - innerSL ℝ (pseq k))
        Filter.atTop (nhds 0) := squeeze_zero_norm' hDPfpk hdeltendc
    have h := HgradTendstoOfTendsto G.sig hsigc zseq xl
      (fun k => DPf mu xl (zseq k) - innerSL ℝ (pseq k)) 0 hztend hD0
    rw [hgradZero] at h
    simpa only [hetakdef] using h
  -- display (15): `‖ξ_k‖ ≥ θ/8` eventually, from (10), (14) and `η_k → 0`
  have h15 : ∀ᶠ k in Filter.atTop, θ / 8 < ‖xik k‖ := by
    have hn0 : Filter.Tendsto (fun k => ‖etak k‖) Filter.atTop (nhds 0) := by
      simpa using hetatend.norm
    have hev : ∀ᶠ k in Filter.atTop, ‖etak k‖ < θ / 8 :=
      hn0.eventually (eventually_lt_nhds (by linarith only [hθpos]))
    filter_upwards [h14, hev] with k hk hk2
    have h1 : ‖hgrad G.sig (zseq k) (Dk k)‖ ≤ ‖xik k‖ + ‖etak k‖ := by
      rw [h10 k]
      exact norm_add_le _ _
    linarith only [hk, hk2, h1]
  -- (3d) for `v₁`, display (16) right half: the super-solution inequality holds
  -- classically at `z_k`, the non-vanishing side condition being (15)
  have h16v : ∀ᶠ k in Filter.atTop,
      0 ≤ Lop G.sig A H (zseq k) (Dtk k - DPf mu xl (zseq k))
            (Btk k - D2Pf mu xl (zseq k)) := by
    filter_upwards [h15] with k hk
    refine (ClassicalAtTwiceDiff G A H Ω hΩo hΩb v₁ hv₁cont (zseq k) (hzkΩ k)
      (Dtk k - DPf mu xl (zseq k)) (Btk k - D2Pf mu xl (zseq k)) (hjetv1 k) ?_).2 hv₁sup
    simp only [hxikdef] at hk
    intro hz
    rw [hz, norm_zero] at hk
    linarith only [hk, hθpos]
  -- `hhessS` is additive in the pair `(D, B)`, by `hhessS`/`Mfield`
  have hhessSAdd : ∀ (x : EuclideanSpace ℝ (Fin G.n))
      (D D' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (B B' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      hhessS G.sig x (D + D') (B + B')
        = hhessS G.sig x D B + hhessS G.sig x D' B' := by
    intro x D D' B B'
    ext i j
    simp only [hhessS, Mfield, Matrix.add_apply, Matrix.of_apply,
      add_apply]
    ring
  -- display (11) = eq:klam, with
  -- `N_k = σ(z_k)ᵗ D²P(z_k) σ(z_k) + 𝓜(z_k, DP(z_k) - p_k) = hhessS σ z_k (DP - p) (D²P)`
  set Nk : ℕ → Matrix (Fin G.m) (Fin G.m) ℝ :=
    fun k => hhessS G.sig (zseq k) (DPf mu xl (zseq k) - innerSL ℝ (pseq k))
      (D2Pf mu xl (zseq k)) with hNkdef
  have h11 : ∀ k, MatLe (hhessS G.sig (zseq k) (Dk k) (Bk k))
      (hhessS G.sig (zseq k) (Dtk k - DPf mu xl (zseq k))
          (Btk k - D2Pf mu xl (zseq k)) + Nk k) := by
    intro k
    have hD : Dtk k - innerSL ℝ (pseq k)
        = (Dtk k - DPf mu xl (zseq k)) + (DPf mu xl (zseq k) - innerSL ℝ (pseq k)) := by
      abel
    have hB : Btk k = (Btk k - D2Pf mu xl (zseq k)) + D2Pf mu xl (zseq k) := by abel
    have h := h9c k
    rw [hD, hB, hhessSAdd] at h
    simp only [hNkdef]
    exact h
  -- Step 4.  The jet-Hessian sign from convexity -- that convexity of `w + Λ/2|·|²` on a
  -- ball forces `B(h,h) ≥ -Λ|h|²` for any second-order jet `(D,B)` of `w` at an interior
  -- point -- is `JetHessianLowerBoundOfConvex`, used at `hBksign`/`hBvksign` below.
  have hBopBound : ∀ (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ]
        EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ) (a b : EuclideanSpace ℝ (Fin G.n)),
      |B a b| ≤ ‖B‖ * ‖a‖ * ‖b‖ := by
    intro B a b
    have ha := (B a).le_opNorm b
    have hbb := B.le_opNorm a
    rw [Real.norm_eq_abs] at ha
    exact ha.trans (mul_le_mul_of_nonneg_right hbb (norm_nonneg _))
  -- `c₁`: a single bound for `|σⁱ|` and `‖Dσⁱ‖` on the compact `K = closedBall x₁ ρ ⊆ Ω`,
  -- obtained from one continuous function so that no finite maximum over `i` is needed.
  obtain ⟨c1, hc1nn, hc1sig, hc1Dsig⟩ : ∃ c1 : ℝ, 0 ≤ c1 ∧
      (∀ x ∈ Metric.closedBall xl rho, ∀ i, ‖G.sig x i‖ ≤ c1) ∧
      (∀ x ∈ Metric.closedBall xl rho, ∀ i,
        ‖fderiv ℝ (fun y => G.sig y i) x‖ ≤ c1) := by
    have hFcont : Continuous (fun x => ∑ i : Fin G.m,
        (‖G.sig x i‖ + ‖fderiv ℝ (fun y => G.sig y i) x‖)) := by
      refine continuous_finsetSum _ fun i _ => ?_
      exact ((hsigc i).norm).add
        (((G.sig_smooth i).continuous_fderiv (by norm_num)).norm)
    obtain ⟨Mb, hMb2⟩ := hKcpt.bddAbove_image hFcont.continuousOn
    refine ⟨max Mb 0, le_max_right _ _, ?_, ?_⟩ <;> intro x hx i
    all_goals
      have hle : (∑ j : Fin G.m, (‖G.sig x j‖ + ‖fderiv ℝ (fun y => G.sig y j) x‖)) ≤ Mb :=
        hMb2 (Set.mem_image_of_mem _ hx)
    all_goals
      have hsing : ‖G.sig x i‖ + ‖fderiv ℝ (fun y => G.sig y i) x‖
          ≤ ∑ j : Fin G.m, (‖G.sig x j‖ + ‖fderiv ℝ (fun y => G.sig y j) x‖) :=
        Finset.single_le_sum (f := fun j : Fin G.m =>
          ‖G.sig x j‖ + ‖fderiv ℝ (fun y => G.sig y j) x‖)
          (fun j _ => by positivity) (Finset.mem_univ i)
    all_goals
      exact by
        have h1 : (0:ℝ) ≤ ‖G.sig x i‖ := norm_nonneg _
        have h2 : (0:ℝ) ≤ ‖fderiv ℝ (fun y => G.sig y i) x‖ := norm_nonneg _
        have h3 : Mb ≤ max Mb 0 := le_max_left _ _
        linarith only [hle, hsing, h1, h2, h3]
  -- `C_K`: clause (4) of `SemiConvexLocLipschitz` for `ũ` on `K`
  obtain ⟨CK, hCKnn, hCKb⟩ := (SemiConvexLocLipschitz Ω (fun y => psi lam (u y))
    (hulamsc lam hlam0)).2.2.2 (Metric.closedBall xl rho) hKsub hKcpt
  -- `Λ'` for `ũ` and `Λ''` for `-v₁`, from `LocallySemiConvexOn` at `x₁`
  obtain ⟨rhou, hrhou, Lam1, hLam1, hballu, hconvu⟩ := hulamsc lam hlam0 xl hxlΩ
  obtain ⟨rhov, hrhov, Lam2, hLam2, hballv, hconvv⟩ := hv₁sc xl hxlΩ
  have hzevu : ∀ᶠ k in Filter.atTop, zseq k ∈ Metric.ball xl rhou :=
    hztend.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrhou))
  have hzevv : ∀ᶠ k in Filter.atTop, zseq k ∈ Metric.ball xl rhov :=
    hztend.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrhov))
  -- the two jet-Hessian signs.  (Departure from the `.tex`: no common radius `ρ₁` is
  -- formed -- each convexity statement is used on its own ball, with `z_k` in it
  -- eventually, which is all the argument needs.)
  have hBksign : ∀ᶠ k in Filter.atTop, ∀ h : EuclideanSpace ℝ (Fin G.n),
      -(Lam1 * ‖h‖ ^ 2) ≤ Bk k h h := by
    filter_upwards [hzevu] with k hk
    exact JetHessianLowerBoundOfConvex (fun y => psi lam (u y)) Lam1 xl rhou hconvu
      (zseq k) hk (Dk k) (Bk k) (hjetu k)
  have hBvksign : ∀ᶠ k in Filter.atTop, ∀ h : EuclideanSpace ℝ (Fin G.n),
      (Btk k - D2Pf mu xl (zseq k)) h h ≤ Lam2 * ‖h‖ ^ 2 := by
    filter_upwards [hzevv] with k hk h
    have hjn := jetNeg v₁ (zseq k) (Dtk k - DPf mu xl (zseq k))
      (Btk k - D2Pf mu xl (zseq k)) (hjetv1 k)
    have h1 := JetHessianLowerBoundOfConvex (fun y => -v₁ y) Lam2 xl rhov hconvv
      (zseq k) hk (-(Dtk k - DPf mu xl (zseq k)))
      (-(Btk k - D2Pf mu xl (zseq k))) hjn h
    rw [neg_apply, neg_apply] at h1
    linarith only [h1]
  -- `Λ* := max {Λ', Λ'' + 12μρ²}` and the two-sided bound on the quadratic form of `B_k`
  obtain ⟨Lams, hLamsnn, hLams1, hLams2⟩ : ∃ Lams : ℝ, 0 ≤ Lams ∧ Lam1 ≤ Lams
      ∧ Lam2 + 12 * mu * rho ^ 2 ≤ Lams :=
    ⟨max Lam1 (Lam2 + 12 * mu * rho ^ 2), le_trans hLam1 (le_max_left _ _),
      le_max_left _ _, le_max_right _ _⟩
  have hBkabs : ∀ᶠ k in Filter.atTop, ∀ h : EuclideanSpace ℝ (Fin G.n),
      |Bk k h h| ≤ Lams * ‖h‖ ^ 2 := by
    filter_upwards [hBksign, hBvksign, hzev] with k hk1 hk2 hk3 h
    have hzr : ‖zseq k - xl‖ ≤ rho := by
      have hh := Metric.mem_ball.1 hk3
      rw [dist_eq_norm] at hh
      exact hh.le
    have hD2n : ‖D2Pf mu xl (zseq k)‖ ≤ 12 * mu * rho ^ 2 := by
      refine (hD2Pfbound mu hmunn xl (zseq k)).trans ?_
      have hsq : ‖zseq k - xl‖ ^ 2 ≤ rho ^ 2 := by
        have hx := mul_self_le_mul_self (norm_nonneg (zseq k - xl)) hzr
        linarith only [hx]
      have hx := mul_le_mul_of_nonneg_left hsq
        (by linarith only [hmunn] : (0:ℝ) ≤ 12 * mu)
      linarith only [hx]
    have hD2 : |D2Pf mu xl (zseq k) h h| ≤ 12 * mu * rho ^ 2 * ‖h‖ ^ 2 := by
      refine (hBopBound _ h h).trans ?_
      have hx := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hD2n (norm_nonneg h)) (norm_nonneg h)
      calc ‖D2Pf mu xl (zseq k)‖ * ‖h‖ * ‖h‖
          ≤ 12 * mu * rho ^ 2 * ‖h‖ * ‖h‖ := hx
        _ = 12 * mu * rho ^ 2 * ‖h‖ ^ 2 := by ring
    have hup : Bk k h h ≤ Btk k h h := (h9 k).2.1 h
    have hsplit : Btk k h h = (Btk k - D2Pf mu xl (zseq k)) h h
        + D2Pf mu xl (zseq k) h h := by
      rw [sub_apply, sub_apply]
      ring
    have hL1 := mul_le_mul_of_nonneg_right hLams1 (sq_nonneg ‖h‖)
    have hL2 := mul_le_mul_of_nonneg_right hLams2 (sq_nonneg ‖h‖)
    have hD2le := (abs_le.1 hD2).2
    rw [abs_le]
    exact ⟨by linarith only [hk1 h, hL1], by
      linarith only [hup, hsplit, hk2 h, hD2le, hL2]⟩
  -- polarization: a symmetric form with `|B(a,a)| ≤ Λ|a|²` satisfies
  -- `|B(a,b)| ≤ Λ(|a|² + |b|²)/2`, which is all that (18b) needs
  have hBquadToBilin : ∀ (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ]
        EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ) (Lam : ℝ),
      (∀ a b, B a b = B b a) →
      (∀ a, |B a a| ≤ Lam * ‖a‖ ^ 2) →
      ∀ a b, |B a b| ≤ Lam * (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
    intro B Lam hsymm hbd a b
    have hpol : 4 * B a b = B (a + b) (a + b) - B (a - b) (a - b) := by
      simp only [map_add, map_sub, add_apply,
        sub_apply]
      rw [hsymm b a]
      ring
    have hpar : ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      rw [norm_add_sq_real, norm_sub_sq_real]
      ring
    have h3 : |4 * B a b| = 4 * |B a b| := by
      rw [abs_mul]
      norm_num
    rw [hpol] at h3
    have h4 : |B (a + b) (a + b) - B (a - b) (a - b)|
        ≤ |B (a + b) (a + b)| + |B (a - b) (a - b)| := by
      calc |B (a + b) (a + b) - B (a - b) (a - b)|
          = |B (a + b) (a + b) + -(B (a - b) (a - b))| := by
            rw [← sub_eq_add_neg]
        _ ≤ |B (a + b) (a + b)| + |-(B (a - b) (a - b))| := abs_add_le _ _
        _ = |B (a + b) (a + b)| + |B (a - b) (a - b)| := by rw [abs_neg]
    have h5 : Lam * ‖a + b‖ ^ 2 + Lam * ‖a - b‖ ^ 2
        = Lam * (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) := by
      rw [← mul_add, hpar]
    linarith only [h3, h4, hbd (a + b), hbd (a - b), h5]
  -- display (18b)
  have h18b : ∀ᶠ k in Filter.atTop, ∀ i j,
      |Bk k (G.sig (zseq k) i) (G.sig (zseq k) j)| ≤ Lams * c1 ^ 2 := by
    filter_upwards [hBkabs, hzev] with k hk hk3 i j
    have hmem : zseq k ∈ Metric.closedBall xl rho := Metric.ball_subset_closedBall hk3
    have hi := hc1sig (zseq k) hmem i
    have hj := hc1sig (zseq k) hmem j
    have hpol := hBquadToBilin (Bk k) Lams (hjetu k).1 hk
      (G.sig (zseq k) i) (G.sig (zseq k) j)
    have hisq : ‖G.sig (zseq k) i‖ ^ 2 ≤ c1 ^ 2 := by
      have hx := mul_self_le_mul_self (norm_nonneg (G.sig (zseq k) i)) hi
      linarith only [hx]
    have hjsq : ‖G.sig (zseq k) j‖ ^ 2 ≤ c1 ^ 2 := by
      have hx := mul_self_le_mul_self (norm_nonneg (G.sig (zseq k) j)) hj
      linarith only [hx]
    have hx := mul_le_mul_of_nonneg_left
      (by linarith only [hisq, hjsq] :
        ‖G.sig (zseq k) i‖ ^ 2 + ‖G.sig (zseq k) j‖ ^ 2 ≤ 2 * c1 ^ 2) hLamsnn
    linarith only [hpol, hx]
  -- display (18c): the entries of the correction matrix `𝓜(z_k, D_k)`
  have h18c : ∀ᶠ k in Filter.atTop, ∀ i j,
      |Mfield G.sig (zseq k) (Dk k) i j| ≤ CK * (c1 * c1) := by
    filter_upwards [hzev] with k hk i j
    have hmem : zseq k ∈ Metric.closedBall xl rho := Metric.ball_subset_closedBall hk
    have hDkb : ‖Dk k‖ ≤ CK := hCKb (zseq k) hmem (Dk k) (hutildeFD k)
    have hterm : ∀ i' j' : Fin G.m,
        |Dk k (fderiv ℝ (fun y => G.sig y j') (zseq k) (G.sig (zseq k) i'))|
          ≤ CK * (c1 * c1) := by
      intro i' j'
      have h1 : |Dk k (fderiv ℝ (fun y => G.sig y j') (zseq k) (G.sig (zseq k) i'))|
          ≤ ‖Dk k‖ * ‖fderiv ℝ (fun y => G.sig y j') (zseq k) (G.sig (zseq k) i')‖ := by
        simpa [Real.norm_eq_abs] using (Dk k).le_opNorm
          (fderiv ℝ (fun y => G.sig y j') (zseq k) (G.sig (zseq k) i'))
      have h2 : ‖fderiv ℝ (fun y => G.sig y j') (zseq k) (G.sig (zseq k) i')‖
          ≤ ‖fderiv ℝ (fun y => G.sig y j') (zseq k)‖ * ‖G.sig (zseq k) i'‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have h3 : ‖fderiv ℝ (fun y => G.sig y j') (zseq k)‖ * ‖G.sig (zseq k) i'‖
          ≤ c1 * c1 :=
        mul_le_mul (hc1Dsig (zseq k) hmem j') (hc1sig (zseq k) hmem i')
          (norm_nonneg _) hc1nn
      calc |Dk k (fderiv ℝ (fun y => G.sig y j') (zseq k) (G.sig (zseq k) i'))|
          ≤ ‖Dk k‖ * ‖fderiv ℝ (fun y => G.sig y j') (zseq k) (G.sig (zseq k) i')‖ := h1
        _ ≤ ‖Dk k‖ * (c1 * c1) :=
            mul_le_mul_of_nonneg_left (h2.trans h3) (norm_nonneg _)
        _ ≤ CK * (c1 * c1) :=
            mul_le_mul_of_nonneg_right hDkb (mul_nonneg hc1nn hc1nn)
    have hent : Mfield G.sig (zseq k) (Dk k) i j
        = 1 / 2 * (Dk k (fderiv ℝ (fun y => G.sig y j) (zseq k) (G.sig (zseq k) i))
          + Dk k (fderiv ℝ (fun y => G.sig y i) (zseq k) (G.sig (zseq k) j))) := by
      simp only [Mfield, Matrix.of_apply]
    rw [hent, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    have hab := abs_add_le
      (Dk k (fderiv ℝ (fun y => G.sig y j) (zseq k) (G.sig (zseq k) i)))
      (Dk k (fderiv ℝ (fun y => G.sig y i) (zseq k) (G.sig (zseq k) j)))
    linarith only [hab, hterm i j, hterm j i]
  -- display (18): the entries of `𝔛𝔛ˢũ(z_k)` are bounded independently of `k`.
  -- (Departure from the `.tex`: an ENTRYWISE bound rather than a Frobenius-norm bound.
  -- Mathlib carries the Frobenius norm only as scoped instances, and the trace estimate
  -- of (4c) is done entrywise below, so no matrix norm is introduced at all.)
  obtain ⟨Cbig, hCbignn, hCbigb⟩ : ∃ C : ℝ, 0 ≤ C ∧ Lams * c1 ^ 2 + CK * (c1 * c1) ≤ C :=
    ⟨Lams * c1 ^ 2 + CK * (c1 * c1),
      by
        have h1 : (0:ℝ) ≤ Lams * c1 ^ 2 := mul_nonneg hLamsnn (sq_nonneg c1)
        have h2 : (0:ℝ) ≤ CK * (c1 * c1) := mul_nonneg hCKnn (mul_nonneg hc1nn hc1nn)
        linarith only [h1, h2],
      le_rfl⟩
  have h18 : ∀ᶠ k in Filter.atTop, ∀ i j,
      |hhessS G.sig (zseq k) (Dk k) (Bk k) i j| ≤ Cbig := by
    filter_upwards [h18b, h18c] with k hk1 hk2 i j
    have hent : hhessS G.sig (zseq k) (Dk k) (Bk k) i j
        = Bk k (G.sig (zseq k) i) (G.sig (zseq k) j)
          + Mfield G.sig (zseq k) (Dk k) i j := by
      simp only [hhessS, Matrix.add_apply, Matrix.of_apply]
    rw [hent]
    have hab := abs_add_le (Bk k (G.sig (zseq k) i) (G.sig (zseq k) j))
      (Mfield G.sig (zseq k) (Dk k) i j)
    linarith only [hab, hk1 i j, hk2 i j, hCbigb]
  -- the entrywise trace estimate, replacing the `.tex`'s Frobenius Cauchy-Schwarz
  -- `|Tr(XY)| ≤ |X| |Y|`.  (Departure: Mathlib carries the Frobenius norm only as scoped
  -- instances and has no named Cauchy-Schwarz for the trace; every constant in display
  -- (26) only has to be `k`-independent, so the crude entrywise bound is enough.  The
  -- `.tex`'s operator-norm convention for the `n × n` Hessians is untouched -- that is
  -- where (4a) and the `X ≤ ‖X‖_op I` ordering genuinely need it.)
  have trAbs : ∀ (X Y : Matrix (Fin G.m) (Fin G.m) ℝ) (b : ℝ),
      (∀ i j, |Y i j| ≤ b) → |(X * Y).trace| ≤ (∑ i, ∑ j, |X i j|) * b := by
    intro X Y b hY
    have hexp : (X * Y).trace = ∑ i, ∑ j, X i j * Y j i := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [hexp]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hY j i) (abs_nonneg _)
  -- the `𝓜` entry bound in general form, and the symmetry of `hhessS`
  have hMfieldent : ∀ (x : EuclideanSpace ℝ (Fin G.n))
      (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      x ∈ Metric.closedBall xl rho → ∀ i j,
      |Mfield G.sig x D i j| ≤ ‖D‖ * (c1 * c1) := by
    intro x D hmem i j
    have hterm : ∀ i' j' : Fin G.m,
        |D (fderiv ℝ (fun y => G.sig y j') x (G.sig x i'))| ≤ ‖D‖ * (c1 * c1) := by
      intro i' j'
      have h1 : |D (fderiv ℝ (fun y => G.sig y j') x (G.sig x i'))|
          ≤ ‖D‖ * ‖fderiv ℝ (fun y => G.sig y j') x (G.sig x i')‖ := by
        simpa [Real.norm_eq_abs] using D.le_opNorm
          (fderiv ℝ (fun y => G.sig y j') x (G.sig x i'))
      have h2 : ‖fderiv ℝ (fun y => G.sig y j') x (G.sig x i')‖
          ≤ ‖fderiv ℝ (fun y => G.sig y j') x‖ * ‖G.sig x i'‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have h3 : ‖fderiv ℝ (fun y => G.sig y j') x‖ * ‖G.sig x i'‖ ≤ c1 * c1 :=
        mul_le_mul (hc1Dsig x hmem j') (hc1sig x hmem i') (norm_nonneg _) hc1nn
      calc |D (fderiv ℝ (fun y => G.sig y j') x (G.sig x i'))|
          ≤ ‖D‖ * ‖fderiv ℝ (fun y => G.sig y j') x (G.sig x i')‖ := h1
        _ ≤ ‖D‖ * (c1 * c1) := mul_le_mul_of_nonneg_left (h2.trans h3) (norm_nonneg _)
    have hent : Mfield G.sig x D i j
        = 1 / 2 * (D (fderiv ℝ (fun y => G.sig y j) x (G.sig x i))
          + D (fderiv ℝ (fun y => G.sig y i) x (G.sig x j))) := by
      simp only [Mfield, Matrix.of_apply]
    rw [hent, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    have hab := abs_add_le (D (fderiv ℝ (fun y => G.sig y j) x (G.sig x i)))
      (D (fderiv ℝ (fun y => G.sig y i) x (G.sig x j)))
    linarith only [hab, hterm i j, hterm j i]
  have hhessSsymmOf : ∀ (x : EuclideanSpace ℝ (Fin G.n))
      (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      (∀ a b, B a b = B b a) → (hhessS G.sig x D B).IsSymm := by
    intro x D B hsymm
    ext i j
    simp only [Matrix.transpose_apply, hhessS, Matrix.add_apply, Matrix.of_apply, Mfield]
    rw [hsymm (G.sig x j) (G.sig x i)]
    ring
  -- `N_k` entries tend to 0, which is display (12) in the only form (4c) uses
  obtain ⟨nb, hnbdef⟩ : ∃ nb : ℕ → ℝ, ∀ k, nb k
      = ‖D2Pf mu xl (zseq k)‖ * (c1 * c1)
        + ‖DPf mu xl (zseq k) - innerSL ℝ (pseq k)‖ * (c1 * c1) :=
    ⟨_, fun _ => rfl⟩
  have hD2Pfnn : ∀ (mu' : ℝ) (c x : EuclideanSpace ℝ (Fin G.n)),
      (0:ℝ) ≤ ‖D2Pf mu' c x‖ := fun mu' c x => (D2Pf mu' c x).opNorm_nonneg
  have hnb0 : ∀ k, 0 ≤ nb k := by
    intro k
    rw [hnbdef]
    have h1 : (0:ℝ) ≤ ‖D2Pf mu xl (zseq k)‖ * (c1 * c1) :=
      mul_nonneg (hD2Pfnn mu xl (zseq k)) (mul_nonneg hc1nn hc1nn)
    have h2 : (0:ℝ) ≤ ‖DPf mu xl (zseq k) - innerSL ℝ (pseq k)‖ * (c1 * c1) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg hc1nn hc1nn)
    linarith only [h1, h2]
  have hNkent : ∀ᶠ k in Filter.atTop, ∀ i j, |Nk k i j| ≤ nb k := by
    filter_upwards [hzev] with k hk i j
    have hmem : zseq k ∈ Metric.closedBall xl rho := Metric.ball_subset_closedBall hk
    have hent : Nk k i j
        = D2Pf mu xl (zseq k) (G.sig (zseq k) i) (G.sig (zseq k) j)
          + Mfield G.sig (zseq k) (DPf mu xl (zseq k) - innerSL ℝ (pseq k)) i j := by
      simp only [hNkdef, hhessS, Matrix.add_apply, Matrix.of_apply]
    have hb1 : |D2Pf mu xl (zseq k) (G.sig (zseq k) i) (G.sig (zseq k) j)|
        ≤ ‖D2Pf mu xl (zseq k)‖ * (c1 * c1) := by
      refine (hBopBound _ _ _).trans ?_
      have h3 : ‖G.sig (zseq k) i‖ * ‖G.sig (zseq k) j‖ ≤ c1 * c1 :=
        mul_le_mul (hc1sig (zseq k) hmem i) (hc1sig (zseq k) hmem j)
          (norm_nonneg _) hc1nn
      have hx := mul_le_mul_of_nonneg_left h3 (hD2Pfnn mu xl (zseq k))
      calc ‖D2Pf mu xl (zseq k)‖ * ‖G.sig (zseq k) i‖ * ‖G.sig (zseq k) j‖
          = ‖D2Pf mu xl (zseq k)‖ * (‖G.sig (zseq k) i‖ * ‖G.sig (zseq k) j‖) := by ring
        _ ≤ ‖D2Pf mu xl (zseq k)‖ * (c1 * c1) := hx
    have hb2 := hMfieldent (zseq k) (DPf mu xl (zseq k) - innerSL ℝ (pseq k)) hmem i j
    rw [hent, hnbdef]
    have hab := abs_add_le (D2Pf mu xl (zseq k) (G.sig (zseq k) i) (G.sig (zseq k) j))
      (Mfield G.sig (zseq k) (DPf mu xl (zseq k) - innerSL ℝ (pseq k)) i j)
    linarith only [hab, hb1, hb2]
  have hnbtend : Filter.Tendsto nb Filter.atTop (nhds 0) := by
    have hd1 : Filter.Tendsto (fun k => ‖D2Pf mu xl (zseq k)‖) Filter.atTop (nhds 0) := by
      refine squeeze_zero' (by filter_upwards with k; exact hD2Pfnn mu xl (zseq k))
        hD2Pfk ?_
      simpa using hdeltend.const_mul (12 * mu * rho)
    have hd2 : Filter.Tendsto (fun k => ‖DPf mu xl (zseq k) - innerSL ℝ (pseq k)‖)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero' (by
        filter_upwards with k
        exact (DPf mu xl (zseq k) - innerSL ℝ (pseq k)).opNorm_nonneg) hDPfpk ?_
      simpa using hdeltend.const_mul (4 * mu * rho ^ 2 + 1)
    have h := (hd1.mul_const (c1 * c1)).add (hd2.mul_const (c1 * c1))
    rw [show (0:ℝ) * (c1 * c1) + 0 * (c1 * c1) = 0 from by ring] at h
    exact h.congr fun k => (hnbdef k).symm
  -- (4b).  DEPARTURE from the `.tex`: no compact `𝒬` and no moduli `ω_A, ω_H`.  Both
  -- `ξ_k` and `ξ_k + η_k` CONVERGE, to the same non-zero limit `ξ∞`, so plain continuity
  -- of `A` and `H` at `ξ∞` replaces uniform continuity on `𝒬`, the non-decreasing moduli
  -- of eq:modHA and the sup `‖A‖_{L^∞(𝒬)}`; and `C'` is never needed.
  have hucontAt : ContinuousAt u xl :=
    hucont.continuousAt (mem_nhds_iff.2 ⟨Ω, subset_closure, hΩo, hxlΩ⟩)
  have hutend : Filter.Tendsto (fun k => u (zseq k)) Filter.atTop (nhds (u xl)) :=
    hucontAt.tendsto.comp hztend
  have httend : Filter.Tendsto tk Filter.atTop (nhds (1 + lam * Real.exp (u xl))) := by
    have h := ((Real.continuous_exp.continuousAt.tendsto).comp hutend).const_mul lam
    exact (h.const_add 1).congr fun k => (htkdef k).symm
  have hDktend : Filter.Tendsto Dk Filter.atTop
      (nhds ((1 + lam * Real.exp (u xl)) • Dx1)) :=
    (httend.smul hDukconv).congr fun k => (hDkeq2 k).symm
  obtain ⟨xinf, hxinfdef⟩ : ∃ q : EuclideanSpace ℝ (Fin G.m),
      q = hgrad G.sig xl ((1 + lam * Real.exp (u xl)) • Dx1) := ⟨_, rfl⟩
  have hsumtend : Filter.Tendsto (fun k => xik k + etak k) Filter.atTop (nhds xinf) := by
    rw [hxinfdef]
    exact (HgradTendstoOfTendsto G.sig hsigc zseq xl Dk _ hztend hDktend).congr
      fun k => h10 k
  have hxiktend : Filter.Tendsto xik Filter.atTop (nhds xinf) := by
    have h := hsumtend.sub hetatend
    rw [sub_zero] at h
    exact h.congr fun k => by abel
  have hxinfnorm : θ / 4 ≤ ‖xinf‖ := by
    refine ge_of_tendsto hsumtend.norm ?_
    filter_upwards [h14] with k hk
    rw [← h10 k]
    exact hk.le
  have hxinfne : xinf ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hxinfnorm
    linarith only [hxinfnorm, hθpos]
  have hnbhd : {ξ : EuclideanSpace ℝ (Fin G.m) | ξ ≠ 0} ∈ nhds xinf :=
    mem_nhds_iff.2 ⟨{ξ | ξ ≠ 0}, subset_rfl, isOpen_ne, hxinfne⟩
  have hHat : ContinuousAt H xinf := hAH.contH.continuousAt hnbhd
  have hAat : ContinuousAt A xinf := hAH.contA.continuousAt hnbhd
  have hAent : ∀ i j, ContinuousAt (fun ξ => A ξ i j) xinf := by
    intro i j
    have hproj : Continuous fun M : Matrix (Fin G.m) (Fin G.m) ℝ => M i j :=
      (continuous_apply j).comp (continuous_apply i)
    exact hproj.continuousAt.comp hAat
  -- the two error moduli of display (26), as sequence limits
  have hE1 : Filter.Tendsto (fun k => |H (xik k) - H (xik k + etak k)|)
      Filter.atTop (nhds 0) := by
    have h := (hHat.tendsto.comp hxiktend).sub (hHat.tendsto.comp hsumtend)
    rw [sub_self] at h
    simpa using h.abs
  have hSdA : Filter.Tendsto
      (fun k => ∑ i, ∑ j, |A (xik k + etak k) i j - A (xik k) i j|)
      Filter.atTop (nhds 0) := by
    have h : ∀ i : Fin G.m, Filter.Tendsto
        (fun k => ∑ j, |A (xik k + etak k) i j - A (xik k) i j|)
        Filter.atTop (nhds 0) := by
      intro i
      have hj : ∀ j : Fin G.m, Filter.Tendsto
          (fun k => |A (xik k + etak k) i j - A (xik k) i j|)
          Filter.atTop (nhds 0) := by
        intro j
        have h1 := ((hAent i j).tendsto.comp hsumtend).sub
          ((hAent i j).tendsto.comp hxiktend)
        rw [sub_self] at h1
        simpa using h1.abs
      have h2 := tendsto_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) => hj j
      simpa using h2
    have h3 := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) => h i
    simpa using h3
  obtain ⟨Ca, hCannn, hCa⟩ : ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ᶠ k in Filter.atTop,
      (∑ i, ∑ j, |A (xik k) i j|) ≤ Ca := by
    refine ⟨(∑ i : Fin G.m, ∑ j : Fin G.m, |A xinf i j|) + 1, by positivity, ?_⟩
    have h : Filter.Tendsto (fun k => ∑ i, ∑ j, |A (xik k) i j|) Filter.atTop
        (nhds (∑ i : Fin G.m, ∑ j : Fin G.m, |A xinf i j|)) := by
      refine tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) => ?_
      exact tendsto_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) =>
        ((hAent i j).tendsto.comp hxiktend).abs
    exact h.eventually (eventually_le_nhds (by linarith only []))
  -- (4c) the trace estimate, assembled into display (26).
  have hfinal : ∀ᶠ k in Filter.atTop, gam ≤ |H (xik k) - H (xik k + etak k)|
      + (∑ i, ∑ j, |A (xik k + etak k) i j - A (xik k) i j|) * Cbig
      + Ca * nb k := by
    filter_upwards [h15, h16v, h17, h18, hNkent, hCa] with k h15k h16vk h17k h18k hNkk hCak
    -- `ξ_k ≠ 0` by (15), so `A(ξ_k)` is symmetric and non-negative definite by (E)
    have hxine : xik k ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at h15k
      linarith only [h15k, hθpos]
    have hAsymm := hAH.symm (xik k) hxine
    have hApsd := hAH.psd (xik k) hxine
    have hYsymm := hhessSsymmOf (zseq k) (Dk k) (Bk k) (hjetu k).1
    have hBvsymm : ∀ a b, (Btk k - D2Pf mu xl (zseq k)) a b
        = (Btk k - D2Pf mu xl (zseq k)) b a := by
      intro a b
      rw [sub_apply, sub_apply,
        sub_apply, sub_apply,
        (hjetv k).1 a b, hD2Pfsymm mu xl (zseq k) a b]
    have hXsymm : (hhessS G.sig (zseq k) (Dtk k - DPf mu xl (zseq k))
          (Btk k - D2Pf mu xl (zseq k)) + Nk k).IsSymm := by
      refine Matrix.IsSymm.add (hhessSsymmOf _ _ _ hBvsymm) ?_
      simp only [hNkdef]
      exact hhessSsymmOf _ _ _ (hD2Pfsymm mu xl (zseq k))
    -- display (20): eq:matmon with the non-negative `A(ξ_k)` and the ordering (11)
    have htm := TraceMonotone (A (xik k)) (hhessS G.sig (zseq k) (Dk k) (Bk k))
      (hhessS G.sig (zseq k) (Dtk k - DPf mu xl (zseq k))
        (Btk k - D2Pf mu xl (zseq k)) + Nk k)
      hAsymm hApsd hYsymm hXsymm (h11 k)
    rw [mul_add, Matrix.trace_add] at htm
    -- displays (22) and (23)
    have hxikval : hgrad G.sig (zseq k) (Dtk k - DPf mu xl (zseq k)) = xik k := by
      simp only [hxikdef]
    have hTu : (A (xik k + etak k) * hhessS G.sig (zseq k) (Dk k) (Bk k)).trace
        = H (xik k + etak k) - Lop G.sig A H (zseq k) (Dk k) (Bk k) := by
      simp only [Lop]
      rw [h10 k]
      ring
    have hTv : (A (xik k) * hhessS G.sig (zseq k) (Dtk k - DPf mu xl (zseq k))
          (Btk k - D2Pf mu xl (zseq k))).trace
        = H (xik k) - Lop G.sig A H (zseq k) (Dtk k - DPf mu xl (zseq k))
            (Btk k - D2Pf mu xl (zseq k)) := by
      simp only [Lop]
      rw [hxikval]
      ring
    -- display (24): split `A(ξ_k) = A(ξ_k + η_k) - [A(ξ_k + η_k) - A(ξ_k)]`
    have hsplitA : (A (xik k) * hhessS G.sig (zseq k) (Dk k) (Bk k)).trace
        = (A (xik k + etak k) * hhessS G.sig (zseq k) (Dk k) (Bk k)).trace
          - ((A (xik k + etak k) - A (xik k))
              * hhessS G.sig (zseq k) (Dk k) (Bk k)).trace := by
      rw [sub_mul, Matrix.trace_sub]
      ring
    -- the two error traces, bounded entrywise
    have hE2 : |((A (xik k + etak k) - A (xik k))
          * hhessS G.sig (zseq k) (Dk k) (Bk k)).trace|
        ≤ (∑ i, ∑ j, |A (xik k + etak k) i j - A (xik k) i j|) * Cbig := by
      refine (trAbs (A (xik k + etak k) - A (xik k))
        (hhessS G.sig (zseq k) (Dk k) (Bk k)) Cbig h18k).trans ?_
      refine mul_le_mul_of_nonneg_right (le_of_eq ?_) hCbignn
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.sub_apply]
    have hE3 : |(A (xik k) * Nk k).trace| ≤ Ca * nb k :=
      (trAbs (A (xik k)) (Nk k) (nb k) hNkk).trans
        (mul_le_mul_of_nonneg_right hCak (hnb0 k))
    have hHabs : H (xik k) - H (xik k + etak k)
        ≤ |H (xik k) - H (xik k + etak k)| := le_abs_self _
    have hE2' := (abs_le.1 hE2).2
    have hE3' := (abs_le.1 hE3).2
    linarith only [htm, hTu, hTv, hsplitA, h16vk, h17k, hHabs, hE2', hE3']
  -- the three error terms of display (26) vanish, so the right-hand side is eventually
  -- strictly below `γ`, contradicting `hfinal`.  That refutes the assumption `M₀ > 0`.
  have herr : Filter.Tendsto (fun k => |H (xik k) - H (xik k + etak k)|
      + (∑ i, ∑ j, |A (xik k + etak k) i j - A (xik k) i j|) * Cbig
      + Ca * nb k) Filter.atTop (nhds 0) := by
    have h2 := hSdA.mul_const Cbig
    rw [zero_mul] at h2
    have h3 := hnbtend.const_mul Ca
    rw [mul_zero] at h3
    have h := (hE1.add h2).add h3
    rw [add_zero, add_zero] at h
    exact h
  obtain ⟨k0, hk1, hk2⟩ :=
    ((herr.eventually (eventually_lt_nhds hgampos)).and hfinal).exists
  linarith only [hk1, hk2]
