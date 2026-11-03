import CompND.AbelianNoStandingPair
import CompND.NormalizationExists
import CompND.NormalizedSameViscositySolutions
import CompND.RegularizedPairStandingAssumptions

/-- Comparison in an abelian setting under (E) and (S) alone, with no non-degeneracy
hypothesis: the paper's "by the proof of Theorem thm:comp, it suffices to show that under the
standing assumptions a semi-convex/semi-concave pair cannot exist". The regularized pair
`(uᵋ, ṽ_ε)` on `Ω[ε]` is such a pair, and the abelian engine forbids it. -/
theorem ComparisonAbelian (G : CarnotSetting) (hc : CitedResults G)
    (hab : ∀ x y : EuclideanSpace ℝ (Fin G.n), G.mul x y = G.mul y x)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (hAH : StructureConditionsES G.m A H)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hΩne : ∃ y : EuclideanSpace ℝ (Fin G.n), y ∉ Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (hsub : IsViscSubsol G A H Ω u) (hsup : IsViscSupersol G A H Ω v)
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x)
    (R : ℝ) (hR : 0 ≤ R)
    (hRb : ∀ x ∈ closure Ω, |u x| ≤ R / 2 ∧ |v x| ≤ R / 2) :
    ∀ x ∈ Ω, u x ≤ v x := by
  intro x₀ hx₀
  by_contra hcon
  rw [not_le] at hcon
  -- ===== Step 0: `M₀ > 0` =====
  have hΩcl : IsCompact (closure Ω) := hΩbdd.isCompact_closure
  obtain ⟨xM, hxM, hxMmax⟩ :=
    hΩcl.exists_isMaxOn ⟨x₀, subset_closure hx₀⟩ (hucont.sub hvcont)
  have hM0pos : 0 < u xM - v xM := by
    have hle : u x₀ - v x₀ ≤ u xM - v xM := isMaxOn_iff.1 hxMmax x₀ (subset_closure hx₀)
    linarith
  -- ===== Step 1: normalize once =====
  obtain ⟨A₀, H₀, a, hapos, -, hAeq, hHeq, hAH₀, hN₀⟩ := NormalizationExists A H hAH
  have hsub0 : IsViscSubsol G A₀ H₀ Ω u :=
    (NormalizedSameViscositySolutions G A A₀ H H₀ a hapos hAeq hHeq Ω u).1.1 hsub
  have hsup0 : IsViscSupersol G A₀ H₀ Ω v :=
    (NormalizedSameViscositySolutions G A A₀ H H₀ a hapos hAeq hHeq Ω v).2.1 hsup
  -- ===== Step 2: the regularized pair =====
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = (u xM - v xM) / 2 := ⟨_, rfl⟩
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  obtain ⟨-, -, ⟨ε₁, hε₁pos, hRPSA⟩, -⟩ :=
    RegularizedPairStandingAssumptions G hc A₀ H₀ hAH₀ Ω hΩopen hΩbdd hΩne u v hucont hvcont
      hsub0 hsup0 hbdry R hR hRb xM hxM hxMmax hM0pos τ hτdef _ rfl
  obtain ⟨ep, hepdef⟩ : ∃ e : ℝ, e = ε₁ / 2 := ⟨_, rfl⟩
  have heppos : 0 < ep := by rw [hepdef]; linarith
  have heplt : ep < ε₁ := by rw [hepdef]; linarith
  obtain ⟨U, hUdef⟩ : ∃ U : EuclideanSpace ℝ (Fin G.n) → ℝ, U = SupConv G Ω u ep := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : EuclideanSpace ℝ (Fin G.n) → ℝ,
      V = fun y => InfConv G Ω v ep y + τ := ⟨_, rfl⟩
  obtain ⟨-, hUcont, hVcont, hUsc, hVsc, hUsub, hVsup, hbdryUV,
    ⟨xe, hxe, hxemax, hxeval⟩, -⟩ := hRPSA ep heppos heplt U V hUdef hVdef
  -- ===== Step 3: the geometry of `Ω' = Ω[ε]` =====
  obtain ⟨hrd1, hrd2, -, hrd4, -, -, -⟩ := ReducedDomainProperties G Ω hΩopen hΩbdd hΩne R hR
  have hΩ'open : IsOpen (ReducedDomain G Ω R ep) := hrd4 ep heppos
  have hΩ'bdd : Bornology.IsBounded (ReducedDomain G Ω R ep) := hrd2 ep
  have hΩ'ne : ∃ y : EuclideanSpace ℝ (Fin G.n), y ∉ ReducedDomain G Ω R ep := by
    obtain ⟨p, hp⟩ := hΩne
    exact ⟨p, fun hpm => hp (hrd1 ep hpm)⟩
  have hΩ'cl : IsCompact (closure (ReducedDomain G Ω R ep)) := hΩ'bdd.isCompact_closure
  -- ===== Step 4: the eq:rho0 package, as a two-valued step function (pm-0018) =====
  have hstep : ∀ w : EuclideanSpace ℝ (Fin G.n) → ℝ,
      ContinuousOn w (closure (ReducedDomain G Ω R ep)) → ∀ η : ℝ, 0 < η →
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ ω : ℝ → ℝ, (∀ s t : ℝ, s ≤ t → ω s ≤ ω t) ∧
        (∀ a ∈ closure (ReducedDomain G Ω R ep),
          ∀ b ∈ closure (ReducedDomain G Ω R ep),
          |w a - w b| ≤ ω (G.hnorm (G.mul (-b) a))) ∧ ω ρ ≤ η := by
    intro w hw η hη
    -- a sup-norm bound for `w` on the compact `K`
    obtain ⟨M, hM⟩ := hΩ'cl.exists_bound_of_continuousOn hw
    have hMabs : ∀ x ∈ closure (ReducedDomain G Ω R ep), |w x| ≤ M := by
      intro x hx
      have := hM x hx
      rwa [Real.norm_eq_abs] at this
    -- uniform continuity of `w` on `K` in the Euclidean metric
    have hwcu := hΩ'cl.uniformContinuousOn_of_continuous hw
    rw [Metric.uniformContinuousOn_iff] at hwcu
    obtain ⟨ϱ, hϱpos, hbw⟩ := hwcu η hη
    -- the Hölder comparison (LOWER half only; pm-0013)
    obtain ⟨ν0, hν0⟩ := hΩ'cl.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin G.n))
    have hνnn : (0:ℝ) ≤ max ν0 0 := le_max_right _ _
    have hνpos : (0:ℝ) < max ν0 0 + 1 := by linarith only [hνnn]
    obtain ⟨c, hcpos, hc⟩ := G.holder_equiv (max ν0 0 + 1) hνpos
    have hnorml : ∀ x ∈ closure (ReducedDomain G Ω R ep), ‖x‖ ≤ max ν0 0 + 1 := by
      intro x hx
      have h := hν0 hx
      rw [Metric.mem_closedBall, dist_zero_right] at h
      have h2 : ν0 ≤ max ν0 0 := le_max_left _ _
      linarith only [h, h2]
    -- the radius and the step function.  The `/2` is what makes the Euclidean bound STRICT.
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ϱ / (2 * c) := ⟨_, rfl⟩
    have hρpos : 0 < ρ := by rw [hρdef]; positivity
    have hcρ : c * ρ = ϱ / 2 := by
      rw [hρdef]
      field_simp
    obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ → ℝ,
        ∀ s, ω s = if s ≤ ρ then η else η + (2 * |M| + 1) := ⟨_, fun _ => rfl⟩
    refine ⟨ρ, hρpos, ω, ?_, ?_, ?_⟩
    · -- monotone
      intro s t hst
      rw [hωdef s, hωdef t]
      by_cases hs : s ≤ ρ
      · by_cases ht : t ≤ ρ
        · rw [if_pos hs, if_pos ht]
        · rw [if_pos hs, if_neg ht]
          have := abs_nonneg M
          linarith
      · have ht : ¬ t ≤ ρ := fun hh => hs (le_trans hst hh)
        rw [if_neg hs, if_neg ht]
    · -- the modulus property
      intro p hp q hq
      rw [hωdef]
      by_cases hd : G.hnorm (G.mul (-q) p) ≤ ρ
      · rw [if_pos hd]
        obtain ⟨hlow, -⟩ := hc p q (hnorml p hp) (hnorml q hq)
        have h1 : ‖p - q‖ ≤ c * G.hnorm (G.mul (-q) p) := by
          have h := mul_le_mul_of_nonneg_left hlow hcpos.le
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul] at h
          exact h
        have hcd : c * G.hnorm (G.mul (-q) p) ≤ c * ρ :=
          mul_le_mul_of_nonneg_left hd hcpos.le
        rw [hcρ] at hcd
        have h2 : ‖p - q‖ < ϱ := by linarith
        have h3 := hbw p hp q hq (by rw [dist_eq_norm]; exact h2)
        rw [Real.dist_eq] at h3
        linarith
      · rw [if_neg hd]
        obtain ⟨h4, h5⟩ := abs_le.1 (hMabs p hp)
        obtain ⟨h6, h7⟩ := abs_le.1 (hMabs q hq)
        have h8 : |w p - w q| ≤ 2 * M := by
          rw [abs_le]
          constructor <;> linarith
        have h9 := le_abs_self M
        linarith
    · -- `ω ρ ≤ η`
      rw [hωdef, if_pos (le_refl ρ)]
  obtain ⟨ρU, hρUpos, ωU, hωUmono, hωUmod, hωUval⟩ :=
    hstep U hUcont (τ / 16) (by linarith)
  obtain ⟨ρV, hρVpos, ωV, hωVmono, hωVmod, hωVval⟩ :=
    hstep V hVcont (τ / 16) (by linarith)
  obtain ⟨ρ0, hρ0pos, hρ0U, hρ0V⟩ : ∃ ρ0 : ℝ, 0 < ρ0 ∧ ρ0 ≤ ρU ∧ ρ0 ≤ ρV :=
    ⟨min ρU ρV, lt_min hρUpos hρVpos, min_le_left _ _, min_le_right _ _⟩
  -- display (3)
  have hmodsum : ωU ρ0 + ωV ρ0 ≤ (τ / 2) / 4 := by
    have h1 := hωUmono ρ0 ρU hρ0U
    have h2 := hωVmono ρ0 ρV hρ0V
    linarith
  -- ===== Step 5: the standing assumptions for `(U, V)` on `Ω'`, and the contradiction =====
  exact AbelianNoStandingPair G hc hab A₀ H₀ hAH₀ hN₀ (ReducedDomain G Ω R ep)
    hΩ'open hΩ'bdd hΩ'ne U V hUcont hVcont hUsc hVsc hUsub hVsup
    ωU ωV hωUmono hωVmono hωUmod hωVmod (τ / 2) (by linarith) hbdryUV
    xe (subset_closure hxe) hxemax (by linarith) ρ0 hρ0pos hmodsum
