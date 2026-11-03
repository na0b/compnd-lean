import CompND.ComparisonNondegenerateSemiconvex
import CompND.NormalizationExists
import CompND.NormalizedSameViscositySolutions
import CompND.RegularizedPairStandingAssumptions

/-- thm:comp: the comparison principle under the non-degeneracy hypothesis of the first step
of the Barles-Busca argument, imposed on the regularizations. On a bounded open `Ω`, for
`(A, H)` satisfying only (E) and (S), a viscosity sub-solution `u` and super-solution `v` in
`C(closure Ω)` with `u ≤ v` on `∂Ω` satisfy `u ≤ v` in `Ω`, provided there is a sequence
`εₖ → 0⁺` along which `𝔛uᵋ` does not vanish on the interior maximum set `E_ε` of eq:Eeps. -/
theorem ComparisonUnderNondegeneracy (G : CarnotSetting) (hc : CitedResults G)
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
    (hRb : ∀ x ∈ closure Ω, |u x| ≤ R / 2 ∧ |v x| ≤ R / 2)
    (εs : ℕ → ℝ) (hεpos : ∀ k, 0 < εs k)
    (hεlim : Filter.Tendsto εs Filter.atTop (nhds 0))
    (hnd : ∀ k : ℕ, ∀ x ∈ ReducedDomain G Ω R (εs k),
      IsMaxOn (fun y => SupConv G Ω u (εs k) y - InfConv G Ω v (εs k) y)
        (closure (ReducedDomain G Ω R (εs k))) x →
      ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
        HasFDerivAt (SupConv G Ω u (εs k)) D x → hgrad G.sig x D ≠ 0) :
    ∀ x ∈ Ω, u x ≤ v x := by
  intro x0 hx0
  by_contra hcon
  rw [not_le] at hcon
  -- Step 0: the maximum of `u - v` over `closure Ω` is positive
  have hcl : IsCompact (closure Ω) := hΩbdd.isCompact_closure
  have hclne : (closure Ω).Nonempty := ⟨x0, subset_closure hx0⟩
  have hdiffcont : ContinuousOn (fun y => u y - v y) (closure Ω) := hucont.sub hvcont
  obtain ⟨xM, hxM, hxMmax⟩ := hcl.exists_isMaxOn hclne hdiffcont
  have hM0 : 0 < u xM - v xM := by
    have h1 : u x0 - v x0 ≤ u xM - v xM := hxMmax (subset_closure hx0)
    linarith
  set τ : ℝ := (u xM - v xM) / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  -- Step 1: normalize once
  obtain ⟨A₀, H₀, a, ha, hacont, hA, hH, hAH₀, hN₀⟩ := NormalizationExists A H hAH
  have hiff := NormalizedSameViscositySolutions G A A₀ H H₀ a ha hA hH Ω u
  have hiffv := NormalizedSameViscositySolutions G A A₀ H H₀ a ha hA hH Ω v
  have hsub₀ : IsViscSubsol G A₀ H₀ Ω u := hiff.1.1 hsub
  have hsup₀ : IsViscSupersol G A₀ H₀ Ω v := hiffv.2.1 hsup
  -- Step 2: the standing assumptions for the regularized pair
  obtain ⟨-, -, hmain, -⟩ :=
    RegularizedPairStandingAssumptions G hc A₀ H₀ hAH₀ Ω hΩopen hΩbdd hΩne u v hucont hvcont
      hsub₀ hsup₀ hbdry R hR hRb xM hxM hxMmax hM0 τ hτdef
      {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} rfl
  obtain ⟨ε₁, hε₁pos, hstand⟩ := hmain
  -- Step 3: choose an index
  obtain ⟨k, hk⟩ := (hεlim.eventually_lt_const hε₁pos).exists
  set ε : ℝ := εs k with hεdef
  have hεpos' : 0 < ε := hεpos k
  set Ω' : Set (EuclideanSpace ℝ (Fin G.n)) := ReducedDomain G Ω R ε with hΩ'def
  obtain ⟨-, hbdd, -, hopen, -, -, -⟩ :=
    ReducedDomainProperties G Ω hΩopen hΩbdd hΩne R hR
  have hΩ'open : IsOpen Ω' := hopen ε hεpos'
  have hΩ'bdd : Bornology.IsBounded Ω' := hbdd ε
  -- the standing-assumption clauses at this ε
  obtain ⟨-, huC, hvC, husc, hvsc, hsubE, hsupE, hbdryE, hattain, -⟩ :=
    hstand ε hεpos' hk (SupConv G Ω u ε) (fun y => InfConv G Ω v ε y + τ) rfl rfl
  -- Step 4: the non-degeneracy hypothesis transfers to Ω'
  have hnd' : ∀ x ∈ Ω', IsMaxOn (fun y => SupConv G Ω u ε y - (InfConv G Ω v ε y + τ)) Ω' x →
      ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
        HasFDerivAt (SupConv G Ω u ε) D x → hgrad G.sig x D ≠ 0 := by
    intro x hx hmax D hD
    have hcontE : ContinuousOn (fun y => SupConv G Ω u ε y - (InfConv G Ω v ε y + τ))
        (closure Ω') := huC.sub hvC
    have hup : IsMaxOn (fun y => SupConv G Ω u ε y - (InfConv G Ω v ε y + τ))
        (closure Ω') x := by
      intro z hz
      obtain ⟨zs, hzs, hzlim⟩ := mem_closure_iff_seq_limit.1 hz
      have hten : Filter.Tendsto
          (fun j => SupConv G Ω u ε (zs j) - (InfConv G Ω v ε (zs j) + τ))
          Filter.atTop
          (nhds (SupConv G Ω u ε z - (InfConv G Ω v ε z + τ))) := by
        have hw : Filter.Tendsto zs Filter.atTop (nhdsWithin z (closure Ω')) :=
          tendsto_nhdsWithin_iff.2
            ⟨hzlim, Filter.Eventually.of_forall fun j => subset_closure (hzs j)⟩
        exact (hcontE z hz).tendsto.comp hw
      exact le_of_tendsto' hten fun j => hmax (hzs j)
    have hupnoτ : IsMaxOn (fun y => SupConv G Ω u ε y - InfConv G Ω v ε y)
        (closure Ω') x := by
      intro z hz
      have h1 : SupConv G Ω u ε z - (InfConv G Ω v ε z + τ)
          ≤ SupConv G Ω u ε x - (InfConv G Ω v ε x + τ) := hup hz
      show SupConv G Ω u ε z - InfConv G Ω v ε z
        ≤ SupConv G Ω u ε x - InfConv G Ω v ε x
      linarith
    exact hnd k x hx hupnoτ D hD
  -- Step 5: prop:comp0 on Ω'
  have hcomp := ComparisonNondegenerateSemiconvex G hc A₀ H₀ hAH₀ hN₀ Ω' hΩ'open hΩ'bdd
    (SupConv G Ω u ε) (fun y => InfConv G Ω v ε y + τ) huC hvC husc hvsc
    (fun z hz => by
      have h1 : SupConv G Ω u ε z - (InfConv G Ω v ε z + τ) ≤ -(τ / 2) := hbdryE z hz
      show SupConv G Ω u ε z ≤ InfConv G Ω v ε z + τ
      linarith)
    hsubE hsupE hnd'
  -- Step 6: contradiction
  obtain ⟨xe, hxe, -, hxeval⟩ := hattain
  have h1 : SupConv G Ω u ε xe ≤ InfConv G Ω v ε xe + τ := hcomp xe hxe
  have h2 : τ ≤ SupConv G Ω u ε xe - (InfConv G Ω v ε xe + τ) := hxeval
  linarith
