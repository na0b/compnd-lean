import CompND.AddConstPreservesSubsol
import CompND.CitedResults
import CompND.ViscTestLocalization

/-- thm:uncond(ii): if one of the two functions is constant, comparison holds. With `v ≡ c`
(resp. `u ≡ c`) a positive `max (u - v)` would put an interior maximum of `u` (resp. interior
minimum of `v`) in `Ω`; the strong maximum (resp. minimum) principle makes it constant on the
connected component, where `u - v ≡ M₀ > 0`, contradicting `u ≤ v` on `∂Ω`. -/
theorem UncondCaseConstant (G : CarnotSetting) (hcr : CitedResults G)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (hAH : StructureConditionsES G.m A H)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hΩne : ∃ y : EuclideanSpace ℝ (Fin G.n), y ∉ Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (hsub : IsViscSubsol G A H Ω u) (hsup : IsViscSupersol G A H Ω v)
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ((∃ c : ℝ, ∀ x ∈ closure Ω, v x = c) → ∀ x ∈ Ω, u x ≤ v x) ∧
    ((∃ c : ℝ, ∀ x ∈ closure Ω, u x = c) → ∀ x ∈ Ω, u x ≤ v x) := by
  have hdc : ContinuousOn (fun w => u w - v w) (closure Ω) := hucont.sub hvcont
  -- the common topological core: a component on which `u - v` is a positive constant
  -- contradicts `u ≤ v` on `∂Ω`
  have core : ∀ y : EuclideanSpace ℝ (Fin G.n), y ∈ Ω → ∀ M : ℝ, 0 < M →
      (∀ z ∈ connectedComponentIn Ω y, u z - v z = M) → False := by
    intro y hy M hM hconst
    set C : Set (EuclideanSpace ℝ (Fin G.n)) := connectedComponentIn Ω y with hCdef
    have hCopen : IsOpen C := hΩopen.connectedComponentIn
    have hCsub : C ⊆ Ω := connectedComponentIn_subset Ω y
    have hyC : y ∈ C := mem_connectedComponentIn hy
    -- `∂C ≠ ∅`
    have hfrne : (frontier C).Nonempty := by
      rcases Set.eq_empty_or_nonempty (frontier C) with hemp | hne
      · exfalso
        have hclopen : IsClopen C := isClopen_iff_frontier_eq_empty.2 hemp
        have huniv : C = Set.univ := hclopen.eq_univ ⟨y, hyC⟩
        obtain ⟨p, hp⟩ := hΩne
        exact hp (hCsub (by rw [huniv]; trivial))
      · exact hne
    obtain ⟨z, hzf⟩ := hfrne
    have hzsplit : z ∈ closure C \ C := by rw [← hCopen.frontier_eq]; exact hzf
    -- `∂C ⊆ ∂Ω`
    have hzΩ : z ∉ Ω := by
      intro hzΩ
      have hop : IsOpen (connectedComponentIn Ω z) := hΩopen.connectedComponentIn
      have hzin : z ∈ connectedComponentIn Ω z := mem_connectedComponentIn hzΩ
      obtain ⟨w, hwz, hwC⟩ := mem_closure_iff.1 hzsplit.1 _ hop hzin
      have h1 : connectedComponentIn Ω z = connectedComponentIn Ω w := connectedComponentIn_eq hwz
      have h2 : C = connectedComponentIn Ω w := by rw [hCdef]; exact connectedComponentIn_eq hwC
      rw [← h2] at h1
      exact hzsplit.2 (h1 ▸ hzin)
    have hzfr : z ∈ frontier Ω := by
      rw [hΩopen.frontier_eq]
      exact ⟨closure_mono hCsub hzsplit.1, hzΩ⟩
    have hzclΩ : z ∈ closure Ω := frontier_subset_closure hzfr
    -- pass to the limit along a sequence in `C`
    obtain ⟨zs, hzs, hzlim⟩ := mem_closure_iff_seq_limit.1 hzsplit.1
    have hten : Filter.Tendsto (fun k => u (zs k) - v (zs k)) Filter.atTop
        (nhds (u z - v z)) := by
      have hw : Filter.Tendsto zs Filter.atTop (nhdsWithin z (closure Ω)) :=
        tendsto_nhdsWithin_iff.2
          ⟨hzlim, Filter.Eventually.of_forall fun k => subset_closure (hCsub (hzs k))⟩
      exact (hdc z hzclΩ).tendsto.comp hw
    have hconstseq : (fun k => u (zs k) - v (zs k)) = fun _ : ℕ => M :=
      funext fun k => hconst _ (hzs k)
    rw [hconstseq] at hten
    have hval : u z - v z = M := (tendsto_nhds_unique tendsto_const_nhds hten).symm
    have hle := hbdry z hzfr
    linarith
  constructor
  · -- `v ≡ c`
    rintro ⟨cv, hcv⟩ x0 hx0
    by_contra hcon
    rw [not_le] at hcon
    have hcl : IsCompact (closure Ω) := hΩbdd.isCompact_closure
    have hclne : (closure Ω).Nonempty := ⟨x0, subset_closure hx0⟩
    obtain ⟨xM, hxM, hxMmax⟩ := hcl.exists_isMaxOn hclne hdc
    have hM0 : 0 < u xM - v xM := by
      have h1 : u x0 - v x0 ≤ u xM - v xM := hxMmax (subset_closure hx0)
      linarith
    have hxMΩ : xM ∈ Ω := by
      by_contra hno
      have hfr : xM ∈ frontier Ω := by rw [hΩopen.frontier_eq]; exact ⟨hxM, hno⟩
      have := hbdry xM hfr
      linarith
    have humax : ∀ z ∈ closure Ω, u z ≤ u xM := by
      intro z hz
      have h1 : u z - v z ≤ u xM - v xM := hxMmax hz
      rw [hcv z hz, hcv xM hxM] at h1
      linarith
    set C : Set (EuclideanSpace ℝ (Fin G.n)) := connectedComponentIn Ω xM with hCdef
    have hCopen : IsOpen C := hΩopen.connectedComponentIn
    have hCsub : C ⊆ Ω := connectedComponentIn_subset Ω xM
    have hbd : ∃ Mu : ℝ, ∀ y ∈ Ω, u y + -(u xM) ≤ Mu :=
      ⟨0, fun y hy => by have := humax y (subset_closure hy); linarith⟩
    have hshift : IsViscSubsol G A H Ω (fun z => u z + -(u xM)) :=
      (AddConstPreservesSubsol G A H Ω u (-(u xM))).1 hsub
    obtain ⟨-, hrest⟩ :=
      (ViscTestLocalization G A H Ω (fun z => u z + -(u xM))).1 hbd hshift
    have hsubC : IsViscSubsol G A H C (fun z => u z + -(u xM)) := hrest C hCopen hCsub
    have hmaxC : IsMaxOn (fun z => u z + -(u xM)) C xM := by
      intro z hz
      have h1 := humax z (subset_closure (hCsub hz))
      show u z + -(u xM) ≤ u xM + -(u xM)
      linarith
    have hnn : (0 : ℝ) ≤ u xM + -(u xM) := by linarith
    have hcC := hcr.strongMax A H hAH C hCopen
      (isConnected_connectedComponentIn_iff.2 hxMΩ) (fun z => u z + -(u xM)) hsubC
      xM (mem_connectedComponentIn hxMΩ) hmaxC hnn
    refine core xM hxMΩ (u xM - v xM) hM0 fun z hz => ?_
    have h1 : u z + -(u xM) = u xM + -(u xM) := hcC z hz
    have h2 : v z = cv := hcv z (subset_closure (hCsub hz))
    have h3 : v xM = cv := hcv xM hxM
    show u z - v z = u xM - v xM
    rw [h2, h3]; linarith
  · -- `u ≡ c`
    rintro ⟨cu, hcu⟩ x0 hx0
    by_contra hcon
    rw [not_le] at hcon
    have hcl : IsCompact (closure Ω) := hΩbdd.isCompact_closure
    have hclne : (closure Ω).Nonempty := ⟨x0, subset_closure hx0⟩
    obtain ⟨xM, hxM, hxMmax⟩ := hcl.exists_isMaxOn hclne hdc
    have hM0 : 0 < u xM - v xM := by
      have h1 : u x0 - v x0 ≤ u xM - v xM := hxMmax (subset_closure hx0)
      linarith
    have hxMΩ : xM ∈ Ω := by
      by_contra hno
      have hfr : xM ∈ frontier Ω := by rw [hΩopen.frontier_eq]; exact ⟨hxM, hno⟩
      have := hbdry xM hfr
      linarith
    have hvmin : ∀ z ∈ closure Ω, v xM ≤ v z := by
      intro z hz
      have h1 : u z - v z ≤ u xM - v xM := hxMmax hz
      rw [hcu z hz, hcu xM hxM] at h1
      linarith
    set C : Set (EuclideanSpace ℝ (Fin G.n)) := connectedComponentIn Ω xM with hCdef
    have hCopen : IsOpen C := hΩopen.connectedComponentIn
    have hCsub : C ⊆ Ω := connectedComponentIn_subset Ω xM
    have hbd : ∃ mu : ℝ, ∀ y ∈ Ω, mu ≤ v y + -(v xM) :=
      ⟨0, fun y hy => by have := hvmin y (subset_closure hy); linarith⟩
    have hshift : IsViscSupersol G A H Ω (fun z => v z + -(v xM)) :=
      (AddConstPreservesSubsol G A H Ω v (-(v xM))).2 hsup
    obtain ⟨-, hrest⟩ :=
      (ViscTestLocalization G A H Ω (fun z => v z + -(v xM))).2 hbd hshift
    have hsupC : IsViscSupersol G A H C (fun z => v z + -(v xM)) := hrest C hCopen hCsub
    have hminC : IsMinOn (fun z => v z + -(v xM)) C xM := by
      intro z hz
      have h1 := hvmin z (subset_closure (hCsub hz))
      show v xM + -(v xM) ≤ v z + -(v xM)
      linarith
    have hnp : v xM + -(v xM) ≤ (0 : ℝ) := by linarith
    have hcC := hcr.strongMin A H hAH C hCopen
      (isConnected_connectedComponentIn_iff.2 hxMΩ) (fun z => v z + -(v xM)) hsupC
      xM (mem_connectedComponentIn hxMΩ) hminC hnp
    refine core xM hxMΩ (u xM - v xM) hM0 fun z hz => ?_
    have h1 : v z + -(v xM) = v xM + -(v xM) := hcC z hz
    have h2 : u z = cu := hcu z (subset_closure (hCsub hz))
    have h3 : u xM = cu := hcu xM hxM
    show u z - v z = u xM - v xM
    rw [h2, h3]; linarith
