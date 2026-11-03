import CompND.TranslatedDomain
import CompND.BoundaryCore

/-- The geometry of the inner domains `Ω_δ` and the compact cores `K_ρ` of eq:omdelta:
both sit inside `Ω`, `Ω_δ` is open, `K_ρ` is compact for `ρ > 0`, `K_ρ ⊆ Ω_δ` for `δ < ρ`,
and the whole `d`-ball of radius `δ` (resp. `ρ`) about a point of `Ω_δ` (resp. `K_ρ`) lies
in `Ω`. -/
theorem InnerDomainProperties (G : CarnotSetting)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω) :
    (∀ δ : ℝ, TranslatedDomain G Ω δ ⊆ Ω) ∧
    (∀ ρ : ℝ, BoundaryCore G Ω ρ ⊆ Ω) ∧
    (∀ δ : ℝ, IsOpen (TranslatedDomain G Ω δ)) ∧
    (∀ ρ : ℝ, 0 < ρ → IsCompact (BoundaryCore G Ω ρ)) ∧
    (∀ δ ρ : ℝ, δ < ρ → BoundaryCore G Ω ρ ⊆ TranslatedDomain G Ω δ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ x ∈ TranslatedDomain G Ω δ,
      {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-x) z) < δ} ⊆ Ω) ∧
    (∀ ρ : ℝ, 0 < ρ → ∀ x ∈ BoundaryCore G Ω ρ,
      {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-x) z) < ρ} ⊆ Ω) := by
  -- the group inverse is `-`, hence `d` is symmetric
  have hnegrev : ∀ x y : EuclideanSpace ℝ (Fin G.n), G.mul (-y) (-x) = -(G.mul x y) := by
    intro x y
    have key : ∀ a b : EuclideanSpace ℝ (Fin G.n), G.mul a b = 0 → b = -a := by
      intro a b hab
      have h1 : G.mul (-a) (G.mul a b) = G.mul (-a) 0 := by rw [hab]
      rw [← G.mul_assoc, G.neg_mul, G.zero_mul, G.mul_zero] at h1
      exact h1
    have h2 : G.mul (G.mul x y) (G.mul (-y) (-x)) = 0 := by
      rw [G.mul_assoc x y, ← G.mul_assoc y (-y) (-x), G.mul_neg, G.zero_mul, G.mul_neg]
    exact key _ _ h2
  have hdsymm : ∀ x y : EuclideanSpace ℝ (Fin G.n),
      G.hnorm (G.mul (-y) x) = G.hnorm (G.mul (-x) y) := by
    intro x y
    have h : G.mul (-x) y = -(G.mul (-y) x) := by
      have h0 := hnegrev (-y) x
      simpa using h0
    rw [h, G.hnorm_neg]
  -- the distance kernel is jointly continuous, and continuous in each slot
  have hdjoint : Continuous (Function.uncurry
      fun (x y : EuclideanSpace ℝ (Fin G.n)) => G.hnorm (G.mul (-y) x)) := by
    apply G.hnorm_cont.comp
    exact G.mul_smooth.continuous.comp (continuous_snd.neg.prodMk continuous_fst)
  have hdcont2 : ∀ x : EuclideanSpace ℝ (Fin G.n),
      Continuous fun y : EuclideanSpace ℝ (Fin G.n) => G.hnorm (G.mul (-y) x) :=
    fun x => G.hnorm_cont.comp (G.mul_smooth.continuous.comp
      (continuous_neg.prodMk continuous_const))
  have hdcont1 : ∀ y : EuclideanSpace ℝ (Fin G.n),
      Continuous fun x : EuclideanSpace ℝ (Fin G.n) => G.hnorm (G.mul (-y) x) :=
    fun y => G.hnorm_cont.comp (G.mul_smooth.continuous.comp
      (continuous_const.prodMk continuous_id))
  -- the frontier is compact
  have hKcpt : IsCompact (frontier Ω) := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_frontier ?_
    exact (hΩbdd.closure).subset frontier_subset_closure
  -- the ball-inclusion fact: it comes from `ball_connected`, not a triangle inequality
  have hball : ∀ (x : EuclideanSpace ℝ (Fin G.n)), x ∈ Ω → ∀ δ : ℝ, 0 < δ →
      (∀ y ∈ frontier Ω, δ ≤ G.hnorm (G.mul (-y) x)) →
      {z : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-x) z) < δ} ⊆ Ω := by
    intro x hx δ hδ hfar
    set S : Set (EuclideanSpace ℝ (Fin G.n)) := {z | G.hnorm (G.mul (-x) z) < δ} with hS
    have hconn : IsConnected S := G.ball_connected x δ hδ
    have hmiss : ∀ z ∈ S, z ∉ frontier Ω := by
      intro z hz hzf
      have h1 : δ ≤ G.hnorm (G.mul (-z) x) := hfar z hzf
      rw [hdsymm x z] at h1
      exact absurd hz (by simpa [hS] using not_lt.mpr h1)
    have hcover : S ⊆ Ω ∪ (closure Ω)ᶜ := by
      intro z hz
      by_cases hzc : z ∈ closure Ω
      · left
        by_contra hzo
        exact hmiss z hz (by rw [hΩopen.frontier_eq]; exact ⟨hzc, hzo⟩)
      · right; exact hzc
    have hpre := hconn.isPreconnected
    by_contra hnot
    obtain ⟨w, hwS, hwΩ⟩ := Set.not_subset.1 hnot
    have hw2 : w ∈ (closure Ω)ᶜ := by
      rcases hcover hwS with h | h
      · exact absurd h hwΩ
      · exact h
    have hxS : x ∈ S := by
      have : G.hnorm (G.mul (-x) x) = 0 := by rw [G.neg_mul]; exact (G.hnorm_eq_zero 0).2 rfl
      simpa [hS, this] using hδ
    exact absurd (hpre Ω (closure Ω)ᶜ hΩopen isClosed_closure.isOpen_compl hcover
      ⟨x, hxS, hx⟩ ⟨w, hwS, hw2⟩) (by
        rintro ⟨z, -, hz1, hz2⟩
        exact hz2 (subset_closure hz1))
  refine ⟨fun δ x hx => hx.1, fun ρ x hx => hx.1, ?_, ?_,
    fun δ ρ hδρ x hx => ⟨hx.1, fun y hy => lt_of_lt_of_le hδρ (hx.2 y hy)⟩, ?_, ?_⟩
  · -- `Ω_δ` is open
    intro δ
    rcases Set.eq_empty_or_nonempty (frontier Ω) with hemp | hne
    · have : TranslatedDomain G Ω δ = Ω := by
        ext x; simp [TranslatedDomain, hemp]
      rw [this]; exact hΩopen
    · have hBdd : ∀ x : EuclideanSpace ℝ (Fin G.n),
          BddBelow ((fun y => G.hnorm (G.mul (-y) x)) '' frontier Ω) := by
        intro x
        refine ⟨0, ?_⟩
        rintro r ⟨y, -, rfl⟩
        exact G.hnorm_nonneg _
      set f : EuclideanSpace ℝ (Fin G.n) → ℝ :=
        fun x => sInf ((fun y => G.hnorm (G.mul (-y) x)) '' frontier Ω) with hf
      have hfcont : Continuous f := hKcpt.continuous_sInf hdjoint
      have hle : ∀ (x : EuclideanSpace ℝ (Fin G.n)), ∀ y ∈ frontier Ω,
          f x ≤ G.hnorm (G.mul (-y) x) := by
        intro x y hy
        exact csInf_le (hBdd x) ⟨y, hy, rfl⟩
      have hmem : ∀ x : EuclideanSpace ℝ (Fin G.n),
          f x ∈ (fun y => G.hnorm (G.mul (-y) x)) '' frontier Ω := by
        intro x
        exact (hKcpt.image (hdcont2 x)).sInf_mem (hne.image _)
      have hset : TranslatedDomain G Ω δ = Ω ∩ {x | δ < f x} := by
        ext x
        constructor
        · intro hx
          refine ⟨hx.1, ?_⟩
          obtain ⟨y, hy, hyf⟩ := hmem x
          have h1 : δ < G.hnorm (G.mul (-y) x) := hx.2 y hy
          have h2 : G.hnorm (G.mul (-y) x) = f x := hyf
          show δ < f x
          rw [← h2]; exact h1
        · intro hx
          exact ⟨hx.1, fun y hy => lt_of_lt_of_le hx.2 (hle x y hy)⟩
      rw [hset]
      exact hΩopen.inter (isOpen_lt continuous_const hfcont)
  · -- `K_ρ` is compact
    intro ρ hρ
    have hT : IsClosed {x : EuclideanSpace ℝ (Fin G.n) |
        ∀ y ∈ frontier Ω, ρ ≤ G.hnorm (G.mul (-y) x)} := by
      have : {x : EuclideanSpace ℝ (Fin G.n) | ∀ y ∈ frontier Ω, ρ ≤ G.hnorm (G.mul (-y) x)}
          = ⋂ y ∈ frontier Ω, {x | ρ ≤ G.hnorm (G.mul (-y) x)} := by
        ext x; simp
      rw [this]
      exact isClosed_biInter fun y _ => isClosed_le continuous_const (hdcont1 y)
    have hEq : BoundaryCore G Ω ρ = closure Ω ∩ {x : EuclideanSpace ℝ (Fin G.n) |
        ∀ y ∈ frontier Ω, ρ ≤ G.hnorm (G.mul (-y) x)} := by
      ext x
      constructor
      · intro hx; exact ⟨subset_closure hx.1, hx.2⟩
      · intro hx
        refine ⟨?_, hx.2⟩
        by_contra hxΩ
        have hxf : x ∈ frontier Ω := by rw [hΩopen.frontier_eq]; exact ⟨hx.1, hxΩ⟩
        have := hx.2 x hxf
        rw [G.neg_mul] at this
        rw [(G.hnorm_eq_zero 0).2 rfl] at this
        linarith
    rw [hEq]
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_closure.inter hT) ?_
    exact hΩbdd.closure.subset Set.inter_subset_left
  · -- the `d`-ball of radius `δ` around a point of `Ω_δ`
    intro δ hδ x hx
    exact hball x hx.1 δ hδ fun y hy => (hx.2 y hy).le
  · -- the `d`-ball of radius `ρ` around a point of `K_ρ`
    intro ρ hρ x hx
    exact hball x hx.1 ρ hρ fun y hy => hx.2 y hy
