import CompND.ReducedDomain
import CompND.InverseUniquenessAndDistanceSymmetry

/-- The properties of the reduced domains `Ω[ε]` of eq:redom asserted at paper line 608:
`Ω[ε] ⊆ Ω` is open and bounded, increases as `ε` decreases, exhausts `Ω` as `ε → 0⁺`, has
closure inside `Ω`, and its boundary approaches `∂Ω` uniformly as `ε → 0⁺`. -/
theorem ReducedDomainProperties (G : CarnotSetting)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hΩne : ∃ y : EuclideanSpace ℝ (Fin G.n), y ∉ Ω)
    (R : ℝ) (hR : 0 ≤ R) :
    (∀ ε : ℝ, ReducedDomain G Ω R ε ⊆ Ω) ∧
    (∀ ε : ℝ, Bornology.IsBounded (ReducedDomain G Ω R ε)) ∧
    (∀ ε ε' : ℝ, ε' ≤ ε → ReducedDomain G Ω R ε ⊆ ReducedDomain G Ω R ε') ∧
    (∀ ε : ℝ, 0 < ε → IsOpen (ReducedDomain G Ω R ε)) ∧
    (∀ x ∈ Ω, ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → x ∈ ReducedDomain G Ω R ε) ∧
    (∀ ε : ℝ, 0 < ε → closure (ReducedDomain G Ω R ε) ⊆ Ω) ∧
    (∀ η : ℝ, 0 < η → ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ z ∈ frontier (ReducedDomain G Ω R ε), ∃ w ∈ frontier Ω,
        G.hnorm (G.mul (-w) z) < η) := by
  -- Throughout, `q = 2 r!`, `c = 1 + 4R`, `κ y x = ‖y * x⁻¹‖^q = ‖y * (-x)‖^q` and
  -- `f x = ⨅_{y ∉ Ω} κ y x`, so that `Ω[ε] = {x ∈ Ω | c ε < f x}` by `ReducedDomain`.
  -- Step 0 (0a): `c ≥ 1 > 0`.
  have hcnn : (0:ℝ) ≤ 1 + 4 * R := by linarith only [hR]
  have hcpos : (0:ℝ) < 1 + 4 * R := by linarith only [hR]
  -- Step 0 (0b): the infimum of `ReducedDomain` is a genuine infimum.  In Lean this is
  -- load-bearing rather than a remark: `⨅` over a subtype is a `ciInf`, and in Mathlib the
  -- infimum of an empty or unbounded-below real family is `0` by convention, so every one
  -- of the seven conjuncts needs `Nonempty {y // y ∉ Ω}` and the `BddBelow` below.
  obtain ⟨y₀, hy₀⟩ := hΩne
  have hsubne : Nonempty {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω} := ⟨⟨y₀, hy₀⟩⟩
  have hq1 : 1 ≤ 2 * Nat.factorial G.r := by
    have h := Nat.factorial_pos G.r
    omega
  have hqne : 2 * Nat.factorial G.r ≠ 0 := by omega
  have hkapnn : ∀ y x : EuclideanSpace ℝ (Fin G.n),
      0 ≤ G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r) :=
    fun y x => pow_nonneg (G.hnorm_nonneg _) _
  have hbdd : ∀ x : EuclideanSpace ℝ (Fin G.n),
      BddBelow (Set.range fun y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω} =>
        G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r)) := by
    intro x
    refine ⟨0, ?_⟩
    rintro b ⟨y, rfl⟩
    exact hkapnn y.1 x
  -- Step 0 (0c): `κ` is jointly continuous -- the group law is `C^∞`, `‖·‖` is continuous
  -- and `t ↦ t^q` is continuous.
  have hkapcont : Continuous
      fun p : EuclideanSpace ℝ (Fin G.n) × EuclideanSpace ℝ (Fin G.n) =>
        G.hnorm (G.mul p.2 (-p.1)) ^ (2 * Nat.factorial G.r) := by
    have hmul : Continuous
        fun p : EuclideanSpace ℝ (Fin G.n) × EuclideanSpace ℝ (Fin G.n) =>
          G.mul p.1 p.2 := G.mul_smooth.continuous
    have hswap : Continuous
        fun p : EuclideanSpace ℝ (Fin G.n) × EuclideanSpace ℝ (Fin G.n) =>
          ((p.2, -p.1) : EuclideanSpace ℝ (Fin G.n) × EuclideanSpace ℝ (Fin G.n)) :=
      continuous_snd.prodMk continuous_fst.neg
    exact (G.hnorm_cont.comp (hmul.comp hswap)).pow _
  have hkapcontx : ∀ y : EuclideanSpace ℝ (Fin G.n),
      Continuous fun x => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r) := fun y =>
    hkapcont.comp (continuous_id.prodMk continuous_const)
  have hkapconty : ∀ x : EuclideanSpace ℝ (Fin G.n),
      Continuous fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r) := fun x =>
    hkapcont.comp (continuous_const.prodMk continuous_id)
  -- Step 0 (0d): `κ x x = 0`
  have hkapself : ∀ x : EuclideanSpace ℝ (Fin G.n),
      G.hnorm (G.mul x (-x)) ^ (2 * Nat.factorial G.r) = 0 := by
    intro x
    rw [G.mul_neg x, (G.hnorm_eq_zero 0).2 rfl, zero_pow hqne]
  -- Step 0 (0e): `‖·‖` is bounded on `Ω`, by clause (6) of `CarnotNorm` at `b := 0`
  obtain ⟨T, hTnn, hTb⟩ : ∃ T : ℝ, 0 ≤ T ∧ ∀ a ∈ Ω, G.hnorm a ≤ T := by
    obtain ⟨r0, hr0⟩ := hΩbdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin G.n))
    have hmr : (0:ℝ) ≤ max r0 0 := le_max_right r0 0
    have hν : (0:ℝ) < max r0 0 + 1 := by linarith only [hmr]
    obtain ⟨c2, hc2pos, hc2⟩ := G.holder_equiv (max r0 0 + 1) hν
    refine ⟨c2 * (max r0 0 + 1) ^ ((1:ℝ) / G.r), ?_, fun a ha => ?_⟩
    · exact mul_nonneg hc2pos.le (Real.rpow_nonneg hν.le _)
    · have hane : ‖a‖ ≤ max r0 0 := by
        have h := hr0 ha
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h.trans (le_max_left _ _)
      have hale : ‖a‖ ≤ max r0 0 + 1 := by linarith only [hane]
      have h0le : ‖(0 : EuclideanSpace ℝ (Fin G.n))‖ ≤ max r0 0 + 1 := by
        rw [norm_zero]
        linarith only [hν]
      obtain ⟨-, h2⟩ := hc2 a 0 hale h0le
      rw [neg_zero, G.zero_mul, sub_zero] at h2
      refine h2.trans (mul_le_mul_of_nonneg_left ?_ hc2pos.le)
      exact Real.rpow_le_rpow (norm_nonneg a) hale (by positivity)
  -- Step 4: the compact localization of the infimum.  This is the step the paper does not
  -- supply, and conjunct (4) rests on it: for every `x₀` there are an open `U ∋ x₀` and a
  -- non-empty compact `K ⊆ ℝⁿ \ Ω` with `f = ⨅_K κ(·, x)` on `U`, and that localized
  -- infimum is continuous.
  have step4 : ∀ x₀ : EuclideanSpace ℝ (Fin G.n),
      ∃ U K : Set (EuclideanSpace ℝ (Fin G.n)),
        IsOpen U ∧ x₀ ∈ U ∧ IsCompact K ∧ K.Nonempty ∧ (∀ y ∈ K, y ∉ Ω) ∧
        Continuous (fun x => sInf ((fun y =>
            G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K)) ∧
        ∀ x ∈ U, (⨅ y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω},
            G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r))
          = sInf ((fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K) := by
    intro x₀
    have hU'cpt : IsCompact (Metric.closedBall x₀ 1) := isCompact_closedBall _ _
    have hx₀U' : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
    have hUU' : Metric.ball x₀ 1 ⊆ Metric.closedBall x₀ 1 := Metric.ball_subset_closedBall
    -- `M := 1 + max_{U'} κ(y₀, ·) ≥ 1`, so that `κ(y₀, x) ≤ M - 1 < M` on `U'`
    obtain ⟨Mb, hMb⟩ := hU'cpt.bddAbove_image (hkapcontx y₀).continuousOn
    obtain ⟨M, hM1, hMU'⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ x ∈ Metric.closedBall x₀ 1,
        G.hnorm (G.mul y₀ (-x)) ^ (2 * Nat.factorial G.r) ≤ M - 1 := by
      refine ⟨1 + max Mb 0, by linarith only [le_max_right Mb (0:ℝ)], fun x hx => ?_⟩
      have h := hMb (Set.mem_image_of_mem _ hx)
      have h2 := le_max_left Mb (0:ℝ)
      linarith only [h, h2]
    -- `S := M + 1`.  (Departure from the `.tex`'s `S := M^{1/q}`: only the forward
    -- implication `t^q ≤ M → t ≤ S` is ever used, and `M + 1` supplies it with no `rpow`.)
    have hSle : ∀ t : ℝ, 0 ≤ t → t ^ (2 * Nat.factorial G.r) ≤ M → t ≤ M + 1 := by
      intro t ht h
      by_contra hc
      rw [not_le] at hc
      have ht1 : (1:ℝ) ≤ t := by linarith only [hc, hM1]
      have h1 : t ^ 1 ≤ t ^ (2 * Nat.factorial G.r) := pow_le_pow_right₀ ht1 hq1
      rw [pow_one] at h1
      linarith only [h, h1, hc]
    -- `T' := max_{U'} ‖·‖ ≥ 0`
    obtain ⟨T'b, hT'b⟩ := hU'cpt.bddAbove_image G.hnorm_cont.continuousOn
    obtain ⟨T', hT'nn, hT'U'⟩ : ∃ T' : ℝ, 0 ≤ T' ∧
        ∀ x ∈ Metric.closedBall x₀ 1, G.hnorm x ≤ T' :=
      ⟨max T'b 0, le_max_right _ _, fun x hx =>
        (hT'b (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩
    -- clause (4) of `CarnotNorm` at `ν := S + T' + 1`.  `‖·‖` is only a QUASI-norm
    -- (pm-0013), so the constant `c₁ = c_G(ν)` is carried and BOTH side conditions
    -- `‖a‖ < ν`, `‖b‖ < ν` are discharged at each use; the `+1` is the slack that does it.
    have hνpos : (0:ℝ) < (M + 1) + T' + 1 := by linarith only [hM1, hT'nn]
    obtain ⟨c₁, hc₁pos, hc₁⟩ := G.hnorm_mul_le ((M + 1) + T' + 1) hνpos
    obtain ⟨K, hKdef⟩ : ∃ K : Set (EuclideanSpace ℝ (Fin G.n)),
        K = {y : EuclideanSpace ℝ (Fin G.n) | y ∉ Ω} ∩
          {y : EuclideanSpace ℝ (Fin G.n) | G.hnorm y ≤ c₁ * ((M + 1) + T')} := ⟨_, rfl⟩
    have hKmem : ∀ y : EuclideanSpace ℝ (Fin G.n),
        y ∈ K ↔ (y ∉ Ω ∧ G.hnorm y ≤ c₁ * ((M + 1) + T')) := by
      intro y
      rw [hKdef]
      exact Iff.rfl
    -- (4-ii) the key implication: on `U'`, `κ(y,x) ≤ M` forces `‖y‖ ≤ C₁`
    have h4ii : ∀ x ∈ Metric.closedBall x₀ 1, ∀ y : EuclideanSpace ℝ (Fin G.n),
        G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r) ≤ M →
        G.hnorm y ≤ c₁ * ((M + 1) + T') := by
      intro x hx y hkle
      have haS : G.hnorm (G.mul y (-x)) ≤ M + 1 := hSle _ (G.hnorm_nonneg _) hkle
      have hxT : G.hnorm x ≤ T' := hT'U' x hx
      have hax : G.mul (G.mul y (-x)) x = y := by
        rw [G.mul_assoc, G.neg_mul, G.mul_zero]
      have h := hc₁ (G.mul y (-x)) x (by linarith only [haS, hT'nn])
        (by linarith only [hxT, hM1])
      rw [hax] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hc₁pos.le)
      linarith only [haS, hxT]
    -- (4-iii) `y₀ ∈ K`, so `K ≠ ∅`
    have h4iii : y₀ ∈ K := by
      refine (hKmem y₀).2 ⟨hy₀, h4ii x₀ hx₀U' y₀ ?_⟩
      have h := hMU' x₀ hx₀U'
      linarith only [h]
    -- (4-i) `K` is compact: closed (as `Ωᶜ ∩` a closed sublevel set) and bounded (clause
    -- (8) of `CarnotNorm`)
    have hKclosed : IsClosed K := by
      rw [hKdef]
      exact hΩopen.isClosed_compl.inter (isClosed_le G.hnorm_cont continuous_const)
    have hKbdd : Bornology.IsBounded K := by
      refine (G.hnorm_proper (c₁ * ((M + 1) + T'))).subset fun y hy => ?_
      exact ((hKmem y).1 hy).2
    have hKcpt : IsCompact K :=
      hKbdd.isCompact_closure.of_isClosed_subset hKclosed subset_closure
    have hKne : K.Nonempty := ⟨y₀, h4iii⟩
    have hKsub : ∀ y ∈ K, y ∉ Ω := fun y hy => ((hKmem y).1 hy).1
    -- (4-v) the localized infimum is continuous, by `IsCompact.continuous_sInf`
    have hFcont : Continuous fun x => sInf ((fun y =>
        G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K) :=
      IsCompact.continuous_sInf
        (f := fun x y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) hKcpt hkapcont
    -- (4-iv) the identity (4a), on `U'` and hence on `U`
    have h4iv : ∀ x ∈ Metric.closedBall x₀ 1,
        (⨅ y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω},
            G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r))
          = sInf ((fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K) := by
      intro x hx
      have himne : ((fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K).Nonempty :=
        hKne.image _
      have himbdd : BddBelow
          ((fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K) := by
        refine ⟨0, ?_⟩
        rintro b ⟨y, -, rfl⟩
        exact hkapnn y x
      refine le_antisymm (le_csInf himne ?_) (le_ciInf fun y => ?_)
      · rintro b ⟨y, hyK, rfl⟩
        exact ciInf_le (hbdd x) (⟨y, hKsub y hyK⟩ : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω})
      · by_cases hyK : y.1 ∈ K
        · exact csInf_le himbdd (Set.mem_image_of_mem _ hyK)
        · -- `y ∉ Ω` and `y ∉ K` force `‖y‖ > C₁`, so `κ(y,x) > M > M - 1 ≥ α`
          have hgt : c₁ * ((M + 1) + T') < G.hnorm y.1 := by
            by_contra hc
            rw [not_lt] at hc
            exact hyK ((hKmem y.1).2 ⟨y.2, hc⟩)
          have hkgt : M < G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r) := by
            by_contra hc
            rw [not_lt] at hc
            exact absurd (h4ii x hx y.1 hc) (not_le.2 hgt)
          have h0 : sInf ((fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K)
              ≤ G.hnorm (G.mul y₀ (-x)) ^ (2 * Nat.factorial G.r) :=
            csInf_le himbdd (Set.mem_image_of_mem _ h4iii)
          have h1 := hMU' x hx
          linarith only [h0, h1, hkgt]
    exact ⟨Metric.ball x₀ 1, K, Metric.isOpen_ball, Metric.mem_ball_self one_pos,
      hKcpt, hKne, hKsub, hFcont, fun x hx => h4iv x (hUU' hx)⟩
  -- Step 5: conjunct (4), openness.  Hoisted out of the conjunction because Step 8 needs
  -- it as well: `∂Ω[ε] = closure Ω[ε] \ Ω[ε]` requires `Ω[ε]` open.
  have hopen : ∀ ε : ℝ, 0 < ε → IsOpen (ReducedDomain G Ω R ε) := by
    -- Step 5, conjunct (4): openness.  `V := Ω ∩ U ∩ {c ε < F}` is open by Step 4 and sits
      -- inside `Ω[ε]` because `f = F` on `U`.
      intro ε hε
      rw [isOpen_iff_forall_mem_open]
      intro x₀ hx₀
      obtain ⟨U, K, hUopen, hx₀U, hKcpt, hKne, hKsub, hFcont, hid⟩ := step4 x₀
      refine ⟨Ω ∩ U ∩ {x : EuclideanSpace ℝ (Fin G.n) | (1 + 4 * R) * ε <
        sInf ((fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K)}, ?_, ?_, ?_⟩
      · intro x hx
        refine ⟨hx.1.1, ?_⟩
        rw [hid x hx.1.2]
        exact hx.2
      · exact (hΩopen.inter hUopen).inter (isOpen_lt continuous_const hFcont)
      · refine ⟨⟨hx₀.1, hx₀U⟩, ?_⟩
        show (1 + 4 * R) * ε <
          sInf ((fun y => G.hnorm (G.mul y (-x₀)) ^ (2 * Nat.factorial G.r)) '' K)
        rw [← hid x₀ hx₀U]
        exact hx₀.2
  -- Step 7: conjunct (6), `closure (Ω[ε]) ⊆ Ω`.  Hoisted for the same reason.
  have hclosure : ∀ ε : ℝ, 0 < ε → closure (ReducedDomain G Ω R ε) ⊆ Ω := by
      -- `Ω[ε] ⊆ S⋆ := ⋂_{y ∉ Ω} {c ε ≤ κ(y, ·)}`, which is closed, and `x ∉ Ω` would make
      -- `y := x` admissible, giving `c ε ≤ κ(x,x) = 0`.
      intro ε hε
      have hSclosed : IsClosed (⋂ y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω},
          {x : EuclideanSpace ℝ (Fin G.n) | (1 + 4 * R) * ε ≤
            G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r)}) :=
        isClosed_iInter fun y => isClosed_le continuous_const (hkapcontx y.1)
      have hsub : ReducedDomain G Ω R ε ⊆ ⋂ y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω},
          {x : EuclideanSpace ℝ (Fin G.n) | (1 + 4 * R) * ε ≤
            G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r)} := by
        intro x hx
        refine Set.mem_iInter.2 fun y => ?_
        exact le_of_lt (lt_of_lt_of_le hx.2 (ciInf_le (hbdd x) y))
      have hclsub := hSclosed.closure_subset_iff.2 hsub
      intro x hxcl
      by_contra hxΩ
      have h := Set.mem_iInter.1 (hclsub hxcl)
        (⟨x, hxΩ⟩ : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω})
      have h' : (1 + 4 * R) * ε ≤ G.hnorm (G.mul x (-x)) ^ (2 * Nat.factorial G.r) := h
      rw [hkapself x] at h'
      have hcε : 0 < (1 + 4 * R) * ε := mul_pos hcpos hε
      linarith only [h', hcε]
  -- Step 8, preliminaries: `-(a * b) = (-b) * (-a)` and the symmetry (8a) of the
  -- quasi-distance `d`, both from uniqueness of inverses in the group axioms.
  obtain ⟨-, hnegmul, hdsymm⟩ := InverseUniquenessAndDistanceSymmetry G
  refine ⟨?_, ?_, ?_, hopen, ?_, hclosure, ?_⟩
  · -- Step 1, conjunct (1): `Ω[ε] ⊆ Ω` is the first component of the set-builder
    intro ε x hx
    exact hx.1
  · -- Step 2, conjunct (2): a subset of the bounded `Ω`
    intro ε
    exact hΩbdd.subset fun x hx => hx.1
  · -- Step 3, conjunct (3): `c > 0`, so `c ε' ≤ c ε < f x`
    intro ε ε' hle x hx
    exact ⟨hx.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle hcnn) hx.2⟩
  · -- Step 6, conjunct (5): the exhaustion.  On the non-empty compact `K` of Step 4 the
    -- infimum is attained at some `y⋆ ∉ Ω`, and `y⋆ ≠ x` forces `f x > 0`.
    intro x hx
    obtain ⟨U, K, hUopen, hxU, hKcpt, hKne, hKsub, hFcont, hid⟩ := step4 x
    have himne : ((fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K).Nonempty :=
      hKne.image _
    have himbdd : BddBelow
        ((fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K) := by
      refine ⟨0, ?_⟩
      rintro b ⟨y, -, rfl⟩
      exact hkapnn y x
    obtain ⟨ys, hysK, hysmin⟩ :=
      hKcpt.exists_isMinOn hKne (hkapconty x).continuousOn
    have hattained : sInf ((fun y => G.hnorm (G.mul y (-x)) ^ (2 * Nat.factorial G.r)) '' K)
        = G.hnorm (G.mul ys (-x)) ^ (2 * Nat.factorial G.r) := by
      refine le_antisymm (csInf_le himbdd (Set.mem_image_of_mem _ hysK)) ?_
      refine le_csInf himne ?_
      rintro b ⟨y, hyK, rfl⟩
      exact hysmin hyK
    have hysne : G.mul ys (-x) ≠ 0 := by
      intro hz
      have hid2 : G.mul (G.mul ys (-x)) x = ys := by
        rw [G.mul_assoc, G.neg_mul, G.mul_zero]
      rw [hz, G.zero_mul] at hid2
      exact hKsub ys hysK (hid2 ▸ hx)
    have hpos : 0 < G.hnorm (G.mul ys (-x)) ^ (2 * Nat.factorial G.r) := by
      refine pow_pos ?_ _
      rcases lt_or_eq_of_le (G.hnorm_nonneg (G.mul ys (-x))) with h | h
      · exact h
      · exact absurd ((G.hnorm_eq_zero _).1 h.symm) hysne
    have hfpos : 0 < ⨅ y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω},
        G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r) := by
      rw [hid x hxU, hattained]
      exact hpos
    refine ⟨(⨅ y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω},
        G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r)) / (1 + 4 * R),
      div_pos hfpos hcpos, fun ε hεpos hεlt => ?_⟩
    refine ⟨hx, ?_⟩
    rw [lt_div_iff₀ hcpos, mul_comm] at hεlt
    exact hεlt
  · -- Step 8, conjunct (7): the boundary approach.
    intro η hη
    -- (8b): clause (5) of `CarnotNorm` at `ν := T + 2`, `T` from (0e)
    have hν2 : (0:ℝ) < T + 2 := by linarith only [hTnn]
    obtain ⟨c3, hc3pos, hc3⟩ := G.hnorm_conj_le (T + 2) hν2
    have hrpos : (0:ℝ) < (G.r : ℝ) := by
      have h := G.one_le_r
      have : (1:ℝ) ≤ (G.r : ℝ) := by exact_mod_cast h
      linarith only [this]
    -- (8c): a radius `δ < 1` with `c₃ δ^{1/r} < η`, and then `ε₀ := δ^q / (2c)`.
    -- (Departure from the `.tex`, which picks `ε₀` from the two limits
    -- `(2cε)^{1/q} → 0` and `c₃(2cε)^{1/(qr)} → 0`: choosing `δ` FIRST and `ε₀` from it
    -- gives the same two conclusions with one `rpow` identity instead of two limits.)
    obtain ⟨δ, hδpos, hδ1, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        c3 * δ ^ ((1:ℝ) / G.r) < η := by
      have hbase : (0:ℝ) < η / (2 * c3) := by positivity
      have hmpos : (0:ℝ) < min (1/2) ((η / (2 * c3)) ^ (G.r : ℝ)) :=
        lt_min (by norm_num) (Real.rpow_pos_of_pos hbase _)
      refine ⟨min (1/2) ((η / (2 * c3)) ^ (G.r : ℝ)), hmpos,
        lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
      have h2 : ((η / (2 * c3)) ^ (G.r : ℝ)) ^ ((1:ℝ) / G.r) = η / (2 * c3) := by
        rw [← Real.rpow_mul hbase.le, mul_one_div, div_self (ne_of_gt hrpos),
          Real.rpow_one]
      have h1 : (min (1/2) ((η / (2 * c3)) ^ (G.r : ℝ))) ^ ((1:ℝ) / G.r)
          ≤ η / (2 * c3) := by
        have hmono : (min (1/2) ((η / (2 * c3)) ^ (G.r : ℝ))) ^ ((1:ℝ) / G.r)
            ≤ ((η / (2 * c3)) ^ (G.r : ℝ)) ^ ((1:ℝ) / G.r) :=
          Real.rpow_le_rpow hmpos.le (min_le_right _ _) (by positivity)
        rwa [h2] at hmono
      have h3 : c3 * (min (1/2) ((η / (2 * c3)) ^ (G.r : ℝ))) ^ ((1:ℝ) / G.r)
          ≤ c3 * (η / (2 * c3)) := mul_le_mul_of_nonneg_left h1 hc3pos.le
      have h4 : c3 * (η / (2 * c3)) = η / 2 := by
        field_simp
      rw [h4] at h3
      linarith only [h3, hη]
    refine ⟨δ ^ (2 * Nat.factorial G.r) / (2 * (1 + 4 * R)),
      div_pos (pow_pos hδpos _) (by linarith only [hcpos]), fun ε hεpos hεlt z hz => ?_⟩
    -- (8-i) `z ∈ Ω` and `f z ≤ c ε`
    rw [(hopen ε hεpos).frontier_eq] at hz
    have hzcl : z ∈ closure (ReducedDomain G Ω R ε) := hz.1
    have hznot : z ∉ ReducedDomain G Ω R ε := hz.2
    have hzΩ : z ∈ Ω := hclosure ε hεpos hzcl
    have hfz : (⨅ y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω},
        G.hnorm (G.mul y.1 (-z)) ^ (2 * Nat.factorial G.r)) ≤ (1 + 4 * R) * ε := by
      by_contra hc
      rw [not_le] at hc
      exact hznot ⟨hzΩ, hc⟩
    have hzT : G.hnorm z ≤ T := hTb z hzΩ
    -- (8-ii) a point `y ∉ Ω` with `d(z,y) < η`
    have hcε : (0:ℝ) < (1 + 4 * R) * ε := mul_pos hcpos hεpos
    obtain ⟨y, hylt⟩ := exists_lt_of_ciInf_lt
      (show (⨅ y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω},
          G.hnorm (G.mul y.1 (-z)) ^ (2 * Nat.factorial G.r))
        < (1 + 4 * R) * ε + (1 + 4 * R) * ε from by linarith only [hfz, hcε])
    have hsq : G.hnorm (G.mul y.1 (-z)) ^ (2 * Nat.factorial G.r)
        < δ ^ (2 * Nat.factorial G.r) := by
      rw [lt_div_iff₀ (by linarith only [hcpos] : (0:ℝ) < 2 * (1 + 4 * R))] at hεlt
      linarith only [hylt, hεlt]
    have hsδ : G.hnorm (G.mul y.1 (-z)) < δ :=
      lt_of_pow_lt_pow_left₀ _ hδpos.le hsq
    have hgz : G.mul (G.mul y.1 (-z)) z = y.1 := by
      rw [G.mul_assoc, G.neg_mul, G.mul_zero]
    have hdzy : G.hnorm (G.mul (-y.1) z) < η := by
      have hconj := hc3 z (-(G.mul y.1 (-z)))
        (by linarith only [hzT]) (by rw [G.hnorm_neg]; linarith only [hsδ, hδ1, hTnn])
      have hrw : G.mul (G.mul (-z) (-(G.mul y.1 (-z)))) z = G.mul (-y.1) z := by
        rw [← hnegmul (G.mul y.1 (-z)) z, hgz]
      rw [hrw, G.hnorm_neg] at hconj
      refine lt_of_le_of_lt (hconj.trans ?_) hδη
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (G.hnorm_nonneg _) hsδ.le (by positivity)) hc3pos.le
    -- (8-iii) the quasi-ball `B` is connected, meets `Ω` at `z` and its complement at `y`,
    -- so it meets `∂Ω`
    have hBconn : IsConnected {w : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-z) w) < η} :=
      G.ball_connected z η hη
    have hzB : z ∈ {w : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-z) w) < η} := by
      show G.hnorm (G.mul (-z) z) < η
      rw [G.neg_mul, (G.hnorm_eq_zero 0).2 rfl]
      exact hη
    have hyB : y.1 ∈ {w : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-z) w) < η} := by
      show G.hnorm (G.mul (-z) y.1) < η
      rw [hdsymm y.1 z]
      exact hdzy
    by_contra hcon
    push Not at hcon
    -- no point of `B` lies on `∂Ω`, so `B ⊆ Ω ∪ (closure Ω)ᶜ`, two disjoint open sets
    have hBsub : {w : EuclideanSpace ℝ (Fin G.n) | G.hnorm (G.mul (-z) w) < η}
        ⊆ Ω ∪ (closure Ω)ᶜ := by
      intro w hw
      by_cases hwΩ : w ∈ Ω
      · exact Or.inl hwΩ
      · refine Or.inr ?_
        intro hwcl
        have hwfr : w ∈ frontier Ω := by
          rw [hΩopen.frontier_eq]
          exact ⟨hwcl, hwΩ⟩
        have hge := hcon w hwfr
        rw [hdsymm z w] at hge
        have hw' : G.hnorm (G.mul (-z) w) < η := hw
        linarith only [hw', hge]
    obtain ⟨w, hwB, hwΩ, hwcl⟩ := hBconn.isPreconnected Ω (closure Ω)ᶜ hΩopen
      isClosed_closure.isOpen_compl hBsub ⟨z, hzB, hzΩ⟩ ⟨y.1, hyB, by
        intro hyc
        have hyfr : y.1 ∈ frontier Ω := by
          rw [hΩopen.frontier_eq]
          exact ⟨hyc, y.2⟩
        have hge := hcon y.1 hyfr
        rw [hdsymm z y.1] at hge
        have hy' : G.hnorm (G.mul (-z) y.1) < η := hyB
        linarith only [hy', hge]⟩
    exact hwcl (subset_closure hwΩ)
