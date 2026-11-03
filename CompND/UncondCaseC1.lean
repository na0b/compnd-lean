import CompND.ComparisonUnderNondegeneracy
import CompND.LeftTranslateHgrad
import CompND.SemiConvexDiffAtMax
import CompND.SupConvAttainment

/-- thm:uncond(i): if one of the two functions is `C¹` with non-vanishing horizontal gradient
on a neighbourhood of `argmax_Ω (u - v)`, then comparison holds. The node's work is to verify
the non-degeneracy hypothesis of thm:comp on the regularizations, by transporting the
non-vanishing from `v` (resp. `u`) to `v_ε` (resp. `u^ε`) along the left translation supplied
by lem:wang(4). -/
theorem UncondCaseC1 (G : CarnotSetting) (hc : CitedResults G)
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
    (N : Set (EuclideanSpace ℝ (Fin G.n))) (hNopen : IsOpen N)
    (hEN : {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} ⊆ N) :
    ((ContDiffOn ℝ 1 v N ∧
        ∀ z ∈ N, ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
          HasFDerivAt v D z → hgrad G.sig z D ≠ 0) →
      ∀ x ∈ Ω, u x ≤ v x) ∧
    ((ContDiffOn ℝ 1 u N ∧
        ∀ z ∈ N, ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
          HasFDerivAt u D z → hgrad G.sig z D ≠ 0) →
      ∀ x ∈ Ω, u x ≤ v x) := by
  have hclcpt : IsCompact (closure Ω) := hΩbdd.isCompact_closure
  have hq1 : 1 ≤ 2 * Nat.factorial G.r := by
    have h := Nat.factorial_pos G.r
    omega
  obtain ⟨-, -, -, hrd4, -, -, -⟩ :=
    ReducedDomainProperties G Ω hΩopen hΩbdd hΩne R hR
  -- (6c): a differentiable function touching another from one side at an interior point of
  -- an open set has the same derivative there.  Covers both orientations.
  have touch : ∀ (f g : EuclideanSpace ℝ (Fin G.n) → ℝ)
      (S : Set (EuclideanSpace ℝ (Fin G.n))) (x : EuclideanSpace ℝ (Fin G.n))
      (Df Dg : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ),
      IsOpen S → x ∈ S → (∀ y ∈ S, f y ≤ g y) → f x = g x →
      HasFDerivAt f Df x → HasFDerivAt g Dg x → Df = Dg := by
    intro f g S x Df Dg hS hx hle heq hf hg
    have hmax : IsLocalMax (fun y => f y - g y) x := by
      filter_upwards [hS.mem_nhds hx] with y hy
      show f y - g y ≤ f x - g x
      rw [heq, sub_self]
      linarith only [hle y hy]
    exact sub_eq_zero.1 (hmax.hasFDerivAt_eq_zero (hf.sub hg))
  -- (6b) and Step 7 bundled: on `N` a `C¹` function with non-vanishing horizontal gradient
  -- transports that non-vanishing to the left translate, by `LeftTranslateHgrad`.
  have transport : ∀ (w : EuclideanSpace ℝ (Fin G.n) → ℝ), ContDiffOn ℝ 1 w N →
      (∀ zz ∈ N, ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
        HasFDerivAt w D zz → hgrad G.sig zz D ≠ 0) →
      ∀ z x : EuclideanSpace ℝ (Fin G.n), G.mul z x ∈ N →
      ∃ D' : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
        HasFDerivAt (fun y => w (G.mul z y)) D' x ∧ hgrad G.sig x D' ≠ 0 := by
    intro w hw hnv z x hzxN
    have hdw : DifferentiableAt ℝ w (G.mul z x) :=
      (hw.differentiableOn (by norm_num)).differentiableAt (hNopen.mem_nhds hzxN)
    have hDw : HasFDerivAt w (fderiv ℝ w (G.mul z x)) (G.mul z x) := hdw.hasFDerivAt
    have hL : ContDiff ℝ (⊤ : ℕ∞) fun y : EuclideanSpace ℝ (Fin G.n) => G.mul z y :=
      G.mul_smooth.comp (contDiff_const.prodMk contDiff_id)
    have hLd := (hL.differentiable (by norm_num) x).hasFDerivAt
    refine ⟨(fderiv ℝ w (G.mul z x)).comp (fderiv ℝ (fun y => G.mul z y) x),
      hDw.comp x hLd, ?_⟩
    rw [LeftTranslateHgrad G w z x (fderiv ℝ w (G.mul z x)) _ hDw (hDw.comp x hLd)]
    exact hnv (G.mul z x) hzxN _ hDw
  -- Step 2: the Hölder comparison `|a - b| ≤ c₀ d(a,b)` on `closure Ω`, and a bound on the
  -- homogeneous norm there.  `d` is only a quasi-distance (pm-0013), so the comparison must
  -- come from the `holder_equiv` clause with its constant.
  obtain ⟨ν0, hν0pos, hν0b⟩ : ∃ ν0 : ℝ, 0 < ν0 ∧ ∀ a ∈ closure Ω, ‖a‖ ≤ ν0 := by
    obtain ⟨r0, hr0⟩ := hclcpt.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin G.n))
    refine ⟨max r0 0 + 1, by linarith only [le_max_right r0 (0:ℝ)], fun a ha => ?_⟩
    have h := hr0 ha
    rw [Metric.mem_closedBall, dist_zero_right] at h
    have h2 : r0 ≤ max r0 0 := le_max_left _ _
    linarith only [h, h2]
  obtain ⟨c0, hc0pos, hc0⟩ := G.holder_equiv ν0 hν0pos
  have h3 : ∀ a ∈ closure Ω, ∀ b ∈ closure Ω,
      ‖a - b‖ ≤ c0 * G.hnorm (G.mul (-b) a) := by
    intro a ha b hb
    obtain ⟨hlow, -⟩ := hc0 a b (hν0b a ha) (hν0b b hb)
    have h := mul_le_mul_of_nonneg_left hlow hc0pos.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc0pos), one_mul] at h
    exact h
  obtain ⟨μ0, hμ0pos, hμ0b⟩ : ∃ μ0 : ℝ, 0 < μ0 ∧ ∀ a ∈ closure Ω, G.hnorm a ≤ μ0 := by
    obtain ⟨Mb, hMb⟩ := hclcpt.bddAbove_image G.hnorm_cont.continuousOn
    refine ⟨max Mb 0 + 1, by linarith only [le_max_right Mb (0:ℝ)], fun a ha => ?_⟩
    have h := hMb (Set.mem_image_of_mem _ ha)
    have h2 : Mb ≤ max Mb 0 := le_max_left _ _
    linarith only [h, h2]
  -- Step 5, with an EXPLICIT threshold instead of the `.tex`'s limit: the inequality is
  -- inverted once and for all, so no `Tendsto` reasoning appears.
  have step5 : ∀ ρN : ℝ, 0 < ρN →
      (∀ p ∈ {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y},
        ∀ w : EuclideanSpace ℝ (Fin G.n), ‖w - p‖ < ρN → w ∈ N) →
      ∃ ε3 > 0, ∀ ε : ℝ, 0 < ε → ε < ε3 →
        ∀ z x p : EuclideanSpace ℝ (Fin G.n),
          G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 2 * R * ε →
          x ∈ closure Ω → G.mul z x ∈ closure Ω →
          p ∈ {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} →
          G.hnorm (G.mul (-p) x) < ρN / (2 * c0) → G.mul z x ∈ N := by
    intro ρN hρN h2
    have hμpos : (0:ℝ) < μ0 + 2 * R + 2 := by linarith only [hμ0pos, hR]
    obtain ⟨c1, hc1pos, hc1⟩ := G.hnorm_conj_le (μ0 + 2 * R + 2) hμpos
    have hrpos : (0:ℝ) < (G.r : ℝ) := by
      have h : (1:ℝ) ≤ (G.r : ℝ) := by exact_mod_cast G.one_le_r
      linarith only [h]
    have hspos : (0:ℝ) < ρN / (2 * c0) / c1 / 2 := by positivity
    have hBpos : (0:ℝ) < (ρN / (2 * c0) / c1 / 2) ^ ((G.r : ℝ)) :=
      Real.rpow_pos_of_pos hspos _
    have hBcollapse : ((ρN / (2 * c0) / c1 / 2) ^ ((G.r : ℝ))) ^ ((1:ℝ) / G.r)
        = ρN / (2 * c0) / c1 / 2 := by
      rw [← Real.rpow_mul hspos.le, mul_one_div, div_self (ne_of_gt hrpos), Real.rpow_one]
    refine ⟨min 1 (((ρN / (2 * c0) / c1 / 2) ^ ((G.r : ℝ))) ^ (2 * Nat.factorial G.r)
        / (2 * R + 1)),
      lt_min one_pos (div_pos (pow_pos hBpos _) (by linarith only [hR])), ?_⟩
    intro ε hεpos hεlt z x p hz hxcl hzxcl hpE hpd
    have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hεlt (min_le_left _ _))
    have hεB : (2 * R + 1) * ε
        < ((ρN / (2 * c0) / c1 / 2) ^ ((G.r : ℝ))) ^ (2 * Nat.factorial G.r) := by
      have h := lt_of_lt_of_le hεlt (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith only [hR])] at h
      linarith only [h]
    -- `‖z‖ < B`, hence `‖z‖^(1/r) ≤ B^(1/r) = s`
    have hzB : G.hnorm z < (ρN / (2 * c0) / c1 / 2) ^ ((G.r : ℝ)) := by
      refine lt_of_pow_lt_pow_left₀ (2 * Nat.factorial G.r) hBpos.le ?_
      have hzε : G.hnorm z ^ (2 * Nat.factorial G.r) ≤ (2 * R + 1) * ε := by
        have h : 2 * R * ε ≤ (2 * R + 1) * ε := by
          have := mul_le_mul_of_nonneg_right (by linarith only [] : 2 * R ≤ 2 * R + 1) hεpos.le
          linarith only [this]
        linarith only [hz, h]
      linarith only [hzε, hεB]
    have hzrp : G.hnorm z ^ ((1:ℝ) / G.r) ≤ ρN / (2 * c0) / c1 / 2 := by
      have h := Real.rpow_le_rpow (G.hnorm_nonneg z) hzB.le
        (by positivity : (0:ℝ) ≤ (1:ℝ) / G.r)
      rwa [hBcollapse] at h
    -- the two quasi-norm side conditions for `hnorm_conj_le`
    have hznu : G.hnorm z < μ0 + 2 * R + 2 := by
      rcases le_or_gt 1 (G.hnorm z) with h | h
      · have h1 : G.hnorm z ^ 1 ≤ G.hnorm z ^ (2 * Nat.factorial G.r) :=
          pow_le_pow_right₀ h hq1
        rw [pow_one] at h1
        have h2 : 2 * R * ε ≤ 2 * R := by
          have := mul_le_mul_of_nonneg_left hε1 (by linarith only [hR] : (0:ℝ) ≤ 2 * R)
          linarith only [this]
        linarith only [h1, hz, h2, hμ0pos]
      · linarith only [h, hμ0pos, hR]
    have hxnu : G.hnorm x < μ0 + 2 * R + 2 := by
      have h := hμ0b x hxcl
      linarith only [h, hR]
    have hconj := hc1 x z hxnu hznu
    rw [G.mul_assoc] at hconj
    -- `d(z*x, x) ≤ c₁ ‖z‖^(1/r) ≤ ρN/(4 c₀)`
    have hd1 : G.hnorm (G.mul (-x) (G.mul z x)) ≤ ρN / (2 * c0) / 2 := by
      refine hconj.trans ?_
      have h := mul_le_mul_of_nonneg_left hzrp hc1pos.le
      have heq : c1 * (ρN / (2 * c0) / c1 / 2) = ρN / (2 * c0) / 2 := by
        field_simp
      linarith only [h, heq.le, heq.ge]
    -- Euclidean closeness, and conclusion by (2)
    have he1 : ‖G.mul z x - x‖ ≤ c0 * (ρN / (2 * c0) / 2) := by
      refine (h3 (G.mul z x) hzxcl x hxcl).trans ?_
      exact mul_le_mul_of_nonneg_left hd1 hc0pos.le
    have he2 : ‖x - p‖ < c0 * (ρN / (2 * c0)) :=
      lt_of_le_of_lt (h3 x hxcl p (subset_closure hpE.1))
        (mul_lt_mul_of_pos_left hpd hc0pos)
    have heq1 : c0 * (ρN / (2 * c0) / 2) = ρN / 4 := by field_simp; ring
    have heq2 : c0 * (ρN / (2 * c0)) = ρN / 2 := by field_simp
    rw [heq1] at he1
    rw [heq2] at he2
    refine h2 p hpE (G.mul z x) ?_
    have htri : ‖G.mul z x - p‖ ≤ ‖G.mul z x - x‖ + ‖x - p‖ := by
      have h := norm_add_le (G.mul z x - x) (x - p)
      rwa [show G.mul z x - x + (x - p) = G.mul z x - p from by abel] at h
    linarith only [htri, he1, he2, hρN]
  -- Step 3: `SupConvAttainment` at `M_u = M_v = R/2` with the CONSTANT moduli `s ↦ R`.
  -- No `d`-modulus of continuity is constructed: only the attainment clauses are used, and
  -- the constant moduli discharge the node's remaining hypotheses.
  have hatt : ∀ ε : ℝ, 0 < ε →
      (∀ x ∈ ReducedDomain G Ω R ε, ∃ z : EuclideanSpace ℝ (Fin G.n),
        G.mul z x ∈ closure Ω ∧
        SupConv G Ω u ε x
          = u (G.mul z x) - G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) ∧
        G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 4 * ε * (R / 2) ∧
        ∀ x' ∈ ReducedDomain G Ω R ε, G.mul z x' ∈ Ω) ∧
      (∀ x ∈ ReducedDomain G Ω R ε, ∃ z : EuclideanSpace ℝ (Fin G.n),
        G.mul z x ∈ closure Ω ∧
        InfConv G Ω v ε x
          = v (G.mul z x) + G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) ∧
        G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 4 * ε * (R / 2) ∧
        ∀ x' ∈ ReducedDomain G Ω R ε, G.mul z x' ∈ Ω) := by
    intro ε hε
    have hmod : ∀ (w : EuclideanSpace ℝ (Fin G.n) → ℝ),
        (∀ x ∈ closure Ω, |w x| ≤ R / 2) →
        ∀ a ∈ closure Ω, ∀ b ∈ closure Ω,
          |w a - w b| ≤ (fun _ : ℝ => R) (G.hnorm (G.mul (-b) a)) := by
      intro w hw a ha b hb
      have h1 := abs_le.1 (hw a ha)
      have h2 := abs_le.1 (hw b hb)
      rw [abs_le]
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
    obtain ⟨-, hsup2, -, hinf4⟩ := SupConvAttainment G Ω hΩopen hΩbdd u v hucont hvcont
      (R / 2) (R / 2) R hR (by linarith only []) (by linarith only [])
      (fun x hx => (hRb x hx).1) (fun x hx => (hRb x hx).2)
      (fun _ => R) (fun _ => R)
      (hmod u fun x hx => (hRb x hx).1) (hmod v fun x hx => (hRb x hx).2) ε hε
    exact ⟨hsup2, hinf4⟩
  -- Step 4: the one-sided bounds on the two families, which is all the `ciInf`/`ciSup`
  -- steps need -- boundedness and an explicit index, not `Nonempty`.
  have hbddI : ∀ (ε : ℝ), 0 < ε → ∀ x : EuclideanSpace ℝ (Fin G.n),
      BddBelow (Set.range fun p : {p : EuclideanSpace ℝ (Fin G.n) //
          G.mul p x ∈ closure Ω} =>
        v (G.mul p.1 x) + G.hnorm p.1 ^ (2 * Nat.factorial G.r) / (2 * ε)) := by
    intro ε hε x
    refine ⟨-(R / 2), ?_⟩
    rintro b ⟨p, rfl⟩
    have h1 := abs_le.1 ((hRb (G.mul p.1 x) p.2).2)
    have h2 : (0:ℝ) ≤ G.hnorm p.1 ^ (2 * Nat.factorial G.r) / (2 * ε) :=
      div_nonneg (pow_nonneg (G.hnorm_nonneg _) _) (by linarith only [hε])
    linarith only [h1.1, h2]
  have hbddS : ∀ (ε : ℝ), 0 < ε → ∀ x : EuclideanSpace ℝ (Fin G.n),
      BddAbove (Set.range fun p : {p : EuclideanSpace ℝ (Fin G.n) //
          G.mul p x ∈ closure Ω} =>
        u (G.mul p.1 x) - G.hnorm p.1 ^ (2 * Nat.factorial G.r) / (2 * ε)) := by
    intro ε hε x
    refine ⟨R / 2, ?_⟩
    rintro b ⟨p, rfl⟩
    have h1 := abs_le.1 ((hRb (G.mul p.1 x) p.2).1)
    have h2 : (0:ℝ) ≤ G.hnorm p.1 ^ (2 * Nat.factorial G.r) / (2 * ε) :=
      div_nonneg (pow_nonneg (G.hnorm_nonneg _) _) (by linarith only [hε])
    linarith only [h1.2, h2]
  -- Steps 0, 1, 5 and (6a), all shared between the two orientations
  have shared : ∀ x0 ∈ Ω, v x0 < u x0 → ∃ εstar : ℝ, 0 < εstar ∧
      ∀ ε : ℝ, 0 < ε → ε < εstar →
      ∀ x ∈ ReducedDomain G Ω R ε,
        IsMaxOn (fun y => SupConv G Ω u ε y - InfConv G Ω v ε y)
          (closure (ReducedDomain G Ω R ε)) x →
        (∃ D₀ : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
            HasFDerivAt (SupConv G Ω u ε) D₀ x ∧ HasFDerivAt (InfConv G Ω v ε) D₀ x) ∧
        (∀ z : EuclideanSpace ℝ (Fin G.n),
          G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 2 * R * ε →
          G.mul z x ∈ closure Ω → G.mul z x ∈ N) := by
    intro x0 hx0 hlt
    -- Step 0
    have hclne : (closure Ω).Nonempty := ⟨x0, subset_closure hx0⟩
    obtain ⟨xM, hxM, hxMmax⟩ := hclcpt.exists_isMaxOn hclne (hucont.sub hvcont)
    have hM0 : 0 < u xM - v xM := by
      have h : u x0 - v x0 ≤ u xM - v xM := hxMmax (subset_closure hx0)
      linarith only [h, hlt]
    obtain ⟨hEne, hEcpt, hmain, hitem3⟩ :=
      RegularizedPairStandingAssumptions G hc A H hAH Ω hΩopen hΩbdd hΩne u v hucont hvcont
        hsub hsup hbdry R hR hRb xM hxM hxMmax hM0 ((u xM - v xM) / 2) rfl
        {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} rfl
    obtain ⟨ε1, hε1pos, hstand⟩ := hmain
    -- Step 1: one Mathlib call, via the thickening of the compact `E` inside the open `N`
    obtain ⟨ρN, hρNpos, h2⟩ : ∃ ρN > 0,
        ∀ p ∈ {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y},
          ∀ w : EuclideanSpace ℝ (Fin G.n), ‖w - p‖ < ρN → w ∈ N := by
      obtain ⟨δ, hδ, hsub'⟩ := hEcpt.exists_thickening_subset_open hNopen hEN
      refine ⟨δ, hδ, fun p hp w hw => ?_⟩
      refine hsub' (Metric.mem_thickening_iff.2 ⟨p, hp, ?_⟩)
      rwa [dist_eq_norm]
    obtain ⟨ε3, hε3pos, hstep5⟩ := step5 ρN hρNpos h2
    obtain ⟨ε2, hε2pos, hitem3'⟩ := hitem3 (ρN / (2 * c0)) (by positivity)
    refine ⟨min ε1 (min ε2 ε3), lt_min hε1pos (lt_min hε2pos hε3pos), ?_⟩
    intro ε hεpos hεlt x hx hxmax
    have hεlt1 : ε < ε1 := lt_of_lt_of_le hεlt (min_le_left _ _)
    have hεlt2 : ε < ε2 := lt_of_lt_of_le hεlt ((min_le_right _ _).trans (min_le_left _ _))
    have hεlt3 : ε < ε3 := lt_of_lt_of_le hεlt ((min_le_right _ _).trans (min_le_right _ _))
    -- display (1): adding the constant `τ` does not move the argmax
    have hxmaxt : IsMaxOn (fun y => SupConv G Ω u ε y
        - (InfConv G Ω v ε y + (u xM - v xM) / 2))
        (closure (ReducedDomain G Ω R ε)) x := by
      intro y hy
      have h : SupConv G Ω u ε y - InfConv G Ω v ε y
          ≤ SupConv G Ω u ε x - InfConv G Ω v ε x := hxmax hy
      show SupConv G Ω u ε y - (InfConv G Ω v ε y + (u xM - v xM) / 2)
          ≤ SupConv G Ω u ε x - (InfConv G Ω v ε x + (u xM - v xM) / 2)
      linarith only [h]
    obtain ⟨-, -, -, husc, hvsc, -, -, -, -, -⟩ :=
      hstand ε hεpos hεlt1 (SupConv G Ω u ε)
        (fun y => InfConv G Ω v ε y + (u xM - v xM) / 2) rfl rfl
    -- (6a)
    obtain ⟨D₀, hD0u, hD0v⟩ :=
      (SemiConvexDiffAtMax (ReducedDomain G Ω R ε) (SupConv G Ω u ε)
        (fun y => InfConv G Ω v ε y + (u xM - v xM) / 2) husc hvsc).2 x hx
        (hxmaxt.on_subset subset_closure)
    have hD0v' : HasFDerivAt (InfConv G Ω v ε) D₀ x := by
      have h := hD0v.sub_const ((u xM - v xM) / 2)
      simpa using h
    refine ⟨⟨D₀, hD0u, hD0v'⟩, fun z hz hzcl => ?_⟩
    obtain ⟨p, hpE, hpd⟩ := hitem3' ε hεpos hεlt2 x hx hxmaxt
    exact hstep5 ε hεpos hεlt3 z x p hz (subset_closure hx.1) hzcl hpE hpd
  -- the two orientations
  refine ⟨?_, ?_⟩
  · -- part (1): `v` is `C¹` with non-vanishing horizontal gradient near `E`
    rintro ⟨hC1, hnv⟩ x0 hx0
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨εstar, hεstarpos, hkey⟩ := shared x0 hx0 hcon
    refine absurd (ComparisonUnderNondegeneracy G hc A H hAH Ω hΩopen hΩbdd hΩne u v
      hucont hvcont hsub hsup hbdry R hR hRb (fun k => εstar / (k + 2))
      (fun k => by positivity) ?_ ?_ x0 hx0) (not_le.2 hcon)
    · refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    · intro k x hx hxmax D hD
      have hεk : (0:ℝ) < εstar / (k + 2) := by positivity
      have hεklt : εstar / (k + 2) < εstar := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith only [hεstarpos]
      obtain ⟨⟨D₀, hD0u, hD0v⟩, hzN⟩ := hkey _ hεk hεklt x hx hxmax
      obtain ⟨-, hinf4⟩ := hatt _ hεk
      obtain ⟨z, hzcl, hzid, hzbd, hzx'⟩ := hinf4 x hx
      have hzbd' : G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 2 * R * (εstar / (k + 2)) := by
        linarith only [hzbd]
      have hzxN : G.mul z x ∈ N := hzN z hzbd' hzcl
      obtain ⟨D', hD', hD'ne⟩ := transport v hC1 hnv z x hzxN
      -- display (5): the infimum is `≤` each member of its family
      have hle : ∀ y ∈ ReducedDomain G Ω R (εstar / (k + 2)),
          InfConv G Ω v (εstar / (k + 2)) y
            ≤ v (G.mul z y) + G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * (εstar / (k + 2))) := by
        intro y hy
        exact ciInf_le (hbddI _ hεk y)
          (⟨z, subset_closure (hzx' y hy)⟩ : {p : EuclideanSpace ℝ (Fin G.n) //
            G.mul p y ∈ closure Ω})
      have hD0eq : D₀ = D' :=
        touch (InfConv G Ω v (εstar / (k + 2)))
          (fun y => v (G.mul z y)
            + G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * (εstar / (k + 2))))
          (ReducedDomain G Ω R (εstar / (k + 2))) x D₀ D'
          (hrd4 _ hεk) hx hle hzid hD0v (hD'.add_const _)
      have hDD0 : D = D₀ := hD.unique hD0u
      rw [hDD0, hD0eq]
      exact hD'ne
  · -- part (2): `u` is `C¹` with non-vanishing horizontal gradient near `E`
    rintro ⟨hC1, hnv⟩ x0 hx0
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨εstar, hεstarpos, hkey⟩ := shared x0 hx0 hcon
    refine absurd (ComparisonUnderNondegeneracy G hc A H hAH Ω hΩopen hΩbdd hΩne u v
      hucont hvcont hsub hsup hbdry R hR hRb (fun k => εstar / (k + 2))
      (fun k => by positivity) ?_ ?_ x0 hx0) (not_le.2 hcon)
    · refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    · intro k x hx hxmax D hD
      have hεk : (0:ℝ) < εstar / (k + 2) := by positivity
      have hεklt : εstar / (k + 2) < εstar := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith only [hεstarpos]
      obtain ⟨⟨D₀, hD0u, hD0v⟩, hzN⟩ := hkey _ hεk hεklt x hx hxmax
      obtain ⟨hsup2, -⟩ := hatt _ hεk
      obtain ⟨z, hzcl, hzid, hzbd, hzx'⟩ := hsup2 x hx
      have hzbd' : G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 2 * R * (εstar / (k + 2)) := by
        linarith only [hzbd]
      have hzxN : G.mul z x ∈ N := hzN z hzbd' hzcl
      obtain ⟨D', hD', hD'ne⟩ := transport u hC1 hnv z x hzxN
      -- the mirror of display (5): the supremum is `≥` each member of its family
      have hle : ∀ y ∈ ReducedDomain G Ω R (εstar / (k + 2)),
          u (G.mul z y) - G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * (εstar / (k + 2)))
            ≤ SupConv G Ω u (εstar / (k + 2)) y := by
        intro y hy
        exact le_ciSup (hbddS _ hεk y)
          (⟨z, subset_closure (hzx' y hy)⟩ : {p : EuclideanSpace ℝ (Fin G.n) //
            G.mul p y ∈ closure Ω})
      have hD0eq : D' = D₀ :=
        touch (fun y => u (G.mul z y)
            - G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * (εstar / (k + 2))))
          (SupConv G Ω u (εstar / (k + 2)))
          (ReducedDomain G Ω R (εstar / (k + 2))) x D' D₀
          (hrd4 _ hεk) hx hle hzid.symm (hD'.sub_const _) hD0u
      have hDD0 : D = D₀ := hD.unique hD0u
      rw [hDD0, ← hD0eq]
      exact hD'ne
