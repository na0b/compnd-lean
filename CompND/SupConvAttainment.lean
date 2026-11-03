import CompND.ReducedDomain
import CompND.InverseUniquenessAndDistanceSymmetry
import CompND.SupConv
import CompND.InfConv

/-- Part (4) of lem:wang, exactly as printed, on `Ω[ε]`: the sup- and inf-convolutions
inherit the moduli of continuity of `u` and `v` on `Ω[ε]`, the extremum is attained at some
`z` with `‖z‖ ^ q ≤ 4 ε ‖u‖_∞`, and `z * x' ∈ Ω` for every `x' ∈ Ω[ε]`. -/
theorem SupConvAttainment (G : CarnotSetting)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hu : ContinuousOn u (closure Ω)) (hv : ContinuousOn v (closure Ω))
    (Mu Mv R : ℝ) (hR : 0 ≤ R) (hMu : 2 * Mu ≤ R) (hMv : 2 * Mv ≤ R)
    (hub : ∀ x ∈ closure Ω, |u x| ≤ Mu) (hvb : ∀ x ∈ closure Ω, |v x| ≤ Mv)
    (ωu ωv : ℝ → ℝ)
    (hωu : ∀ a ∈ closure Ω, ∀ b ∈ closure Ω, |u a - u b| ≤ ωu (G.hnorm (G.mul (-b) a)))
    (hωv : ∀ a ∈ closure Ω, ∀ b ∈ closure Ω, |v a - v b| ≤ ωv (G.hnorm (G.mul (-b) a)))
    (ε : ℝ) (hε : 0 < ε) :
    (∀ x ∈ ReducedDomain G Ω R ε, ∀ x' ∈ ReducedDomain G Ω R ε,
      |SupConv G Ω u ε x - SupConv G Ω u ε x'| ≤ ωu (G.hnorm (G.mul (-x') x))) ∧
    (∀ x ∈ ReducedDomain G Ω R ε, ∃ z : EuclideanSpace ℝ (Fin G.n),
      G.mul z x ∈ closure Ω ∧
      SupConv G Ω u ε x = u (G.mul z x) - G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) ∧
      G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 4 * ε * Mu ∧
      ∀ x' ∈ ReducedDomain G Ω R ε, G.mul z x' ∈ Ω) ∧
    (∀ x ∈ ReducedDomain G Ω R ε, ∀ x' ∈ ReducedDomain G Ω R ε,
      |InfConv G Ω v ε x - InfConv G Ω v ε x'| ≤ ωv (G.hnorm (G.mul (-x') x))) ∧
    (∀ x ∈ ReducedDomain G Ω R ε, ∃ z : EuclideanSpace ℝ (Fin G.n),
      G.mul z x ∈ closure Ω ∧
      InfConv G Ω v ε x = v (G.mul z x) + G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) ∧
      G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 4 * ε * Mv ∧
      ∀ x' ∈ ReducedDomain G Ω R ε, G.mul z x' ∈ Ω) := by
  -- Step 0: the group identities, all used repeatedly.  (0a) is the cancellation that makes
  -- `z ↦ z * x` and `y ↦ y * (-x)` mutually inverse.
  have hcancel1 : ∀ a x : EuclideanSpace ℝ (Fin G.n), G.mul (G.mul a (-x)) x = a := by
    intro a x
    rw [G.mul_assoc, G.neg_mul, G.mul_zero]
  have hcancel2 : ∀ a x : EuclideanSpace ℝ (Fin G.n), G.mul (G.mul a x) (-x) = a := by
    intro a x
    rw [G.mul_assoc, G.mul_neg, G.mul_zero]
  -- the inverse-of-a-product identity `-(a * b) = (-b) * (-a)` of pm-0015(1) and the
  -- symmetry of `d`, both from uniqueness of inverses in the group axioms
  obtain ⟨-, hnegmul, hdsymm⟩ := InverseUniquenessAndDistanceSymmetry G
  -- (0b) the left-invariance of `d`
  have hleftinv : ∀ a x x' : EuclideanSpace ℝ (Fin G.n),
      G.hnorm (G.mul (-(G.mul a x')) (G.mul a x)) = G.hnorm (G.mul (-x') x) := by
    intro a x x'
    congr 1
    rw [hnegmul a x', G.mul_assoc, ← G.mul_assoc (-a) a x, G.neg_mul, G.zero_mul]
  have hqne : (2 * Nat.factorial G.r) ≠ 0 := by
    have h := Nat.factorial_pos G.r
    omega
  have hε2 : (0:ℝ) < 2 * ε := by linarith only [hε]
  have hpennn : ∀ z : EuclideanSpace ℝ (Fin G.n),
      (0:ℝ) ≤ G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) :=
    fun z => div_nonneg (pow_nonneg (G.hnorm_nonneg z) _) hε2.le
  -- Step 1: the index set `Z_x = {z | z * x ∈ closure Ω}` is compact, and non-empty for
  -- `x ∈ Ω`.  `Z_x` is the image of the compact `closure Ω` under `y ↦ y * (-x)` by (0a).
  have hclcpt : IsCompact (closure Ω) := hΩbdd.isCompact_closure
  have htrcont : ∀ x : EuclideanSpace ℝ (Fin G.n),
      Continuous fun z : EuclideanSpace ℝ (Fin G.n) => G.mul z x := fun x =>
    G.mul_smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have hZcpt : ∀ x : EuclideanSpace ℝ (Fin G.n),
      IsCompact {z : EuclideanSpace ℝ (Fin G.n) | G.mul z x ∈ closure Ω} := by
    intro x
    have himg : {z : EuclideanSpace ℝ (Fin G.n) | G.mul z x ∈ closure Ω}
        = (fun y : EuclideanSpace ℝ (Fin G.n) => G.mul y (-x)) '' closure Ω := by
      ext z
      refine ⟨fun hz => ⟨G.mul z x, hz, hcancel2 z x⟩, ?_⟩
      intro hz
      obtain ⟨y, hy, hyz⟩ := hz
      show G.mul z x ∈ closure Ω
      rw [← hyz, hcancel1 y x]
      exact hy
    rw [himg]
    exact hclcpt.image
      (G.mul_smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hZ0 : ∀ x ∈ Ω,
      (0 : EuclideanSpace ℝ (Fin G.n)) ∈ {z : EuclideanSpace ℝ (Fin G.n) |
        G.mul z x ∈ closure Ω} := by
    intro x hx
    show G.mul 0 x ∈ closure Ω
    rw [G.zero_mul]
    exact subset_closure hx
  have hZne : ∀ x ∈ Ω,
      ({z : EuclideanSpace ℝ (Fin G.n) | G.mul z x ∈ closure Ω}).Nonempty :=
    fun x hx => ⟨0, hZ0 x hx⟩
  -- the two objective functions are continuous on `Z_x`
  have hPhicont : ∀ (w : EuclideanSpace ℝ (Fin G.n) → ℝ), ContinuousOn w (closure Ω) →
      ∀ x : EuclideanSpace ℝ (Fin G.n),
      ContinuousOn (fun z => w (G.mul z x)
          - G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε))
        {z : EuclideanSpace ℝ (Fin G.n) | G.mul z x ∈ closure Ω} := by
    intro w hw x
    refine ContinuousOn.sub (hw.comp (htrcont x).continuousOn fun z hz => hz) ?_
    exact ((G.hnorm_cont.pow _).div_const _).continuousOn
  have hPsicont : ∀ (w : EuclideanSpace ℝ (Fin G.n) → ℝ), ContinuousOn w (closure Ω) →
      ∀ x : EuclideanSpace ℝ (Fin G.n),
      ContinuousOn (fun z => w (G.mul z x)
          + G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε))
        {z : EuclideanSpace ℝ (Fin G.n) | G.mul z x ∈ closure Ω} := by
    intro w hw x
    refine ContinuousOn.add (hw.comp (htrcont x).continuousOn fun z hz => hz) ?_
    exact ((G.hnorm_cont.pow _).div_const _).continuousOn
  -- the two one-sided bounds on the families.  `Real.sSup`/`Real.sInf` of an unbounded or
  -- empty family is `0` by convention, so these are load-bearing; and they need no
  -- compactness, only `|u| ≤ M_u` on `closure Ω` and the non-negativity of the penalty.
  have hbddA : ∀ x : EuclideanSpace ℝ (Fin G.n),
      BddAbove (Set.range fun z : {z : EuclideanSpace ℝ (Fin G.n) //
          G.mul z x ∈ closure Ω} =>
        u (G.mul z.1 x) - G.hnorm z.1 ^ (2 * Nat.factorial G.r) / (2 * ε)) := by
    intro x
    refine ⟨Mu, ?_⟩
    rintro b ⟨z, rfl⟩
    have h1 := abs_le.1 (hub (G.mul z.1 x) z.2)
    linarith only [h1.2, hpennn z.1]
  have hbddB : ∀ x : EuclideanSpace ℝ (Fin G.n),
      BddBelow (Set.range fun z : {z : EuclideanSpace ℝ (Fin G.n) //
          G.mul z x ∈ closure Ω} =>
        v (G.mul z.1 x) + G.hnorm z.1 ^ (2 * Nat.factorial G.r) / (2 * ε)) := by
    intro x
    refine ⟨-Mv, ?_⟩
    rintro b ⟨z, rfl⟩
    have h1 := abs_le.1 (hvb (G.mul z.1 x) z.2)
    linarith only [h1.1, hpennn z.1]
  -- the `BddBelow` for `ReducedDomain`'s infimum, used in (3b)
  have hbddRD : ∀ x : EuclideanSpace ℝ (Fin G.n),
      BddBelow (Set.range fun y : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω} =>
        G.hnorm (G.mul y.1 (-x)) ^ (2 * Nat.factorial G.r)) := by
    intro x
    refine ⟨0, ?_⟩
    rintro b ⟨y, rfl⟩
    exact pow_nonneg (G.hnorm_nonneg _) _
  -- the arithmetic of (3b), shared by both sides
  have h3b : ∀ M : ℝ, 2 * M ≤ R → ∀ t : ℝ, t ≤ 4 * ε * M → t < (1 + 4 * R) * ε := by
    intro M hM t ht
    have h1 : 4 * ε * M ≤ 2 * ε * R := by
      have h := mul_le_mul_of_nonneg_left hM hε.le
      linarith only [h]
    have h2 : (0:ℝ) < ε * (1 + 2 * R) := mul_pos hε (by linarith only [hR])
    linarith only [ht, h1, h2]
  -- the (3b) contradiction, shared by both sides
  have hinΩ : ∀ (z : EuclideanSpace ℝ (Fin G.n)) (M : ℝ), 2 * M ≤ R →
      G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 4 * ε * M →
      ∀ x' ∈ ReducedDomain G Ω R ε, G.mul z x' ∈ Ω := by
    intro z M hM hbound x' hx'
    by_contra hcontra
    have hinf := ciInf_le (hbddRD x')
      (⟨G.mul z x', hcontra⟩ : {y : EuclideanSpace ℝ (Fin G.n) // y ∉ Ω})
    rw [hcancel2 z x'] at hinf
    have hlt := hx'.2
    have hgap := h3b M hM _ hbound
    linarith only [hlt, hinf, hgap]
  -- Steps 2 and 3: the maximizer package.  Hoisted, because conjunct (1) consumes
  -- conjunct (2)'s witness and a `refine` bullet cannot see a sibling bullet.
  have hmaxu : ∀ x ∈ ReducedDomain G Ω R ε, ∃ z : EuclideanSpace ℝ (Fin G.n),
      G.mul z x ∈ closure Ω ∧
      SupConv G Ω u ε x = u (G.mul z x) - G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) ∧
      G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 4 * ε * Mu ∧
      ∀ x' ∈ ReducedDomain G Ω R ε, G.mul z x' ∈ Ω := by
    intro x hx
    have hxΩ : x ∈ Ω := hx.1
    have hne : Nonempty {z : EuclideanSpace ℝ (Fin G.n) // G.mul z x ∈ closure Ω} :=
      ⟨⟨0, hZ0 x hxΩ⟩⟩
    obtain ⟨z, hzZ, hzmax⟩ := (hZcpt x).exists_isMaxOn (hZne x hxΩ) (hPhicont u hu x)
    have hid : SupConv G Ω u ε x
        = u (G.mul z x) - G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) := by
      refine le_antisymm (ciSup_le fun z' => hzmax z'.2) ?_
      exact le_ciSup (hbddA x)
        (⟨z, hzZ⟩ : {z : EuclideanSpace ℝ (Fin G.n) // G.mul z x ∈ closure Ω})
    -- (3a) the bound `‖z‖^q ≤ 4 ε M_u`, by comparing with `z' = 0`
    have hcmp := hzmax (hZ0 x hxΩ)
    have hcmp' : u (G.mul 0 x) - G.hnorm (0 : EuclideanSpace ℝ (Fin G.n)) ^
          (2 * Nat.factorial G.r) / (2 * ε)
        ≤ u (G.mul z x) - G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) := hcmp
    rw [G.zero_mul, (G.hnorm_eq_zero 0).2 rfl, zero_pow hqne, zero_div] at hcmp'
    have hub1 := abs_le.1 (hub (G.mul z x) hzZ)
    have hub2 := abs_le.1 (hub x (subset_closure hxΩ))
    have hbound : G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 4 * ε * Mu := by
      have hdiv : G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) ≤ 2 * Mu := by
        linarith only [hcmp', hub1.2, hub2.1]
      rw [div_le_iff₀ hε2] at hdiv
      linarith only [hdiv]
    exact ⟨z, hzZ, hid, hbound, hinΩ z Mu hMu hbound⟩
  -- Steps 2 and 5: the minimizer package, the mirror image
  have hminv : ∀ x ∈ ReducedDomain G Ω R ε, ∃ z : EuclideanSpace ℝ (Fin G.n),
      G.mul z x ∈ closure Ω ∧
      InfConv G Ω v ε x = v (G.mul z x) + G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) ∧
      G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 4 * ε * Mv ∧
      ∀ x' ∈ ReducedDomain G Ω R ε, G.mul z x' ∈ Ω := by
    intro x hx
    have hxΩ : x ∈ Ω := hx.1
    have hne : Nonempty {z : EuclideanSpace ℝ (Fin G.n) // G.mul z x ∈ closure Ω} :=
      ⟨⟨0, hZ0 x hxΩ⟩⟩
    obtain ⟨z, hzZ, hzmin⟩ := (hZcpt x).exists_isMinOn (hZne x hxΩ) (hPsicont v hv x)
    have hid : InfConv G Ω v ε x
        = v (G.mul z x) + G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) := by
      refine le_antisymm ?_ (le_ciInf fun z' => hzmin z'.2)
      exact ciInf_le (hbddB x)
        (⟨z, hzZ⟩ : {z : EuclideanSpace ℝ (Fin G.n) // G.mul z x ∈ closure Ω})
    have hcmp := hzmin (hZ0 x hxΩ)
    have hcmp' : v (G.mul z x) + G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε)
        ≤ v (G.mul 0 x) + G.hnorm (0 : EuclideanSpace ℝ (Fin G.n)) ^
          (2 * Nat.factorial G.r) / (2 * ε) := hcmp
    rw [G.zero_mul, (G.hnorm_eq_zero 0).2 rfl, zero_pow hqne, zero_div] at hcmp'
    have hvb1 := abs_le.1 (hvb (G.mul z x) hzZ)
    have hvb2 := abs_le.1 (hvb x (subset_closure hxΩ))
    have hbound : G.hnorm z ^ (2 * Nat.factorial G.r) ≤ 4 * ε * Mv := by
      have hdiv : G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) ≤ 2 * Mv := by
        linarith only [hcmp', hvb1.1, hvb2.2]
      rw [div_le_iff₀ hε2] at hdiv
      linarith only [hdiv]
    exact ⟨z, hzZ, hid, hbound, hinΩ z Mv hMv hbound⟩
  -- Step 4: the one-sided modulus estimate for `u^ε`.  Note this uses only `le_ciSup` at
  -- `x'` -- `BddAbove` alone -- and so does NOT redo Step 1 or Step 2 at `x'`; a legitimate
  -- shortening of the `.tex`'s route, which invokes "the second assertion of Step 2 at x'".
  have honeu : ∀ x ∈ ReducedDomain G Ω R ε, ∀ x' ∈ ReducedDomain G Ω R ε,
      SupConv G Ω u ε x - SupConv G Ω u ε x' ≤ ωu (G.hnorm (G.mul (-x') x)) := by
    intro x hx x' hx'
    obtain ⟨z, hzZ, hid, hbound, hzx'⟩ := hmaxu x hx
    have hzx'cl : G.mul z x' ∈ closure Ω := subset_closure (hzx' x' hx')
    have hge : u (G.mul z x') - G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε)
        ≤ SupConv G Ω u ε x' :=
      le_ciSup (hbddA x')
        (⟨z, hzx'cl⟩ : {z : EuclideanSpace ℝ (Fin G.n) // G.mul z x' ∈ closure Ω})
    have hmodu := hωu (G.mul z x) hzZ (G.mul z x') hzx'cl
    rw [hleftinv z x x'] at hmodu
    have h1 : u (G.mul z x) - u (G.mul z x') ≤ ωu (G.hnorm (G.mul (-x') x)) :=
      le_trans (le_abs_self _) hmodu
    rw [hid]
    linarith only [hge, h1]
  have honev : ∀ x ∈ ReducedDomain G Ω R ε, ∀ x' ∈ ReducedDomain G Ω R ε,
      InfConv G Ω v ε x' - InfConv G Ω v ε x ≤ ωv (G.hnorm (G.mul (-x) x')) := by
    intro x hx x' hx'
    obtain ⟨z, hzZ, hid, hbound, hzx'⟩ := hminv x hx
    have hzx'cl : G.mul z x' ∈ closure Ω := subset_closure (hzx' x' hx')
    have hle : InfConv G Ω v ε x'
        ≤ v (G.mul z x') + G.hnorm z ^ (2 * Nat.factorial G.r) / (2 * ε) :=
      ciInf_le (hbddB x')
        (⟨z, hzx'cl⟩ : {z : EuclideanSpace ℝ (Fin G.n) // G.mul z x' ∈ closure Ω})
    have hmodv := hωv (G.mul z x') hzx'cl (G.mul z x) hzZ
    rw [hleftinv z x' x] at hmodv
    have h1 : v (G.mul z x') - v (G.mul z x) ≤ ωv (G.hnorm (G.mul (-x) x')) :=
      le_trans (le_abs_self _) hmodv
    rw [hid]
    linarith only [hle, h1]
  refine ⟨?_, hmaxu, ?_, hminv⟩
  · -- conjunct (1): both sides of the modulus estimate for `u^ε`
    intro x hx x' hx'
    rw [abs_le]
    refine ⟨?_, honeu x hx x' hx'⟩
    have h := honeu x' hx' x hx
    rw [hdsymm x' x] at h
    linarith only [h]
  · -- conjunct (3): both sides of the modulus estimate for `v_ε`
    intro x hx x' hx'
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h := honev x hx x' hx'
      rw [hdsymm x' x] at h
      linarith only [h]
    · have h := honev x' hx' x hx
      linarith only [h]
