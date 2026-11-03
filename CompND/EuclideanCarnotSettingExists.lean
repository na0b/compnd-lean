import CompND.CarnotSetting

/-- The Euclidean additive group on `ℝᴺ`, with the constant frame `σⁱ(x) = eᵢ`, is a
Carnot setting: every field of `CarnotSetting` is dischargeable there. This is the
proviso of item 3 of the paper's note for the formalization, and the non-vacuity guard
for the setting. -/
theorem EuclideanCarnotSettingExists (N : ℕ) :
    ∃ G : CarnotSetting,
      G.n = N ∧ G.m = N ∧ G.r = 1 ∧
      (∀ x y, G.mul x y = x + y) ∧
      (∀ x, G.hnorm x = ‖x‖) ∧
      (∀ x, G.hexp (G.pi1 x) = x) ∧
      (∀ x i, G.sig x i = G.hexp (EuclideanSpace.single i (1 : ℝ))) := by
  -- (a) Each frame field lies in the Lie hull: the easy inclusion, valid in every
  -- admissible family, and the only one Hörmander's condition needs here.
  have hframe : ∀ i : Fin N,
      (fun _ : EuclideanSpace ℝ (Fin N) => EuclideanSpace.single i (1 : ℝ)) ∈
        LieHull (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
          EuclideanSpace.single i (1 : ℝ)) := by
    intro i S hS
    exact hS.1 i
  -- (b) The frame is the standard orthonormal basis, hence linearly independent.
  have hindep : LinearIndependent ℝ (fun i : Fin N => EuclideanSpace.single i (1 : ℝ)) := by
    have h : (fun i : Fin N => EuclideanSpace.single i (1 : ℝ))
        = ((EuclideanSpace.basisFun (Fin N) ℝ) : Fin N → EuclideanSpace ℝ (Fin N)) := by
      funext i; simp [EuclideanSpace.basisFun_apply]
    rw [h]
    exact (EuclideanSpace.basisFun (Fin N) ℝ).toBasis.linearIndependent
  -- (c) Hörmander's rank condition eq:horcond.
  have hspan : ∀ x : EuclideanSpace ℝ (Fin N),
      Submodule.span ℝ
        ((fun V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) => V x) ''
          LieHull (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
            EuclideanSpace.single i (1 : ℝ))) = ⊤ := by
    intro x
    have hsub : Set.range (fun i : Fin N => EuclideanSpace.single i (1 : ℝ)) ⊆
        (fun V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) => V x) ''
          LieHull (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
            EuclideanSpace.single i (1 : ℝ)) := by
      rintro v ⟨i, rfl⟩
      exact ⟨_, hframe i, rfl⟩
    have hbasis : Submodule.span ℝ
        (Set.range fun i : Fin N => EuclideanSpace.single i (1 : ℝ)) = ⊤ := by
      have hrange : (Set.range fun i : Fin N => EuclideanSpace.single i (1 : ℝ))
          = Set.range ((EuclideanSpace.basisFun (Fin N) ℝ) :
              Fin N → EuclideanSpace ℝ (Fin N)) := by
        refine congrArg Set.range (funext fun i => ?_)
        simp [EuclideanSpace.basisFun_apply]
      rw [hrange]
      exact (EuclideanSpace.basisFun (Fin N) ℝ).toBasis.span_eq
    exact top_unique (hbasis.ge.trans (Submodule.span_mono hsub))
  -- (d) The correction matrix 𝓜 of eq:Mxz vanishes for a constant frame.
  have hMfield : ∀ (x : EuclideanSpace ℝ (Fin N)) (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      Mfield (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
        EuclideanSpace.single i (1 : ℝ)) x D = 0 := by
    intro x D
    ext i j
    simp [Mfield, fderiv_const_apply]
  -- (e) Components of the horizontal gradient for the constant frame.
  have hhg : ∀ (x : EuclideanSpace ℝ (Fin N)) (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (i : Fin N),
      hgrad (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
        EuclideanSpace.single i (1 : ℝ)) x D i = D (EuclideanSpace.single i (1 : ℝ)) := by
    intro x D i
    simp [hgrad]
  -- (f) The pairing identity ∑ᵢ D(eᵢ) gᵢ = D g.
  have hpair : ∀ (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) (g : EuclideanSpace ℝ (Fin N)),
      ∑ i, D (EuclideanSpace.single i (1 : ℝ)) * g i = D g := by
    intro D g
    have hg : g = ∑ i, g i • EuclideanSpace.single i (1 : ℝ) := by
      ext j; simp [Pi.single_apply, Finset.sum_ite_eq]
    calc ∑ i, D (EuclideanSpace.single i (1 : ℝ)) * g i
        = ∑ i, D (g i • EuclideanSpace.single i (1 : ℝ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul]; simp [mul_comm]
      _ = D (∑ i, g i • EuclideanSpace.single i (1 : ℝ)) := (map_sum D _ _).symm
      _ = D g := by rw [← hg]
  -- (g) eq:taylor2 is the definition of the Fréchet derivative.
  have htaylor : ∀ (u : EuclideanSpace ℝ (Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N))
      (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ), HasFDerivAt u D x →
      HasPansuGradAt (fun a b : EuclideanSpace ℝ (Fin N) => a + b)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N)))
        (fun a : EuclideanSpace ℝ (Fin N) => ‖a‖) u x
        (hgrad (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
          EuclideanSpace.single i (1 : ℝ)) x D) := by
    intro u x D hu ε hε
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (hu.isLittleO.def hε)
    refine ⟨δ, hδ, fun g hg => ?_⟩
    have hd : dist (x + g) x < δ := by
      rw [dist_eq_norm]; simpa using hg
    have h2 := h hd
    rw [add_sub_cancel_left] at h2
    have hs : ∑ i, (hgrad (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
          EuclideanSpace.single i (1 : ℝ)) x D) i
        * ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N))) g) i = D g := by
      simp only [ContinuousLinearMap.coe_id', id_eq]
      rw [← hpair D g]
      exact Finset.sum_congr rfl fun i _ => by rw [hhg]
    rw [hs]
    simpa [Real.norm_eq_abs] using h2
  -- (h) Left-invariance of the horizontal derivatives: for the additive group the jet
  -- transport is the identity, since `DL_h = I` and `D²L_h = 0`.
  have hleft : ∀ (h x : EuclideanSpace ℝ (Fin N)) (φ : EuclideanSpace ℝ (Fin N) → ℝ)
      (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt φ (h + x) D B →
      ∃ (D' : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (B' : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
        TwiceDiffAt (fun y => φ (h + y)) x D' B' ∧
        hgrad (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
            EuclideanSpace.single i (1 : ℝ)) x D'
          = hgrad (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
            EuclideanSpace.single i (1 : ℝ)) (h + x) D ∧
        hhessS (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
            EuclideanSpace.single i (1 : ℝ)) x D' B'
          = hhessS (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
            EuclideanSpace.single i (1 : ℝ)) (h + x) D B := by
    intro h x φ D B hφ
    refine ⟨D, B, ⟨hφ.1, fun ε hε => ?_⟩, rfl, by simp [hhessS, hMfield]⟩
    obtain ⟨δ, hδ, hb⟩ := hφ.2 ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hy' : ‖(h + y) - (h + x)‖ < δ := by
      rw [add_sub_add_left_eq_sub]; exact hy
    have hres := hb (h + y) hy'
    rw [add_sub_add_left_eq_sub] at hres
    exact hres
  -- (i) The form of the Xᵢ on functions of the first layer: here π₁ is the identity.
  have hpi1 : ∀ (ψ : EuclideanSpace ℝ (Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N))
      (Ej : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
      (C : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
      TwiceDiffAt ψ ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N))) x) Ej C →
      ∃ (D : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ),
        TwiceDiffAt
            (fun y => ψ ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N))) y)) x D B ∧
        hgrad (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
            EuclideanSpace.single i (1 : ℝ)) x D
          = (EuclideanSpace.equiv (Fin N) ℝ).symm
            (fun i => Ej (EuclideanSpace.single i (1 : ℝ))) ∧
        hhessS (fun (_ : EuclideanSpace ℝ (Fin N)) (i : Fin N) =>
            EuclideanSpace.single i (1 : ℝ)) x D B
          = Matrix.of fun i j =>
            C (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
    intro ψ x Ej C hψ
    exact ⟨Ej, C, hψ, rfl, by simp [hhessS, hMfield]⟩
  -- The witness.
  refine ⟨{ n := N, m := N, r := 1
          , one_le_r := le_refl 1
          , mul := fun x y => x + y
          , mul_assoc := fun x y z => add_assoc x y z
          , mul_zero := fun x => add_zero x
          , zero_mul := fun x => zero_add x
          , mul_neg := fun x => by simp
          , neg_mul := fun x => by simp
          , mul_smooth := contDiff_fst.add contDiff_snd
          , pi1 := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N))
          , pi1_mul := fun x y => by simp
          , hexp := id
          , hexp_cont := continuous_id
          , pi1_hexp := fun ζ => by simp
          , abelian_of_step_one := fun _ x y => add_comm x y
          , hnorm := fun x => ‖x‖
          , hnorm_nonneg := fun x => norm_nonneg x
          , hnorm_eq_zero := fun x => norm_eq_zero
          , hnorm_neg := fun x => norm_neg x
          , hnorm_cont := continuous_norm
          , hnorm_hexp := fun ζ => rfl
          , hnorm_pow_smooth := by
              simpa using contDiff_norm_sq (E := EuclideanSpace ℝ (Fin N)) ℝ
          , hnorm_mul_le := fun ν _ => ⟨1, one_pos, fun x y _ _ => by
              simpa using norm_add_le x y⟩
          , hnorm_conj_le := fun ν _ => ⟨1, one_pos, fun x y _ _ => by
              have hxy : (-x + y) + x = y := by abel
              rw [hxy]
              simp⟩
          , holder_equiv := fun ν _ => ⟨1, one_pos, fun x y _ _ => by
              refine ⟨?_, ?_⟩
              · rw [neg_add_eq_sub]; simp
              · rw [neg_add_eq_sub]; simp⟩
          , ball_connected := fun x ρ hρ => by
              have hset : {y : EuclideanSpace ℝ (Fin N) | ‖-x + y‖ < ρ} = Metric.ball x ρ := by
                ext y
                simp [Metric.mem_ball, dist_eq_norm, neg_add_eq_sub]
              rw [hset]
              exact ⟨Metric.nonempty_ball.mpr hρ, (convex_ball x ρ).isPreconnected⟩
          , hnorm_proper := fun C => by
              have h : {x : EuclideanSpace ℝ (Fin N) | ‖x‖ ≤ C} ⊆ Metric.closedBall 0 C := by
                intro x hx; simpa [Metric.mem_closedBall] using hx
              exact Metric.isBounded_closedBall.subset h
          , sig := fun _ i => EuclideanSpace.single i (1 : ℝ)
          , sig_smooth := fun _ => contDiff_const
          , sig_indep := fun _ => hindep
          , hormander := hspan
          , taylor2 := htaylor
          , leftJet := hleft
          , pi1Jet := hpi1 },
      rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
