import CompND.ViscTestLocalization

/-- rem:classical: a viscosity sub-solution (resp. super-solution) that is twice
differentiable at `x` with non-vanishing horizontal gradient there satisfies
`ℒ u (x) ≤ 0` (resp. `≥ 0`) classically. `Ω` bounded and `u ∈ C(closure Ω)` are what make
the test function of the proof constructible. -/
theorem ClassicalAtTwiceDiff (G : CarnotSetting)
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (u : EuclideanSpace ℝ (Fin G.n) → ℝ) (hu : ContinuousOn u (closure Ω))
    (x : EuclideanSpace ℝ (Fin G.n)) (hx : x ∈ Ω)
    (D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ)
    (hjet : TwiceDiffAt u x D B) (hg : hgrad G.sig x D ≠ 0) :
    (IsViscSubsol G A H Ω u → Lop G.sig A H x D B ≤ 0) ∧
    (IsViscSupersol G A H Ω u → 0 ≤ Lop G.sig A H x D B) := by
  -- the Euclidean inner product as a continuous bilinear form
  obtain ⟨I, hI⟩ : ∃ I : EuclideanSpace ℝ (Fin G.n) →L[ℝ] EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
      ∀ h k, I h k = (inner ℝ h k : ℝ) := ⟨innerSL ℝ, fun _ _ => rfl⟩
  have hIself : ∀ h, I h h = ‖h‖ ^ 2 := fun h => by
    rw [hI]; exact real_inner_self_eq_norm_sq h
  have hIsymm : ∀ h k, I h k = I k h := fun h k => by
    rw [hI, hI]; exact real_inner_comm k h
  -- `u` is bounded on `Ω`
  obtain ⟨Cu, hCu⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hu
  have hCu' : ∀ y ∈ Ω, |u y| ≤ Cu := by
    intro y hy
    have := hCu y (subset_closure hy)
    rwa [Real.norm_eq_abs] at this
  have hMu : ∃ Mu : ℝ, ∀ y ∈ Ω, u y ≤ Mu :=
    ⟨Cu, fun y hy => (le_abs_self _).trans (hCu' y hy)⟩
  have hmu : ∃ mu : ℝ, ∀ y ∈ Ω, mu ≤ u y :=
    ⟨-Cu, fun y hy => by linarith [neg_abs_le (u y), hCu' y hy]⟩
  -- a ball inside `Ω`
  obtain ⟨r₀, hr₀, hb₀⟩ := Metric.isOpen_iff.1 hΩo x hx
  -- the perturbed quadratic polynomials
  set φ : ℝ → EuclideanSpace ℝ (Fin G.n) → ℝ :=
    fun c y => u x + D (y - x) + (1 / 2) * ((B + c • I) (y - x)) (y - x) with hφ
  have happ : ∀ (c : ℝ) (h : EuclideanSpace ℝ (Fin G.n)),
      ((B + c • I) h) h = B h h + c * ‖h‖ ^ 2 := by
    intro c h; simp [hIself h]
  have hφC : ∀ c : ℝ, ContDiff ℝ 2 (φ c) := by
    intro c
    have h1 : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin G.n) => (y - x, y - x)) :=
      (contDiff_id.sub contDiff_const).prodMk (contDiff_id.sub contDiff_const)
    have h2 : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin G.n) => ((B + c • I) (y - x)) (y - x)) :=
      ((B + c • I).isBoundedBilinearMap.contDiff.of_le le_top).comp h1
    exact (contDiff_const.add (D.contDiff.comp (contDiff_id.sub contDiff_const))).add
      (contDiff_const.mul h2)
  have hφx : ∀ c : ℝ, φ c x = u x := by
    intro c; simp [hφ]
  have hφjet : ∀ c : ℝ, TwiceDiffAt (φ c) x D (B + c • I) := by
    intro c
    refine ⟨fun p q => ?_, fun ε hε => ⟨1, one_pos, fun y _ => ?_⟩⟩
    · simp [hjet.1 p q, hIsymm p q]
    · have : φ c y - φ c x - D (y - x) - (1 / 2) * ((B + c • I) (y - x)) (y - x) = 0 := by
        rw [hφx c]; simp [hφ]; ring
      rw [this, abs_zero]
      positivity
  have hφdiff : ∀ (c : ℝ) (y : EuclideanSpace ℝ (Fin G.n)),
      u y - φ c y
        = (u y - u x - D (y - x) - (1 / 2) * B (y - x) (y - x)) - (c / 2) * ‖y - x‖ ^ 2 := by
    intro c y
    rw [hφ]
    simp only [happ]
    ring
  -- `Lop` is affine in the second-order jet, with `hgrad` untouched
  set Gm : Matrix (Fin G.m) (Fin G.m) ℝ :=
    Matrix.of fun i j => I (G.sig x i) (G.sig x j) with hGm
  set T : ℝ := (A (hgrad G.sig x D) * Gm).trace with hT
  have halg : ∀ c : ℝ, Lop G.sig A H x D (B + c • I) = Lop G.sig A H x D B - c * T := by
    intro c
    have hh : hhessS G.sig x D (B + c • I) = hhessS G.sig x D B + c • Gm := by
      ext i j
      simp [hhessS, hGm, Matrix.add_apply]
      ring
    rw [Lop, Lop, hh, hT, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_smul, smul_eq_mul]
    ring
  have hTsmall : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ 2 * η * T ≤ ε := by
    intro ε hε
    refine ⟨ε / (2 * (|T| + 1)), by positivity, ?_⟩
    have h1 : (0 : ℝ) < |T| + 1 := by positivity
    have h2 : 2 * (ε / (2 * (|T| + 1))) * T ≤ 2 * (ε / (2 * (|T| + 1))) * |T| := by
      have : (0 : ℝ) ≤ 2 * (ε / (2 * (|T| + 1))) := by positivity
      nlinarith [le_abs_self T]
    have h3 : 2 * (ε / (2 * (|T| + 1))) * |T| ≤ ε := by
      have heq : 2 * (ε / (2 * (|T| + 1))) * |T| = ε * |T| / (|T| + 1) := by
        field_simp
      rw [heq, div_le_iff₀ h1]
      nlinarith [abs_nonneg T, hε.le]
    linarith
  constructor
  · -- sub-solution side
    intro hsub
    obtain ⟨hloc, -⟩ := (ViscTestLocalization G A H Ω u).1 hMu hsub
    have hstep : ∀ η : ℝ, 0 < η → Lop G.sig A H x D B ≤ 2 * η * T := by
      intro η hη
      obtain ⟨δ, hδ, hd⟩ := hjet.2 η hη
      set r : ℝ := min r₀ δ with hr
      have hrpos : 0 < r := lt_min hr₀ hδ
      have hrΩ : Metric.ball x r ⊆ Ω :=
        (Metric.ball_subset_ball (min_le_left _ _)).trans hb₀
      have htouch : ∀ y ∈ Metric.ball x r, u y - φ (2 * η) y ≤ u x - φ (2 * η) x := by
        intro y hy
        have hyδ : ‖y - x‖ < δ := by
          have : dist y x < δ := lt_of_lt_of_le (Metric.mem_ball.1 hy) (min_le_right _ _)
          rwa [dist_eq_norm] at this
        have he := abs_le.1 (hd y hyδ)
        rw [hφx, hφdiff]
        have : (2 * η) / 2 * ‖y - x‖ ^ 2 = η * ‖y - x‖ ^ 2 := by ring
        rw [this]
        linarith [he.2]
      have := hloc x hx (φ (2 * η)) r hrpos hrΩ ((hφC (2 * η)).contDiffOn) htouch
        D (B + (2 * η) • I) (hφjet (2 * η)) hg
      rw [halg (2 * η)] at this
      linarith
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨η, hη, hηT⟩ := hTsmall ε hε
    linarith [hstep η hη]
  · -- super-solution side
    intro hsup
    obtain ⟨hloc, -⟩ := (ViscTestLocalization G A H Ω u).2 hmu hsup
    have hstep : ∀ η : ℝ, 0 < η → -(2 * η * T) ≤ Lop G.sig A H x D B := by
      intro η hη
      obtain ⟨δ, hδ, hd⟩ := hjet.2 η hη
      set r : ℝ := min r₀ δ with hr
      have hrpos : 0 < r := lt_min hr₀ hδ
      have hrΩ : Metric.ball x r ⊆ Ω :=
        (Metric.ball_subset_ball (min_le_left _ _)).trans hb₀
      have htouch : ∀ y ∈ Metric.ball x r, u x - φ (-(2 * η)) x ≤ u y - φ (-(2 * η)) y := by
        intro y hy
        have hyδ : ‖y - x‖ < δ := by
          have : dist y x < δ := lt_of_lt_of_le (Metric.mem_ball.1 hy) (min_le_right _ _)
          rwa [dist_eq_norm] at this
        have he := abs_le.1 (hd y hyδ)
        rw [hφx, hφdiff]
        have : -(2 * η) / 2 * ‖y - x‖ ^ 2 = -(η * ‖y - x‖ ^ 2) := by ring
        rw [this]
        linarith [he.1]
      have := hloc x hx (φ (-(2 * η))) r hrpos hrΩ ((hφC (-(2 * η))).contDiffOn) htouch
        D (B + (-(2 * η)) • I) (hφjet (-(2 * η))) hg
      rw [halg (-(2 * η))] at this
      linarith
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨η, hη, hηT⟩ := hTsmall ε hε
    linarith [hstep η hη]
