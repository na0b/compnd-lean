import CompND.ScalingIdentityAllT
import CompND.NormalizedAH
import CompND.EllipPositiveAndQuadraticTwoHomogeneous

/-- rem:scale(a) and subsec:str: under (E) and (S) the pair `(A, H)` factors as
`A = a • A₀`, `H = a * H₀` with `a > 0` continuous away from the origin and `(A₀, H₀)`
satisfying both the structure conditions and the normalization eq:normal. -/
theorem NormalizationExists {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ)
    (hAH : StructureConditionsES m A H) :
    ∃ (A₀ : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
      (H₀ : EuclideanSpace ℝ (Fin m) → ℝ) (a : EuclideanSpace ℝ (Fin m) → ℝ),
      (∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → 0 < a ξ) ∧
      ContinuousOn a {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} ∧
      (∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → A ξ = a ξ • A₀ ξ) ∧
      (∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → H ξ = a ξ * H₀ ξ) ∧
      StructureConditionsES m A₀ H₀ ∧ NormalizedAH m A₀ H₀ := by
  -- The radial projection `ω ξ = ‖ξ‖⁻¹ • ξ`, written as the plain formula: at the origin
  -- `‖(0 : E)‖ = 0` and `inv_zero` give `ω 0 = 0`, which is the `.tex`'s convention
  -- `|0|⁻¹ = 0`, and no case split is needed because every assertion below -- and every
  -- clause of `StructureConditionsES` and `NormalizedAH` -- quantifies over `ξ ≠ 0` only.
  obtain ⟨om, homdef⟩ : ∃ om : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ∀ ξ, om ξ = ‖ξ‖⁻¹ • ξ := ⟨_, fun _ => rfl⟩
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ,
      ∀ ξ, A₀ ξ = A (om ξ) := ⟨_, fun _ => rfl⟩
  obtain ⟨H₀, hH₀def⟩ : ∃ H₀ : EuclideanSpace ℝ (Fin m) → ℝ,
      ∀ ξ, H₀ ξ = ‖ξ‖ * H (om ξ) := ⟨_, fun _ => rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : EuclideanSpace ℝ (Fin m) → ℝ,
      ∀ ξ, a ξ = Ellip A ξ / (‖ξ‖ ^ 2 * Ellip A (om ξ)) := ⟨_, fun _ => rfl⟩
  have hEllipDef : ∀ η : EuclideanSpace ℝ (Fin m),
      Ellip A η = ∑ i, ∑ j, A η i j * η j * η i := fun _ => rfl
  -- the three facts about `ω` that all five steps run on
  have hnormpos : ∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → 0 < ‖ξ‖ :=
    fun ξ hξ => norm_pos_iff.2 hξ
  have homnorm : ∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → ‖om ξ‖ = 1 := by
    intro ξ hξ
    rw [homdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (ne_of_gt (hnormpos ξ hξ))]
  have homne : ∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → om ξ ≠ 0 := by
    intro ξ hξ hz
    have h := homnorm ξ hξ
    rw [hz, norm_zero] at h
    exact absurd h (by norm_num)
  have homback : ∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 → ‖ξ‖ • om ξ = ξ := by
    intro ξ hξ
    rw [homdef, smul_smul, mul_inv_cancel₀ (ne_of_gt (hnormpos ξ hξ)), one_smul]
  -- (E) at every non-zero vector, and 2-homogeneity of the quadratic form in its slot
  obtain ⟨hEpos, hquad⟩ := EllipPositiveAndQuadraticTwoHomogeneous A H hAH
  -- Step 3's continuity package: `ω` is continuous on `{ξ ≠ 0}` and MAPS IT INTO ITSELF
  have hinvcont : ContinuousOn (fun ξ : EuclideanSpace ℝ (Fin m) => ‖ξ‖⁻¹)
      {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := by
    refine ContinuousOn.inv₀ continuous_norm.continuousOn fun ξ hξ => ?_
    exact ne_of_gt (hnormpos ξ hξ)
  have hidcont : ContinuousOn (fun ξ : EuclideanSpace ℝ (Fin m) => ξ)
      {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := continuous_id.continuousOn
  have homcont : ContinuousOn om {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := by
    have h : ContinuousOn (fun ξ : EuclideanSpace ℝ (Fin m) => ‖ξ‖⁻¹ • ξ)
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := hinvcont.smul hidcont
    exact h.congr fun ξ _ => homdef ξ
  have hommaps : Set.MapsTo om {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0}
      {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := fun ξ hξ => homne ξ hξ
  -- `𝓔_A ∘ f` is continuous on `{ξ ≠ 0}` whenever `f` is and maps it into itself:
  -- a finite sum of products of continuous matrix entries and coordinates
  have hEcont : ∀ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContinuousOn f {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} →
      Set.MapsTo f {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0}
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} →
      ContinuousOn (fun ξ => Ellip A (f ξ))
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := by
    intro f hf hmaps
    have hAf : ContinuousOn (fun ξ => A (f ξ))
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := hAH.contA.comp hf hmaps
    have hent : ∀ i j : Fin m, ContinuousOn (fun ξ => A (f ξ) i j)
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := by
      intro i j
      have hproj : Continuous fun M : Matrix (Fin m) (Fin m) ℝ => M i j :=
        (continuous_apply j).comp (continuous_apply i)
      exact hproj.continuousOn.comp hAf (Set.mapsTo_univ _ _)
    have hcoord : ∀ j : Fin m, ContinuousOn (fun ξ => (f ξ) j)
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := fun j =>
      ((EuclideanSpace.proj j).continuous.continuousOn).comp hf (Set.mapsTo_univ _ _)
    have hsum : ContinuousOn (fun ξ => ∑ i, ∑ j, A (f ξ) i j * (f ξ) j * (f ξ) i)
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := by
      refine continuousOn_finsetSum _ fun i _ => ?_
      refine continuousOn_finsetSum _ fun j _ => ?_
      exact ((hent i j).mul (hcoord j)).mul (hcoord i)
    exact hsum
  have hA₀cont : ContinuousOn A₀ {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := by
    have h : ContinuousOn (fun ξ => A (om ξ))
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := hAH.contA.comp homcont hommaps
    exact h.congr fun ξ _ => hA₀def ξ
  have hH₀cont : ContinuousOn H₀ {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := by
    have h : ContinuousOn (fun ξ : EuclideanSpace ℝ (Fin m) => ‖ξ‖ * H (om ξ))
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} :=
      continuous_norm.continuousOn.mul (hAH.contH.comp homcont hommaps)
    exact h.congr fun ξ _ => hH₀def ξ
  -- Step 4: `ω` is invariant along rays, so `(A₀, H₀)` is normalized
  have homscale : ∀ (s : ℝ) (η : EuclideanSpace ℝ (Fin m)), 0 < s → η ≠ 0 →
      om (s • η) = om η := by
    intro s η hs hη
    have hsne : s ≠ 0 := ne_of_gt hs
    have hnne : ‖η‖ ≠ 0 := ne_of_gt (hnormpos η hη)
    have hns : ‖s • η‖ = s * ‖η‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    have hsc : (s * ‖η‖)⁻¹ * s = ‖η‖⁻¹ := by field_simp
    rw [homdef, homdef, hns, smul_smul, hsc]
  have hnormalized : NormalizedAH m A₀ H₀ := by
    refine ⟨?_, ?_⟩
    · intro s η hs hη
      rw [hA₀def, hA₀def, homscale s η hs hη]
    · intro s η hs hη
      rw [hH₀def, hH₀def, homscale s η hs hη, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs, mul_assoc]
  -- Step 5, clause (5): `𝓔_{A₀}(ξ) = ‖ξ‖² 𝓔_A(ω ξ)`, by (0b) and `ξ = ‖ξ‖ • ω ξ`
  have hellip0 : ∀ ξ : EuclideanSpace ℝ (Fin m), ξ ≠ 0 →
      ∑ i, ∑ j, A₀ ξ i j * ξ j * ξ i = ‖ξ‖ ^ 2 * Ellip A (om ξ) := by
    intro ξ hξ
    have h := hquad (A (om ξ)) ‖ξ‖ (om ξ)
    rw [homback ξ hξ] at h
    simp only [hA₀def]
    rw [h, hEllipDef]
  refine ⟨A₀, H₀, a, ?_, ?_, ?_, ?_, ?_, hnormalized⟩
  · -- Step 1, assertion (1): `a ξ > 0`
    intro ξ hξ
    rw [hadef]
    exact div_pos (hEpos ξ hξ)
      (mul_pos (pow_pos (hnormpos ξ hξ) 2) (hEpos (om ξ) (homne ξ hξ)))
  · -- Step 3, assertion (2): `a` is continuous on `{ξ ≠ 0}`
    have hnum : ContinuousOn (fun ξ : EuclideanSpace ℝ (Fin m) => Ellip A ξ)
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} :=
      hEcont (fun ξ => ξ) hidcont fun ξ hξ => hξ
    have hden : ContinuousOn
        (fun ξ : EuclideanSpace ℝ (Fin m) => ‖ξ‖ ^ 2 * Ellip A (om ξ))
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} :=
      (continuous_norm.continuousOn.pow 2).mul (hEcont om homcont hommaps)
    have h : ContinuousOn
        (fun ξ : EuclideanSpace ℝ (Fin m) =>
          Ellip A ξ / (‖ξ‖ ^ 2 * Ellip A (om ξ)))
        {ξ : EuclideanSpace ℝ (Fin m) | ξ ≠ 0} := by
      refine hnum.div hden fun ξ hξ => ?_
      exact ne_of_gt (mul_pos (pow_pos (hnormpos ξ hξ) 2) (hEpos (om ξ) (homne ξ hξ)))
    exact h.congr fun ξ _ => hadef ξ
  · -- Step 2, assertion (3): `ScalingIdentityAllT` at `(‖ξ‖, ω ξ)`, read through `ξ = ‖ξ‖ • ω ξ`
    intro ξ hξ
    obtain ⟨hA1, -⟩ :=
      ScalingIdentityAllT A H hAH ‖ξ‖ (om ξ) (hnormpos ξ hξ) (homne ξ hξ)
    rw [homback ξ hξ] at hA1
    rw [hA1, hadef, hA₀def]
  · -- Step 2, assertion (4)
    intro ξ hξ
    obtain ⟨-, hH1⟩ :=
      ScalingIdentityAllT A H hAH ‖ξ‖ (om ξ) (hnormpos ξ hξ) (homne ξ hξ)
    rw [homback ξ hξ] at hH1
    rw [hH1, hadef, hH₀def]
    ring
  · -- Step 5, assertion (5): the six clauses of (E) and (S) for `(A₀, H₀)`
    refine ⟨?_, ?_, hA₀cont, hH₀cont, ?_, ?_⟩
    · intro ξ hξ
      rw [hA₀def]
      exact hAH.symm (om ξ) (homne ξ hξ)
    · intro ξ hξ η
      simp only [hA₀def]
      exact hAH.psd (om ξ) (homne ξ hξ) η
    · intro ξ hξ
      rw [hellip0 ξ hξ]
      exact mul_pos (pow_pos (hnormpos ξ hξ) 2) (hEpos (om ξ) (homne ξ hξ))
    · -- clause (6) holds with `κ ≡ 1`, the factor the paper announces at rem:scale(a)
      refine ⟨fun _ _ => (1:ℝ), fun t ξ _ _ => one_pos, fun t ξ ht hξ => ?_,
        fun t ξ ht hξ => ?_⟩
      · show A₀ (t • ξ) = (1:ℝ) • A₀ ξ
        rw [hnormalized.A_homog t ξ (by linarith only [ht]) hξ, one_smul]
      · show H₀ (t • ξ) = t * (1:ℝ) * H₀ ξ
        rw [hnormalized.H_homog t ξ (by linarith only [ht]) hξ]
        ring
