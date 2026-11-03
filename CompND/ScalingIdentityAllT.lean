import CompND.Ellip
import CompND.StructureConditionsES
import CompND.EllipPositiveAndQuadraticTwoHomogeneous

/-- rem:scale(a): under (E) and (S) the scaling factor is `κ(t,ξ) = 𝓔(tξ)/(t² 𝓔(ξ))`, and
with that factor the scaling identities eq:scale hold for every `t > 0`, not only for
`t ≥ 1`. -/
theorem ScalingIdentityAllT {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ)
    (hAH : StructureConditionsES m A H) :
    ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin m)), 0 < t → ξ ≠ 0 →
      A (t • ξ) = (Ellip A (t • ξ) / (t ^ 2 * Ellip A ξ)) • A ξ ∧
      H (t • ξ) = t * (Ellip A (t • ξ) / (t ^ 2 * Ellip A ξ)) * H ξ := by
  obtain ⟨kap, hkappos, hkapA, hkapH⟩ := hAH.scaling
  have hEllipDef : ∀ η : EuclideanSpace ℝ (Fin m),
      Ellip A η = ∑ i, ∑ j, A η i j * η j * η i := fun _ => rfl
  -- (0a) (E) makes every denominator below non-zero; (0b) the quadratic form is
  -- 2-homogeneous in its VECTOR slot, the matrix held fixed
  obtain ⟨hEpos, hquad⟩ := EllipPositiveAndQuadraticTwoHomogeneous A H hAH
  -- (0b′): `𝓔_A(tξ) = t² ∑ᵢ∑ⱼ A(tξ)ᵢⱼ ξⱼ ξᵢ` -- the MATRIX argument stays at `t • ξ`
  have hEscale : ∀ (s : ℝ) (η : EuclideanSpace ℝ (Fin m)),
      Ellip A (s • η) = s ^ 2 * ∑ i, ∑ j, A (s • η) i j * η j * η i := by
    intro s η
    rw [hEllipDef]
    exact hquad (A (s • η)) s η
  -- for `t ≥ 1`, (S) turns that sum into `κ(t,ξ) 𝓔_A(ξ)`
  have hmat : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin m)), 1 ≤ t → ξ ≠ 0 →
      ∑ i, ∑ j, A (t • ξ) i j * ξ j * ξ i = kap t ξ * Ellip A ξ := by
    intro t ξ ht hξ
    rw [hkapA t ξ ht hξ, hEllipDef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  -- Step 1, display (1): the existential `κ` of (S) is pinned to the explicit factor
  have step1 : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin m)), 1 ≤ t → ξ ≠ 0 →
      kap t ξ = Ellip A (t • ξ) / (t ^ 2 * Ellip A ξ) := by
    intro t ξ ht hξ
    have htpos : (0:ℝ) < t := by linarith only [ht]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hExne : Ellip A ξ ≠ 0 := ne_of_gt (hEpos ξ hξ)
    have hid : Ellip A (t • ξ) = t ^ 2 * (kap t ξ * Ellip A ξ) := by
      rw [hEscale t ξ, hmat t ξ ht hξ]
    rw [hid]
    field_simp
  -- Step 1, display (2): the conclusion for `t ≥ 1`
  have main1 : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin m)), 1 ≤ t → ξ ≠ 0 →
      A (t • ξ) = (Ellip A (t • ξ) / (t ^ 2 * Ellip A ξ)) • A ξ ∧
      H (t • ξ) = t * (Ellip A (t • ξ) / (t ^ 2 * Ellip A ξ)) * H ξ := by
    intro t ξ ht hξ
    rw [← step1 t ξ ht hξ]
    exact ⟨hkapA t ξ ht hξ, hkapH t ξ ht hξ⟩
  -- Step 3: split on `1 ≤ t` or `0 < t < 1`
  intro t ξ htpos hξ
  rcases le_or_gt 1 t with ht | ht
  · exact main1 t ξ ht hξ
  -- Step 2: `0 < t < 1`, via Step 1 at the pair `(1/t, t • ξ)`
  have htne : t ≠ 0 := ne_of_gt htpos
  have ht' : (1:ℝ) ≤ 1 / t := by
    rw [le_div_iff₀ htpos]
    linarith only [ht]
  have hηne : t • ξ ≠ 0 := smul_ne_zero htne hξ
  have hEx : 0 < Ellip A ξ := hEpos ξ hξ
  have hEtx : 0 < Ellip A (t • ξ) := hEpos (t • ξ) hηne
  have hExne : Ellip A ξ ≠ 0 := ne_of_gt hEx
  have hEtxne : Ellip A (t • ξ) ≠ 0 := ne_of_gt hEtx
  have hback : (1 / t) • (t • ξ) = ξ := by
    rw [smul_smul, one_div, inv_mul_cancel₀ htne, one_smul]
  obtain ⟨hA1, hH1⟩ := main1 (1 / t) (t • ξ) ht' hηne
  rw [hback] at hA1 hH1
  -- display (3): the scalar for the pair `(1/t, t • ξ)` is `λ = t² 𝓔_A(ξ) / 𝓔_A(tξ) > 0`
  have hfac : Ellip A ξ / ((1 / t) ^ 2 * Ellip A (t • ξ))
      = t ^ 2 * Ellip A ξ / Ellip A (t • ξ) := by
    rw [div_pow, one_pow]
    field_simp
  rw [hfac] at hA1 hH1
  have hLampos : 0 < t ^ 2 * Ellip A ξ / Ellip A (t • ξ) :=
    div_pos (mul_pos (pow_pos htpos 2) hEx) hEtx
  have hLamne : t ^ 2 * Ellip A ξ / Ellip A (t • ξ) ≠ 0 := ne_of_gt hLampos
  refine ⟨?_, ?_⟩
  · -- the `A` identity, inverted
    rw [← inv_div (t ^ 2 * Ellip A ξ) (Ellip A (t • ξ)), hA1, smul_smul,
      inv_mul_cancel₀ hLamne, one_smul]
  · -- the `H` identity, solved for `H(tξ)`
    have hid : t * (Ellip A (t • ξ) / (t ^ 2 * Ellip A ξ))
          * (1 / t * (t ^ 2 * Ellip A ξ / Ellip A (t • ξ)) * H (t • ξ))
        = H (t • ξ) := by
      field_simp
    rw [hH1, hid]
