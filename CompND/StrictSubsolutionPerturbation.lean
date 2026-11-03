import CompND.EllipticityLowerBound
import CompND.LocalMaxSecondOrder
import CompND.PerturbationIdentity

/-- cor:gamma: with `ψ'(w x₀) > 0`, `λ ≤ ψ''(w x₀)`, `λ > 0`, `θ ≤ |ξ₀|` and
`ℒw(x₀) ≤ 0`, the relabelled function `ψ ∘ w` is a strict classical sub-solution at `x₀`:
`ℒ(ψ ∘ w)(x₀) ≤ -γ` with `γ = λ e₀ θ² > 0`, `e₀` any ellipticity constant of eq:ell0. -/
theorem StrictSubsolutionPerturbation {n m : ℕ}
    (sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) → ℝ) (hN : NormalizedAH m A H)
    (e₀ : ℝ) (he₀ : 0 < e₀)
    (hell : ∀ ξ : EuclideanSpace ℝ (Fin m), e₀ * ‖ξ‖ ^ 2 ≤ Ellip A ξ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hw : TwiceDiffAt w x₀ D B)
    (θ : ℝ) (hθ : 0 < θ) (hξθ : θ ≤ ‖hgrad sig x₀ D‖)
    (lam : ℝ) (hlam : 0 < lam)
    (ht : 0 < deriv ψ (w x₀)) (hc : lam ≤ deriv (deriv ψ) (w x₀))
    (hsub : Lop sig A H x₀ D B ≤ 0) :
    TwiceDiffAt (fun y => ψ (w y)) x₀ (deriv ψ (w x₀) • D)
        (deriv ψ (w x₀) • B + deriv (deriv ψ) (w x₀) • D.smulRight D) ∧
      Lop sig A H x₀ (deriv ψ (w x₀) • D)
          (deriv ψ (w x₀) • B + deriv (deriv ψ) (w x₀) • D.smulRight D)
        ≤ -(lam * e₀ * θ ^ 2) := by
  have hg : hgrad sig x₀ D ≠ 0 := by
    intro h0
    rw [h0] at hξθ
    simp at hξθ
    linarith
  obtain ⟨hjet, -, hid⟩ :=
    PerturbationIdentity sig A H hN ψ hψ w x₀ D B hw hg ht
  refine ⟨hjet, ?_⟩
  rw [hid]
  -- the ellipticity lower bound along `ξ₀`
  have hE : e₀ * θ ^ 2 ≤ Ellip A (hgrad sig x₀ D) := by
    refine le_trans ?_ (hell (hgrad sig x₀ D))
    have : θ ^ 2 ≤ ‖hgrad sig x₀ D‖ ^ 2 := by
      have h1 : 0 ≤ θ := hθ.le
      nlinarith [hξθ]
    nlinarith [he₀.le]
  have hEpos : 0 < Ellip A (hgrad sig x₀ D) := lt_of_lt_of_le (by positivity) hE
  set t : ℝ := deriv ψ (w x₀) with hdt
  set c : ℝ := deriv (deriv ψ) (w x₀) with hdc
  have hcpos : 0 < c := lt_of_lt_of_le hlam hc
  have hkey : t * (Lop sig A H x₀ D B - c / t * Ellip A (hgrad sig x₀ D))
      = t * Lop sig A H x₀ D B - c * Ellip A (hgrad sig x₀ D) := by
    field_simp
  rw [hkey]
  have h1 : t * Lop sig A H x₀ D B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hsub
  have h2 : lam * e₀ * θ ^ 2 ≤ c * Ellip A (hgrad sig x₀ D) := by
    have ha : lam * (e₀ * θ ^ 2) ≤ c * (e₀ * θ ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    have hb : c * (e₀ * θ ^ 2) ≤ c * Ellip A (hgrad sig x₀ D) :=
      mul_le_mul_of_nonneg_left hE hcpos.le
    nlinarith [ha, hb]
  linarith
