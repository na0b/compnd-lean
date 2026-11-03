import CompND.Preamble
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-- The relabelling used in prop:comp0, Step 1: `ψ_λ(s) = s + λ e^s`. It satisfies the
three global hypotheses of subsec:semi(4) (`C²`, `ψ' ≥ 1`, `ψ'' ≥ 0`), has
`ψ''_λ(s) ≥ λ e^{-M} > 0` on `|s| ≤ M`, and `‖ψ_λ ∘ u - u‖_∞ ≤ λ e^M → 0` as `λ → 0⁺`. -/
theorem ExpRelabelling (lam M : ℝ) (hlam : 0 < lam) :
    ContDiff ℝ 2 (fun s : ℝ => s + lam * Real.exp s) ∧
    (∀ s : ℝ, deriv (fun s : ℝ => s + lam * Real.exp s) s = 1 + lam * Real.exp s) ∧
    (∀ s : ℝ, 1 ≤ deriv (fun s : ℝ => s + lam * Real.exp s) s) ∧
    (∀ s : ℝ, deriv (deriv (fun s : ℝ => s + lam * Real.exp s)) s = lam * Real.exp s) ∧
    (∀ s : ℝ, 0 ≤ deriv (deriv (fun s : ℝ => s + lam * Real.exp s)) s) ∧
    0 < lam * Real.exp (-M) ∧
    (∀ s : ℝ, |s| ≤ M →
        lam * Real.exp (-M) ≤ deriv (deriv (fun s : ℝ => s + lam * Real.exp s)) s) ∧
    (∀ s : ℝ, |s| ≤ M → |(s + lam * Real.exp s) - s| ≤ lam * Real.exp M) := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s + lam * Real.exp s)
      (1 + lam * Real.exp s) s := fun s =>
    (hasDerivAt_id s).add ((Real.hasDerivAt_exp s).const_mul lam)
  have hderiv : deriv (fun s : ℝ => s + lam * Real.exp s)
      = fun s => 1 + lam * Real.exp s := funext fun s => (hd s).deriv
  have hd2 : ∀ s : ℝ, deriv (deriv (fun s : ℝ => s + lam * Real.exp s)) s
      = lam * Real.exp s := by
    intro s
    rw [hderiv]
    have h : HasDerivAt (fun s : ℝ => 1 + lam * Real.exp s) (lam * Real.exp s) s := by
      simpa using ((Real.hasDerivAt_exp s).const_mul lam).const_add (1 : ℝ)
    exact h.deriv
  refine ⟨contDiff_id.add (contDiff_const.mul Real.contDiff_exp), fun s => by rw [hderiv],
    fun s => by rw [hderiv]; nlinarith [Real.exp_pos s, hlam.le], hd2,
    fun s => by rw [hd2]; positivity, mul_pos hlam (Real.exp_pos _), fun s hs => ?_,
    fun s hs => ?_⟩
  · rw [hd2]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_of_abs_le hs)) hlam.le
  · have hexp : Real.exp s ≤ Real.exp M := Real.exp_le_exp.mpr (le_of_abs_le hs)
    have hid : (s + lam * Real.exp s) - s = lam * Real.exp s := by ring
    rw [hid, abs_of_nonneg (mul_nonneg hlam.le (Real.exp_pos s).le)]
    exact mul_le_mul_of_nonneg_left hexp hlam.le
