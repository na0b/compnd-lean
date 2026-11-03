import CompND.MatLe
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-- eq:matmon: for a symmetric non-negative definite `A` and symmetric `Y ≤ X` in the order
eq:matord, `Tr (A Y) ≤ Tr (A X)`. -/
theorem TraceMonotone {m : ℕ} (A Y X : Matrix (Fin m) (Fin m) ℝ)
    (hAsymm : A.IsSymm)
    (hApsd : ∀ ξ : EuclideanSpace ℝ (Fin m), 0 ≤ ∑ i, ∑ j, A i j * ξ j * ξ i)
    (hYsymm : Y.IsSymm) (hXsymm : X.IsSymm) (hYX : MatLe Y X) :
    (A * Y).trace ≤ (A * X).trace := by
  -- Bridge the node's double-sum positivity to `Matrix.PosSemidef`.
  have bridge : ∀ M : Matrix (Fin m) (Fin m) ℝ, M.IsSymm →
      (∀ ξ : EuclideanSpace ℝ (Fin m), 0 ≤ ∑ i, ∑ j, M i j * ξ j * ξ i) → M.PosSemidef := by
    intro M hsymm hpos
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hsymm, fun v => ?_⟩
    have h := hpos (WithLp.toLp 2 v)
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    refine le_of_le_of_eq h ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hApsd' : A.PosSemidef := bridge A hAsymm hApsd
  -- `Z := X - Y` is symmetric and non-negative definite.
  have hZsymm : (X - Y).IsSymm := hXsymm.sub hYsymm
  have hZpos : ∀ ξ : EuclideanSpace ℝ (Fin m), 0 ≤ ∑ i, ∑ j, (X - Y) i j * ξ j * ξ i := by
    intro ξ
    have h := hYX ξ
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    linarith
  have hZpsd : (X - Y).PosSemidef := bridge (X - Y) hZsymm hZpos
  -- Diagonalize `A` and push the unitary through the trace.
  set U : Matrix (Fin m) (Fin m) ℝ := (hApsd'.1.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
    with hUdef
  set dd : Fin m → ℝ := RCLike.ofReal ∘ hApsd'.1.eigenvalues with hdddef
  have hspec : A = U * Matrix.diagonal dd * star U := by
    simpa [hUdef, hdddef] using hApsd'.1.spectral_theorem
  have hkey : 0 ≤ (A * (X - Y)).trace := by
    have hconj : (star U * (X - Y) * U).PosSemidef := by
      have h := hZpsd.conjTranspose_mul_mul_same U
      rwa [← Matrix.star_eq_conjTranspose] at h
    have e1 : (A * (X - Y)).trace
        = (Matrix.diagonal dd * (star U * (X - Y) * U)).trace := by
      calc (A * (X - Y)).trace
          = (U * (Matrix.diagonal dd * (star U * (X - Y)))).trace := by
            rw [hspec]; simp only [mul_assoc]
        _ = ((Matrix.diagonal dd * (star U * (X - Y))) * U).trace :=
            Matrix.trace_mul_comm _ _
        _ = (Matrix.diagonal dd * (star U * (X - Y) * U)).trace := by
            simp only [mul_assoc]
    have e2 : (Matrix.diagonal dd * (star U * (X - Y) * U)).trace
        = ∑ k, dd k * (star U * (X - Y) * U) k k := by
      simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    rw [e1, e2]
    refine Finset.sum_nonneg fun k _ => ?_
    have h1 : 0 ≤ dd k := by
      simpa [hdddef] using hApsd'.eigenvalues_nonneg k
    exact mul_nonneg h1 hconj.diag_nonneg
  have e3 : (A * (X - Y)).trace = (A * X).trace - (A * Y).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [e3] at hkey
  linarith
