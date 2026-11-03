import CompND.hgrad

/-- Continuity of the horizontal gradient along a convergent pair. For a frame `sig` whose
components are continuous, if `x_k → x_∞` in `ℝⁿ` and the `1`-jets `D_k → D_∞` in operator
norm, then `hgrad sig x_k D_k → hgrad sig x_∞ D_∞` in `ℝᵐ`. The proof is the two-term split
of `D_k(sig x_k i) - D_∞(sig x_∞ i)`: the jets converge uniformly while the frame values stay
bounded, and `D_∞` is itself continuous. -/
theorem HgradTendstoOfTendsto {n m : ℕ}
    (sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n))
    (hsigc : ∀ i, Continuous fun x => sig x i)
    (xs : ℕ → EuclideanSpace ℝ (Fin n)) (xinf : EuclideanSpace ℝ (Fin n))
    (Ds : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (Dinf : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hxlim : Filter.Tendsto xs Filter.atTop (nhds xinf))
    (hDlim : Filter.Tendsto Ds Filter.atTop (nhds Dinf)) :
    Filter.Tendsto (fun k => hgrad sig (xs k) (Ds k)) Filter.atTop
      (nhds (hgrad sig xinf Dinf)) := by
  -- `hgrad` unfolded: its `i`-th component is `D (sig y i)`
  have hgradeq : ∀ (y : EuclideanSpace ℝ (Fin n))
      (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      hgrad sig y D = (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => D (sig y i)) :=
    fun _ _ => rfl
  have hopzero : Filter.Tendsto (fun k => ‖Ds k - Dinf‖) Filter.atTop (nhds 0) := by
    have h := (hDlim.sub (tendsto_const_nhds (x := Dinf)
      (f := Filter.atTop (α := ℕ)))).norm
    simpa using h
  have hcoord : ∀ i : Fin m,
      Filter.Tendsto (fun k => Ds k (sig (xs k) i)) Filter.atTop
        (nhds (Dinf (sig xinf i))) := by
    intro i
    have hsj : Filter.Tendsto (fun k => sig (xs k) i) Filter.atTop
        (nhds (sig xinf i)) := ((hsigc i).tendsto xinf).comp hxlim
    have hB : Filter.Tendsto (fun k => Dinf (sig (xs k) i)) Filter.atTop
        (nhds (Dinf (sig xinf i))) := (Dinf.continuous.tendsto _).comp hsj
    have hA0 : Filter.Tendsto (fun k => ‖Ds k - Dinf‖ * ‖sig (xs k) i‖)
        Filter.atTop (nhds 0) := by simpa using hopzero.mul hsj.norm
    refine hB.congr_dist ?_
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hA0
    rw [Real.dist_eq, ← Real.norm_eq_abs]
    have h1 : Dinf (sig (xs k) i) - Ds k (sig (xs k) i)
        = (Dinf - Ds k) (sig (xs k) i) := by simp
    rw [h1]
    calc ‖(Dinf - Ds k) (sig (xs k) i)‖
        ≤ ‖Dinf - Ds k‖ * ‖sig (xs k) i‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Ds k - Dinf‖ * ‖sig (xs k) i‖ := by rw [norm_sub_rev]
  simp only [hgradeq]
  refine ((EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.tendsto _).comp ?_
  rw [tendsto_pi_nhds]
  exact hcoord
