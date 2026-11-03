import CompND.SemiConvexGradPartialCont
import CompND.hgrad
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-- eq:thetahalf: if the horizontal gradient of a locally semi-convex `u` has norm at least
`θ` on a compact set `E ⊆ Ω` and the sets `E_λ` approach `E` as `λ → 0⁺`, then for `λ`
small the horizontal gradient of `u` has norm at least `θ/2` at every differentiability
point of `u` in `E_λ`. -/
theorem RelabellingGradientBound {n m : ℕ}
    (sig : EuclideanSpace ℝ (Fin n) → Fin m → EuclideanSpace ℝ (Fin n))
    (hsig : ∀ i, Continuous fun x => sig x i)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : LocallySemiConvexOn Ω u)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hEcpt : IsCompact E) (hEΩ : E ⊆ Ω)
    (hEdiff : ∀ x ∈ E, ∃ D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, HasFDerivAt u D x)
    (θ : ℝ) (hθ : 0 < θ)
    (hθE : ∀ x ∈ E, ∀ D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      HasFDerivAt u D x → θ ≤ ‖hgrad sig x D‖)
    (Elam : ℝ → Set (EuclideanSpace ℝ (Fin n)))
    (hElamΩ : ∀ lam : ℝ, 0 < lam → Elam lam ⊆ Ω)
    (hElamconv : ∀ η : ℝ, 0 < η → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ x ∈ Elam lam, ∃ z ∈ E, dist x z ≤ η) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ x ∈ Elam lam,
      ∀ D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, HasFDerivAt u D x →
        θ / 2 ≤ ‖hgrad sig x D‖ := by
  -- `hgrad` is a plain definition, so its defining equation is `rfl`.
  have hgradeq : ∀ (y : EuclideanSpace ℝ (Fin n)) (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      hgrad sig y D = (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => D (sig y i)) :=
    fun _ _ => rfl
  by_contra hcon
  push Not at hcon
  -- Step 1: the contradiction sequences, with the `η = 1/(k+1)` diagonal folded in.
  have step : ∀ k : ℕ, ∃ (xk : EuclideanSpace ℝ (Fin n))
      (Dk : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (zk : EuclideanSpace ℝ (Fin n)),
      xk ∈ Ω ∧ HasFDerivAt u Dk xk ∧ ‖hgrad sig xk Dk‖ < θ / 2 ∧ zk ∈ E ∧
        dist xk zk ≤ 1 / (k + 1 : ℝ) := by
    intro k
    have hη : (0:ℝ) < 1 / (k + 1 : ℝ) := by positivity
    obtain ⟨lam₀k, hlam₀k, hprop⟩ := hElamconv (1 / (k + 1 : ℝ)) hη
    obtain ⟨lam, hlam0, hlamlt, xk, hxk, Dk, hDk, hbd⟩ :=
      hcon (min (1 / (k + 1 : ℝ)) lam₀k) (lt_min hη hlam₀k)
    obtain ⟨zk, hzkE, hdist⟩ :=
      hprop lam hlam0 (lt_of_lt_of_le hlamlt (min_le_right _ _)) xk hxk
    exact ⟨xk, Dk, zk, hElamΩ lam hlam0 hxk, hDk, hbd, hzkE, hdist⟩
  choose xx DD zz hxxΩ hDD hbd hzzE hdist using step
  -- Step 2: a convergent subsequence of `zz`, transferred to `xx`.
  obtain ⟨xhat, hxhatE, φ, hφmono, hφlim⟩ := hEcpt.tendsto_subseq hzzE
  have hzφ : Filter.Tendsto (fun j => zz (φ j)) Filter.atTop (nhds xhat) := hφlim
  have hdzero : Filter.Tendsto (fun j => dist (zz (φ j)) (xx (φ j))) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [dist_comm]
    refine (hdist (φ j)).trans ?_
    have hj : (j : ℝ) ≤ (φ j : ℝ) := by exact_mod_cast hφmono.le_apply
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hxxlim : Filter.Tendsto (fun j => xx (φ j)) Filter.atTop (nhds xhat) :=
    hzφ.congr_dist hdzero
  -- Step 3: partial continuity of the gradient.
  obtain ⟨Dhat, hDhat⟩ := hEdiff xhat hxhatE
  have hpc : Filter.Tendsto (fun j => DD (φ j)) Filter.atTop (nhds Dhat) :=
    SemiConvexGradPartialCont Ω u (Or.inl hu) xhat (hEΩ hxhatE) (fun j => xx (φ j))
      (fun j => hxxΩ (φ j)) hxxlim Dhat hDhat (fun j => DD (φ j)) (fun j => hDD (φ j))
  have hopzero : Filter.Tendsto (fun j => ‖DD (φ j) - Dhat‖) Filter.atTop (nhds 0) := by
    have h := (hpc.sub (tendsto_const_nhds (x := Dhat) (f := Filter.atTop (α := ℕ)))).norm
    simpa using h
  -- Step 4: the horizontal gradients converge.
  have hcoord : ∀ i : Fin m, Filter.Tendsto (fun j => DD (φ j) (sig (xx (φ j)) i))
      Filter.atTop (nhds (Dhat (sig xhat i))) := by
    intro i
    have hsj : Filter.Tendsto (fun j => sig (xx (φ j)) i) Filter.atTop (nhds (sig xhat i)) :=
      ((hsig i).tendsto xhat).comp hxxlim
    have hB : Filter.Tendsto (fun j => Dhat (sig (xx (φ j)) i)) Filter.atTop
        (nhds (Dhat (sig xhat i))) := (Dhat.continuous.tendsto _).comp hsj
    have hA0 : Filter.Tendsto (fun j => ‖DD (φ j) - Dhat‖ * ‖sig (xx (φ j)) i‖)
        Filter.atTop (nhds 0) := by
      have h := hopzero.mul hsj.norm
      simpa using h
    refine hB.congr_dist ?_
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hA0
    rw [Real.dist_eq, ← Real.norm_eq_abs]
    have h1 : Dhat (sig (xx (φ j)) i) - DD (φ j) (sig (xx (φ j)) i)
        = (Dhat - DD (φ j)) (sig (xx (φ j)) i) := by simp
    rw [h1]
    calc ‖(Dhat - DD (φ j)) (sig (xx (φ j)) i)‖
        ≤ ‖Dhat - DD (φ j)‖ * ‖sig (xx (φ j)) i‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖DD (φ j) - Dhat‖ * ‖sig (xx (φ j)) i‖ := by rw [norm_sub_rev]
  have hconv : Filter.Tendsto (fun j => hgrad sig (xx (φ j)) (DD (φ j))) Filter.atTop
      (nhds (hgrad sig xhat Dhat)) := by
    simp only [hgradeq]
    refine ((EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.tendsto _).comp ?_
    rw [tendsto_pi_nhds]
    exact hcoord
  -- Step 5: the contradiction.
  have hlimle : ‖hgrad sig xhat Dhat‖ ≤ θ / 2 := by
    refine le_of_tendsto hconv.norm ?_
    filter_upwards with j
    exact (hbd (φ j)).le
  have hge := hθE xhat hxhatE Dhat hDhat
  linarith
