import CompND.UncondCaseC1
import CompND.UncondCaseConstant
import CompND.UncondCaseFirstLayer

/-- thm:uncond: the comparison principle holds unconditionally in each of three cases --
(i) one of `u`, `v` is `C¹` with non-vanishing horizontal gradient near `argmax_Ω (u - v)`,
(ii) one of them is constant, (iii) the step is `1` or both depend only on the first layer --
under the hypotheses of thm:comp minus its non-degeneracy condition on the regularizations,
all written out inline. The cited results are assumed at `G`, and -- because case (iii)
descends to `ℝᵐ` and applies them there -- also at the Euclidean setting on `ℝᵐ`. -/
theorem ComparisonUnconditional (G : CarnotSetting) (hc : CitedResults G)
    (hcE : CitedResults (EuclidSetting G.m))
    (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
    (H : EuclideanSpace ℝ (Fin G.m) → ℝ)
    (hAH : StructureConditionsES G.m A H)
    (Ω : Set (EuclideanSpace ℝ (Fin G.n)))
    (hΩopen : IsOpen Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hΩne : ∃ y : EuclideanSpace ℝ (Fin G.n), y ∉ Ω)
    (u v : EuclideanSpace ℝ (Fin G.n) → ℝ)
    (hucont : ContinuousOn u (closure Ω)) (hvcont : ContinuousOn v (closure Ω))
    (hsub : IsViscSubsol G A H Ω u) (hsup : IsViscSupersol G A H Ω v)
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x)
    (R : ℝ) (hR : 0 ≤ R)
    (hRb : ∀ x ∈ closure Ω, |u x| ≤ R / 2 ∧ |v x| ≤ R / 2)
    (hcases :
      (∃ N : Set (EuclideanSpace ℝ (Fin G.n)), IsOpen N ∧
          {y ∈ Ω | IsMaxOn (fun z => u z - v z) (closure Ω) y} ⊆ N ∧
          ((ContDiffOn ℝ 1 v N ∧ ∀ z ∈ N, ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
                HasFDerivAt v D z → hgrad G.sig z D ≠ 0) ∨
           (ContDiffOn ℝ 1 u N ∧ ∀ z ∈ N, ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
                HasFDerivAt u D z → hgrad G.sig z D ≠ 0))) ∨
      ((∃ c : ℝ, ∀ x ∈ closure Ω, u x = c) ∨ (∃ c : ℝ, ∀ x ∈ closure Ω, v x = c)) ∨
      (G.r = 1 ∨ (∃ F Gf : EuclideanSpace ℝ (Fin G.m) → ℝ,
          ContinuousOn F (G.pi1 '' closure Ω) ∧
          ContinuousOn Gf (G.pi1 '' closure Ω) ∧
          u = (fun x => F (G.pi1 x)) ∧ v = (fun x => Gf (G.pi1 x))))) :
    ∀ x ∈ Ω, u x ≤ v x := by
  rcases hcases with ⟨N, hNopen, hEN, hcase1⟩ | hcase2 | hcase3
  · -- case (i): one of the two functions is `C¹` with non-vanishing horizontal gradient
    have key := UncondCaseC1 G hc A H hAH Ω hΩopen hΩbdd hΩne u v hucont hvcont hsub hsup
      hbdry R hR hRb N hNopen hEN
    rcases hcase1 with hv | hu
    · exact key.1 hv
    · exact key.2 hu
  · -- case (ii): one of the two functions is constant
    have key := UncondCaseConstant G hc A H hAH Ω hΩopen hΩbdd hΩne u v hucont hvcont
      hsub hsup hbdry
    rcases hcase2 with hu | hv
    · exact key.2 hu
    · exact key.1 hv
  · -- case (iii): step one, or dependence on the first layer only
    have key := UncondCaseFirstLayer G hc hcE A H hAH Ω hΩopen hΩbdd hΩne u v hucont hvcont
      hsub hsup hbdry R hR hRb
    rcases hcase3 with hr | hfl
    · exact key.1 hr
    · exact key.2 hfl
