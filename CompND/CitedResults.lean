import CompND.CarnotSetting
import CompND.EuclidCitedResults
import CompND.StructureConditionsES
import CompND.IsViscSubsol
import CompND.IsViscSupersol
import CompND.LocallySemiConvexOn
import CompND.SupConv
import CompND.InfConv
import CompND.ReducedDomain

/-- The five results the paper cites from the literature and does not prove, bundled as a
hypothesis package *at a single sub-elliptic setting* `G`: the Bardi-Goffi strong maximum and
minimum principles in the special case cor:stmx, Pansu's differentiability theorem together
with [DMV13, Prop. 4.8], and parts (1)-(3) of lem:wang, each stated for `G` itself, together
with the two Euclidean cited results of `EuclidCitedResults` (Aleksandrov's theorem and
Jensen's lemma), which mention no setting and are inherited unchanged. The parameter matters:
the three Carnot-side results are theorems about genuine Carnot groups whose proofs use the
dilations and the stratification, neither of which is a field of `CarnotSetting`, so
asserting them at every instance of the axiomatization would over-reach and could make the
package unsatisfiable. No axiom is introduced; every result that uses one of these carries
this structure as an explicit hypothesis, at the setting where it is used. -/
structure CitedResults (G : CarnotSetting) : Prop extends EuclidCitedResults where
  strongMax : ∀ (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
      (H : EuclideanSpace ℝ (Fin G.m) → ℝ),
      StructureConditionsES G.m A H →
      ∀ U : Set (EuclideanSpace ℝ (Fin G.n)), IsOpen U → IsConnected U →
      ∀ u : EuclideanSpace ℝ (Fin G.n) → ℝ, IsViscSubsol G A H U u →
      ∀ x₀ ∈ U, IsMaxOn u U x₀ → 0 ≤ u x₀ → ∀ y ∈ U, u y = u x₀
  strongMin : ∀ (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
      (H : EuclideanSpace ℝ (Fin G.m) → ℝ),
      StructureConditionsES G.m A H →
      ∀ U : Set (EuclideanSpace ℝ (Fin G.n)), IsOpen U → IsConnected U →
      ∀ v : EuclideanSpace ℝ (Fin G.n) → ℝ, IsViscSupersol G A H U v →
      ∀ x₀ ∈ U, IsMinOn v U x₀ → v x₀ ≤ 0 → ∀ y ∈ U, v y = v x₀
  pansuDiff : ∀ (Ω : Set (EuclideanSpace ℝ (Fin G.n))), IsOpen Ω →
      ∀ (f : EuclideanSpace ℝ (Fin G.n) → ℝ) (L : ℝ),
      (∀ x ∈ Ω, ∀ y ∈ Ω, |f x - f y| ≤ L * G.hnorm (G.mul (-y) x)) →
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin G.n))),
        x ∈ Ω → ∃ ξ : EuclideanSpace ℝ (Fin G.m),
          HasPansuGradAt G.mul G.pi1 G.hnorm f x ξ
  pansuConst : ∀ (Ω : Set (EuclideanSpace ℝ (Fin G.n))),
      IsOpen Ω → IsConnected Ω →
      ∀ (f : EuclideanSpace ℝ (Fin G.n) → ℝ) (L : ℝ),
      (∀ x ∈ Ω, ∀ y ∈ Ω, |f x - f y| ≤ L * G.hnorm (G.mul (-y) x)) →
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin G.n))),
        x ∈ Ω → HasPansuGradAt G.mul G.pi1 G.hnorm f x 0) →
      ∀ x ∈ Ω, ∀ y ∈ Ω, f x = f y
  wang1 : ∀ (Ω : Set (EuclideanSpace ℝ (Fin G.n))),
      IsOpen Ω → Bornology.IsBounded Ω →
      ∀ w : EuclideanSpace ℝ (Fin G.n) → ℝ, ContinuousOn w (closure Ω) →
      ∀ ε : ℝ, 0 < ε →
        LocallySemiConvexOn Ω (SupConv G Ω w ε) ∧
        LocallySemiConvexOn Ω (fun x => -(InfConv G Ω w ε x))
  wang2 : ∀ (Ω : Set (EuclideanSpace ℝ (Fin G.n))),
      IsOpen Ω → Bornology.IsBounded Ω →
      ∀ w : EuclideanSpace ℝ (Fin G.n) → ℝ, ContinuousOn w (closure Ω) →
      (∀ ε : ℝ, 0 < ε → ∀ x ∈ closure Ω,
          w x ≤ SupConv G Ω w ε x ∧ InfConv G Ω w ε x ≤ w x) ∧
      (∀ ε ε' : ℝ, 0 < ε' → ε' ≤ ε → ∀ x ∈ closure Ω,
          SupConv G Ω w ε' x ≤ SupConv G Ω w ε x ∧
          InfConv G Ω w ε x ≤ InfConv G Ω w ε' x) ∧
      (∀ η : ℝ, 0 < η → ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ x ∈ closure Ω,
          |SupConv G Ω w ε x - w x| ≤ η ∧ |InfConv G Ω w ε x - w x| ≤ η)
  wang3 : ∀ (A : EuclideanSpace ℝ (Fin G.m) → Matrix (Fin G.m) (Fin G.m) ℝ)
      (H : EuclideanSpace ℝ (Fin G.m) → ℝ),
      StructureConditionsES G.m A H →
      ∀ Ω : Set (EuclideanSpace ℝ (Fin G.n)), IsOpen Ω → Bornology.IsBounded Ω →
      ∀ u v : EuclideanSpace ℝ (Fin G.n) → ℝ,
      ContinuousOn u (closure Ω) → ContinuousOn v (closure Ω) →
      ∀ R : ℝ, (∀ x ∈ closure Ω, |u x| ≤ R / 2 ∧ |v x| ≤ R / 2) →
      IsViscSubsol G A H Ω u → IsViscSupersol G A H Ω v →
      ∀ ε : ℝ, 0 < ε →
        IsViscSubsol G A H (ReducedDomain G Ω R ε) (SupConv G Ω u ε) ∧
        IsViscSupersol G A H (ReducedDomain G Ω R ε) (InfConv G Ω v ε)
