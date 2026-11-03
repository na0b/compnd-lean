# Comparison principles for degenerate sub-elliptic equations, in Lean 4

This repository contains a Lean 4 formalization, built on [Mathlib](https://github.com/leanprover-community/mathlib4), of Theorems 1.2 and 1.3 of

> Juan J. Manfredi and Shirsho Mukherjee,
> *Comparison principles for degenerate sub-elliptic equations in non-divergence form*, manuscript, 2026.

These are the comparison principle for viscosity sub- and super-solutions of −Tr(A(𝔛u) 𝔛𝔛*u) + H(𝔛u) = 0 on a Carnot group under the non-degeneracy hypothesis on the regularizations (Theorem 1.2), and the three unconditional cases (Theorem 1.3 (i)–(iii)).

**Five results that the paper cites from the literature are not proved; they are stated precisely and carried as explicit hypotheses** (see [Cited results](#cited-results)). Everything else is proved. The development contains no `sorry` and no axioms: both theorems depend only on the three standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`). So each theorem reads "the cited results (for the group in question) imply the comparison principle".

<!-- TODO: remove once both authors have read the Lean statements below against the paper. -->

## Results

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 1.2, comparison under non-degeneracy of 𝔛u<sup>ε</sup> on E<sub>ε</sub> | `ComparisonUnderNondegeneracy` | [`CompND/ComparisonUnderNondegeneracy.lean`](CompND/ComparisonUnderNondegeneracy.lean) |
| Theorem 1.3, cases (i), (ii), (iii) | `ComparisonUnconditional` | [`CompND/ComparisonUnconditional.lean`](CompND/ComparisonUnconditional.lean) |

The three cases of Theorem 1.3 are `UncondCaseC1`, `UncondCaseConstant` and `UncondCaseFirstLayer`. Among the intermediate results: Proposition 3.3 is `ComparisonNondegenerateSemiconvex`, Lemma 3.4 `BoundaryLocalization`, Lemma 3.5 `MaxValueLipschitz`, Lemma 3.6 `EnvelopeIdentity`, Lemma 3.7 `NondegeneracyAtEveryScale`, Lemma 3.8(4) `SupConvAttainment`, Remark 2.2 `ClassicalAtTwiceDiff`. The properties of semi-convex functions of Section 2.3 are `SemiConvexDiffAtMax`, `SemiConvexGradPartialCont`, `SemiConvexLocLipschitz` and `SemiConvexCompose`. Section 4 (the obstruction and the open problem) is not formalized.

## The setting

Mathlib has no Carnot groups. The group enters through the structure `CarnotSetting` (files `CarnotGroup.lean`, `CarnotNorm.lean`, `CarnotSetting.lean`), whose fields are the structural facts of Section 2.4 that the paper takes from Bonfiglioli–Lanconelli–Uguzzoni and Magnani, in exponential coordinates on ℝⁿ:

- a smooth group law `mul` with neutral element 0 and inverse x ↦ −x; the first-layer projection π₁ (a linear homomorphism onto ℝᵐ); the horizontal exponential; the step r ≥ 1, and commutativity when r = 1;
- the homogeneous norm (2.15): continuous, even, vanishing only at 0, ‖exp(ζ·X)‖ = |ζ|, ‖·‖<sup>2r!</sup> smooth, proper; the two inequalities (2.17); the Hölder equivalence of d(x, y) = ‖y⁻¹ ∗ x‖ with the Euclidean distance on bounded sets; connected balls;
- the frame X<sub>i</sub> = σ<sup>i</sup>(x)·∇: smooth, linearly independent, satisfying Hörmander's condition (1.6); the Taylor formula (2.18); left-invariance of horizontal jets; and the form of the X<sub>i</sub> on functions of the first layer.

Every Carnot group of step r with m generators, written in the coordinates of Section 2.4, gives an instance of `CarnotSetting`. **This is not checked in Lean**: no particular non-abelian group (such as the Heisenberg group) is constructed. The Euclidean setting is constructed (`EuclideanCarnotSettingExists`, `EuclidSetting`), which shows the structure is not vacuous.

## Cited results

The five cited results are the fields of two structures, each a `Prop` used as a hypothesis; no axiom is introduced.

| Paper | Field | Structure |
|---|---|---|
| Bardi–Goffi strong maximum and minimum principles, in the form of Corollary 2.4 | `strongMax`, `strongMin` | `CitedResults G` |
| Pansu's differentiability theorem, Section 2.4 | `pansuDiff` | `CitedResults G` |
| [DMV13, Proposition 4.8]: zero horizontal differential a.e. ⇒ constant | `pansuConst` | `CitedResults G` |
| Lemma 3.8 (1)–(3) = [CYW07, Proposition 3.3] | `wang1`, `wang2`, `wang3` | `CitedResults G` |
| Aleksandrov's theorem, Theorem 2.6 | `aleksandrov` | `EuclidCitedResults` |
| Jensen's lemma, Lemma 2.7 | `jensen` | `EuclidCitedResults` |

`CitedResults G` extends `EuclidCitedResults` and states the group-dependent results **for the single setting G**, not for every instance of `CarnotSetting`. That restriction matters: these are theorems about genuine Carnot groups, and the structure contains no dilations or stratification. Theorem 1.3 assumes `CitedResults G` and, because case (iii) passes to the Euclidean space ℝᵐ of the first layer and applies the cited results there, also `CitedResults (EuclidSetting G.m)`, the cited results for Euclidean ℝᵐ.

## Definitions

| Paper | Lean | Meaning |
|---|---|---|
| 𝔛u = σ(x)ᵀ∇u, (2.6) | `hgrad sig x D` | the vector (D(σ<sup>i</sup>(x)))<sub>i</sub> for a first-order jet D |
| 𝔛𝔛*u = σᵀD²uσ + 𝓜(x, ∇u), (2.6)–(2.7) | `hhessS sig x D B`, `Mfield` | read on second-order jets (D, B) |
| ℒ, (1.8) | `Lop sig A H x D B` | −Tr(A(𝔛u) 𝔛𝔛*u) + H(𝔛u) |
| (E) and (S), (1.9)–(1.10), with A symmetric PSD and A, H continuous on ℝᵐ∖{0} | `StructureConditionsES m A H` | |
| Definition 2.1, viscosity sub-/super-solution | `IsViscSubsol G A H Ω u`, `IsViscSupersol` | u USC (LSC) on Ω, and Lop ≤ 0 (≥ 0) at the jet of every C² test function φ with x a maximum (minimum) of u − φ over Ω and 𝔛φ(x) ≠ 0 |
| u<sup>ε</sup>, v<sub>ε</sub>, (3.13)–(3.14) | `SupConv G Ω w ε`, `InfConv G Ω w ε` | sup / inf over z with z ∗ x ∈ Ω̄ of w(z ∗ x) ∓ ‖z‖<sup>q</sup>/(2ε), q = 2·r! |
| Ω[ε], (3.15) | `ReducedDomain G Ω R ε` | {x ∈ Ω : inf<sub>y∉Ω</sub> ‖y ∗ x⁻¹‖<sup>q</sup> > (1 + 4R)ε} |
| Definition 2.5, semi-convex | `LocallySemiConvexOn Ω w` | around each point, w + Λ\|x\|²/2 is convex on a ball |
| twice differentiable at x | `TwiceDiffAt w x D B` | second-order Peano expansion |
| Pansu differential | `HasPansuGradAt` | f(x ∗ g) = f(x) + ⟨ξ, π₁g⟩ + o(‖g‖) |

ℝⁿ is `EuclideanSpace ℝ (Fin n)`. A and H are total functions on ℝᵐ, but every hypothesis on them is imposed only for ξ ≠ 0, and test functions have 𝔛φ ≠ 0, so their values at 0 are irrelevant, as in the paper. ∂Ω is `frontier Ω`.

## Theorem 1.2

```lean
theorem ComparisonUnderNondegeneracy (G : CarnotSetting) (hc : CitedResults G)
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
    (εs : ℕ → ℝ) (hεpos : ∀ k, 0 < εs k)
    (hεlim : Filter.Tendsto εs Filter.atTop (nhds 0))
    (hnd : ∀ k : ℕ, ∀ x ∈ ReducedDomain G Ω R (εs k),
      IsMaxOn (fun y => SupConv G Ω u (εs k) y - InfConv G Ω v (εs k) y)
        (closure (ReducedDomain G Ω R (εs k))) x →
      ∀ D : EuclideanSpace ℝ (Fin G.n) →L[ℝ] ℝ,
        HasFDerivAt (SupConv G Ω u (εs k)) D x → hgrad G.sig x D ≠ 0) :
    ∀ x ∈ Ω, u x ≤ v x
```

`R` is any number with |u|, |v| ≤ R/2 on Ω̄ (the paper takes R = 2 max(‖u‖∞, ‖v‖∞)); it enters through the reduced domain Ω[ε]. The hypothesis `hnd` is the paper's: along a sequence ε<sub>k</sub> → 0⁺, at every point of E<sub>ε<sub>k</sub></sub> (a point of Ω[ε<sub>k</sub>] where u<sup>ε</sup> − v<sub>ε</sub> attains its maximum over the closure of Ω[ε<sub>k</sub>]) the horizontal gradient of u<sup>ε<sub>k</sub></sup> is non-zero. `hΩne` (Ω is not all of ℝⁿ) is automatic for n ≥ 1.

## Theorem 1.3

```lean
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
    ∀ x ∈ Ω, u x ≤ v x
```

`hcases` is the disjunction of the three cases: (i) v, or u, is C¹ with non-vanishing horizontal gradient on an open set N containing argmax<sub>Ω</sub>(u − v), the set of points of Ω where u − v attains its maximum over Ω̄; (ii) u or v is constant on Ω̄; (iii) r = 1, or u = F ∘ π₁ and v = G ∘ π₁ with F, G continuous on π₁(Ω̄).

## What is and is not checked by Lean

The Lean kernel checks that the two theorems follow, using only the three standard axioms, from Mathlib, the definitions, and the hypotheses `CitedResults` (and `EuclidCitedResults`). Lean does **not** check:

- that the cited results hold: they are taken from the literature, as in the paper;
- that every Carnot group is an instance of `CarnotSetting` (see [The setting](#the-setting));
- that the definitions and statements say what the paper says.

The statements were reviewed against the paper during the formalization (see below), but readers who rely on the result should compare them, and the definitions they use, against the paper themselves. The definitions are listed in Section 1 of the blueprint.

## Blueprint

The directory [`blueprint/`](blueprint) contains a natural-language statement and a detailed proof for every Lean declaration, cross-referenced to the paper and to each other. They are collected, in dependency order, in [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf) (116 pages). To rebuild it, run `pdflatex blueprint.tex` three times in that directory.

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
git clone <repository URL> compnd-lean
cd compnd-lean
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean Axioms.lean # print the axioms used by each main result
```

The project is pinned to Lean `v4.33.0` and the Mathlib commit recorded in `lakefile.lean`. Continuous integration rebuilds the project and checks the axioms on every push.

## Layout

```
CompND.lean            root module, imports the main results
CompND/                one file per definition, lemma or theorem (75 files)
Axioms.lean            #print axioms for the main results
blueprint/blueprint.tex  natural-language companion (inputs blueprint/nodes/*.tex)
```

## How this formalization was produced

The formalization was produced with [Trellis](https://github.com/wpegden/trellis), an AI-assisted formalization pipeline; the Lean proofs and the blueprint were written by AI agents (Claude, by Anthropic) under the Trellis protocol. Each node was reviewed automatically for soundness of its natural-language proof, for faithfulness to the paper, and for agreement between its Lean statement and its natural-language statement. Juan J. Manfredi chose the targets, decided which cited results are carried as hypotheses, and approved the statements at the Trellis gate (after one revision, which restricted the cited results to the group of the theorem). The Lean kernel checks every proof.

## Citation

Please cite the paper; see [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0, the license of Mathlib. See [`LICENSE`](LICENSE).
