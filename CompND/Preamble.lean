-- Preamble: shared imports for all tablet nodes.
-- Specific Mathlib imports only (never `import Mathlib`).

-- Frechet derivatives, higher smoothness and the Lie bracket of vector fields.
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.VectorField

-- The ambient spaces `EuclideanSpace ℝ (Fin N)` and real powers.
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Matrices: trace and symmetry.
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric

-- Convexity (for semi-convexity) and semi-continuity (for viscosity solutions).
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Topology.Connected.Basic

-- Lebesgue measure on `EuclideanSpace ℝ (Fin N)` (a.e. statements, Jensen's lemma).
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
