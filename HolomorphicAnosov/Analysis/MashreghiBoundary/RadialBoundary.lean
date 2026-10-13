import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialRadius

/-!
Public DAG node: `analysis.mashreghi_radial_boundary_g3` (definition).
Definition origin: radial boundary value in Mashreghi Theorem 4.3 forward proof, printed p.442; implemented by limUnder on the fixed interior sequence.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
open Filter
namespace HolomorphicAnosov.MashreghiRadial
/-- Radial boundary value indexed by the complex point rather than its angle.
Source: Mashreghi Theorem 4.3, printed p.442, definition of the radial limit.
The total limUnder expression carries explicit data; convergence on unit points
is supplied separately by the Cauchy theorem and completeness of the complex numbers. -/
def radialBoundary (F : ℂ → ℂ) (η : ℂ) : ℂ :=
  limUnder atTop (fun n : ℕ ↦ F ((radialRadius n : ℂ) * η))
end HolomorphicAnosov.MashreghiRadial
