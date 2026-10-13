import Mathlib.Analysis.Complex.Exponential

/-!
Public DAG node: `analysis.mashreghi_angle_point_g3` (definition).
Definition origin: exponential circle parametrization in Mashreghi Theorem 4.3 equations (4.6)-(4.7), printed pp.442-443.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
namespace HolomorphicAnosov.MashreghiRadial
/-- Unit-circle parametrization in the target's order of multiplication.
Source: Mashreghi Theorem 4.3, equations (4.6)–(4.7), printed pp.442–443.
This is exp(iθ); the norm and real derivative facts are proved locally by Mathlib. -/
def anglePoint (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))
end HolomorphicAnosov.MashreghiRadial
