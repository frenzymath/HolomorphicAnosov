import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialBoundary

/-!
Public DAG node: `analysis.mashreghi_disk_extension_g3` (definition).
Definition origin: continuous extension asserted in Mashreghi Theorem 4.3, printed pp.442-443. On the open disk use F; on the unit circle use its constructed radial value; outside values are arbitrary.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
namespace HolomorphicAnosov.MashreghiRadial
/-- Total extension using F inside the disk and radial boundary values elsewhere.
Source: the extension asserted in Mashreghi Theorem 4.3, printed pp.442–443.
Only its values on the closed disk are specified by the theorem; the total
outside values selected here create no additional hypothesis or conclusion. -/
def diskExtension (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ < 1 then F z else radialBoundary F z
end HolomorphicAnosov.MashreghiRadial
