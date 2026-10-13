import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory TopologicalSpace

namespace HolomorphicAnosov

open Set
open scoped ContDiff Topology _root_.Topology

/-- The genuine test-function operator in the public current hypothesis. -/
noncomputable def scalarDbarTest {n : ℕ} (V : Opens (Fin n → ℂ))
    (j : Fin n) (φ : TestFunction V ℂ ⊤) : TestFunction V ℂ ⊤ :=
  (2 : ℂ)⁻¹ • ((TestFunction.lineDerivCLM ℂ (Pi.single j 1) φ :
    TestFunction V ℂ ⊤) + Complex.I •
      (TestFunction.lineDerivCLM ℂ (Pi.single j Complex.I) φ : TestFunction V ℂ ⊤))


end HolomorphicAnosov
