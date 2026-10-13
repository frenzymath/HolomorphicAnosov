import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTest

open MeasureTheory TopologicalSpace

namespace HolomorphicAnosov

open Set
open scoped ContDiff Topology _root_.Topology

/-- The bundled test operator has exactly the scalar Wirtinger convention,
with the factor one half and no complex conjugation. -/
theorem scalarDbarTest_apply {n : ℕ} (V : Opens (Fin n → ℂ))
    (j : Fin n) (φ : TestFunction V ℂ ⊤) (x : Fin n → ℂ) :
    scalarDbarTest V j φ x = Analysis.antiholomorphicPartial φ j x := by
  simp only [scalarDbarTest, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply, le_top, ite_true, Analysis.antiholomorphicPartial]
  ring


end HolomorphicAnosov
