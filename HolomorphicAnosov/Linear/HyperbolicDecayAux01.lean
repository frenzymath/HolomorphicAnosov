import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.TensorProduct.Basis

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- The set of vectors whose forward iterates decay, equipped with its real submodule structure. (Alves, Definition 5.4) -/
def fullForwardDecay {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (A : V ≃L[𝕜] V) : Submodule 𝕜 V where
  carrier := {v | Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 (0 : V))}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq, map_add, zero_add] using hx.add hy
  smul_mem' := by
    intro a v hv
    simpa only [Set.mem_ofPred_eq, map_smul, smul_zero] using hv.const_smul a



end HolomorphicAnosov
