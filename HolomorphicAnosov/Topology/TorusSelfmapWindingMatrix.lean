import HolomorphicAnosov.Topology.WindingBasepointChange
import HolomorphicAnosov.Topology.WindingEndomorphismMatrix
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Trace

open CategoryTheory
open scoped BigOperators
noncomputable section
universe u
namespace HolomorphicAnosov

/-- The original induced fundamental-group map determines one integer matrix
 simultaneously for every connecting path. Source: Hatcher's basepoint change
 and coordinate Hurewicz construction, pp.29–34 and166–168. -/
theorem torus_selfmap_winding_matrix (n : ℕ)
    (v : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ)) :
    ∃! A : Matrix (Fin n) (Fin n) ℤ,
      ∀ (δ : Path (v 0) (0 : UnitAddTorus (Fin n)))
        (γ : FundamentalGroup (UnitAddTorus (Fin n)) 0),
        (w ((FundamentalGroup.fundamentalGroupMulEquivOfPath δ)
          (FundamentalGroup.map v 0 γ))).toAdd = Matrix.mulVec A (w γ).toAdd := by
  let δ₀ := PathConnectedSpace.somePath (v 0) (0 : UnitAddTorus (Fin n))
  let f : Multiplicative (Fin n → ℤ) →* Multiplicative (Fin n → ℤ) :=
    w.toMonoidHom.comp ((FundamentalGroup.fundamentalGroupMulEquivOfPath δ₀).toMonoidHom.comp
      ((FundamentalGroup.map v 0).comp w.symm.toMonoidHom))
  obtain ⟨A, hA, hunique⟩ := winding_endomorphism_matrix n f
  refine ⟨A, ?_, ?_⟩
  · intro δ γ
    rw [winding_basepoint_change_independent n w δ δ₀]
    simpa [f] using hA (w γ).toAdd
  · intro B hB
    apply hunique B
    intro z
    simpa [f] using hB δ₀ (w.symm (Multiplicative.ofAdd z))



end HolomorphicAnosov
