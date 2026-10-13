import HolomorphicAnosov.Topology.WindingBasepointChange
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-! Homotopy invariance of the original unbased winding matrix.
Source: Hatcher, Algebraic Topology, Lemma 1.19 and proof, pp.37–38, the induced
homomorphism under homotopy and basepoint-path conjugation. -/
noncomputable section
open CategoryTheory
namespace HolomorphicAnosov

/-- Homotopic self-maps of a torus have the same integer winding matrix, with
arbitrary connecting paths to the zero basepoint.

Proof: The homotopy induces a natural isomorphism on fundamental groupoids.
Its component at zero conjugates the induced homomorphism of the first map
to that of the second. Compose its basepoint path with a path to zero.
The resulting transport agrees with any other such transport because the
receiving torus fundamental group is abelian. Thus both matrices act equally
on every winding vector, which identifies the matrices. -/
theorem winding_matrix_homotopy (n : ℕ)
    (f g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (H : f.Homotopy g)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (A B : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ (p : Path (f 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath p
        (FundamentalGroup.map f 0 γ))).toAdd = A.mulVec (w γ).toAdd)
    (hB : ∀ (p : Path (g 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath p
        (FundamentalGroup.map g 0 γ))).toAdd = B.mulVec (w γ).toAdd) : A = B := by
  let p := PathConnectedSpace.somePath (f 0) (0 : UnitAddTorus (Fin n))
  let q := PathConnectedSpace.somePath (g 0) (0 : UnitAddTorus (Fin n))
  have haction (γ : FundamentalGroup (UnitAddTorus (Fin n)) 0) :
      FundamentalGroup.fundamentalGroupMulEquivOfPath p (FundamentalGroup.map f 0 γ) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath q (FundamentalGroup.map g 0 γ) := by
    let η := FundamentalGroupoidFunctor.homotopicMapsNatIso H
    let α := (Groupoid.isoEquivHom (FundamentalGroupoid.mk (f 0))
      (FundamentalGroupoid.mk (g 0))).symm ⟦H.evalAt 0⟧
    let β := (Groupoid.isoEquivHom (FundamentalGroupoid.mk (g 0))
      (FundamentalGroupoid.mk (0 : UnitAddTorus (Fin n)))).symm ⟦q⟧
    have hn : FundamentalGroup.map f 0 γ ≫ α.hom = α.hom ≫ FundamentalGroup.map g 0 γ :=
      η.naturality γ
    have ha : α.conj (FundamentalGroup.map f 0 γ) = FundamentalGroup.map g 0 γ := by
      rw [Iso.conj_apply, hn, ← Category.assoc, α.inv_hom_id,
        Category.id_comp]
    rw [winding_basepoint_change_independent n w p ((H.evalAt 0).trans q)]
    have hab : (Groupoid.isoEquivHom (FundamentalGroupoid.mk (f 0))
        (FundamentalGroupoid.mk (0 : UnitAddTorus (Fin n)))).symm
        ⟦(H.evalAt 0).trans q⟧ = α ≪≫ β := by
      apply Iso.ext
      rfl
    change ((Groupoid.isoEquivHom _ _).symm ⟦(H.evalAt 0).trans q⟧).conj
      (FundamentalGroup.map f 0 γ) = β.conj (FundamentalGroup.map g 0 γ)
    rw [hab, Iso.trans_conj, ha]
  apply Matrix.mulVec_injective
  funext z
  have hh := congrArg (fun γ ↦ (w γ).toAdd) (haction (w.symm (Multiplicative.ofAdd z)))
  simpa only [hA, hB, w.apply_symm_apply, toAdd_ofAdd] using hh

end HolomorphicAnosov
