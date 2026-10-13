import Mathlib.Topology.Instances.AddCircle.Real

noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The original coordinate torus splits by its last coordinate. This is the product
homeomorphism used in the Künneth induction, including the empty first factor when n=0.
Its inverse appends the circle coordinate to the original finite tuple. -/
def torusSplitHomeomorph (n : ℕ) :
    UnitAddTorus (Fin (n + 1)) ≃ₜ UnitAddTorus (Fin n) × UnitAddCircle where
  toFun x := (Fin.init x, x (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := Fin.snoc_init_self x
  right_inv := by rintro ⟨x, z⟩; simp
  continuous_toFun := continuous_id.finInit.prodMk (continuous_apply (Fin.last n))
  continuous_invFun :=
    continuous_fst.finSnoc (A := fun _ : Fin (n + 1) ↦ UnitAddCircle) continuous_snd

end HolomorphicAnosov.TorusRationalCupBasisKronecker
