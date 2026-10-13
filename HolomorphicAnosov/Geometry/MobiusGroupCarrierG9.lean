import HolomorphicAnosov.Geometry.ComplexMobiusOnePointBridge
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology

noncomputable section
namespace HolomorphicAnosov
open Ghys

/-- The projective Möbius transformation corresponding to a Möbius permutation of the one-point
compactification of `ℂ`. -/
def mobiusGroupToComplexMobius (g : MobiusGroup) : ComplexMobiusTransformation :=
  let ep : OnePoint ℂ ≃ ComplexProjectiveLine := OnePoint.equivProjectivization ℂ
  let v : ComplexProjectiveLine ≃ ComplexProjectiveLine :=
    (ep.symm.trans g.val).trans ep
  ⟨v, by
    obtain ⟨m, hm⟩ := g.property
    refine ⟨m, ?_⟩
    intro p
    apply ep.symm.injective
    dsimp [v, ep]
    rw [Equiv.symm_apply_apply]
    change g.val (ep.symm p) = ep.symm (m • p)
    have hsmul : ep.symm (m • p) = m • ep.symm p := by
      apply ep.injective
      rw [Equiv.apply_symm_apply]
      have hh := (OnePoint.equivProjectivization_smul (K := ℂ) (g := m)
        (x := ep.symm p)).symm
      rw [Equiv.apply_symm_apply] at hh
      exact hh
    rw [hsmul]
    change g.val (ep.symm p) = (MulAction.toPerm m) (ep.symm p)
    exact (congrArg (fun e : Equiv.Perm (OnePoint ℂ) ↦ e (ep.symm p)) hm).symm⟩

/-- The carrier conversion intertwines the Möbius actions under `OnePoint.equivProjectivization ℂ`. -/
theorem mobiusGroupToComplexMobius_apply (g : MobiusGroup) (p : ComplexProjectiveLine) :
    (mobiusGroupToComplexMobius g).apply p =
      (OnePoint.equivProjectivization ℂ)
        (g.apply ((OnePoint.equivProjectivization ℂ).symm p)) := by
  obtain ⟨m, hm⟩ := g.property
  apply (OnePoint.equivProjectivization ℂ).symm.injective
  simp [mobiusGroupToComplexMobius, ComplexMobiusTransformation.apply,
    MobiusGroup.apply, Equiv.trans_apply, Equiv.symm_apply_apply]

end HolomorphicAnosov
