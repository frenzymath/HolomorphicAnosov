import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.EvaluatedKernelElementLift
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- The coboundary of an ambient cochain extending a subspace cocycle is the
image of a relative cocycle. Source: Hatcher, *Algebraic Topology*, pp.199–200.
The coboundary restricts to zero because restriction commutes with differential.
Lift it into the evaluated kernel complex. Its next differential vanishes after
the monic kernel inclusion, by the differential-square identity, hence vanishes. -/
theorem singular_relative_cocycle_of_extension (R : Type u) [CommRing R] (X : TopCat.{u}) (A : Set X) (n : ℕ)
    (α : cycles R (complex R (TopCat.of A)) n) (b : cochains R X n)
    (hb : (pullback R (subspaceInclusion X A)).f n b = α.val) :
    ∃ β : cycles R (relativeComplex R X A) (n+1),
      (kernel.ι (pullback R (subspaceInclusion X A))).f (n+1) β.val =
        (complex R X).d n (n+1) b := by
  let p := pullback R (subspaceInclusion X A)
  have hα : (complex R (TopCat.of A)).d n (n+1) α.val = 0 := by
    have h := α.property
    change (complex R (TopCat.of A)).d n ((ComplexShape.up ℕ).next n) α.val = 0 at h
    exact (congrArg (fun j => (complex R (TopCat.of A)).d n j α.val = 0)
      (CochainComplex.next ℕ n)).mp h
  have hz : p.f (n+1) ((complex R X).d n (n+1) b) = 0 := by
    change ((complex R X).d n (n+1) ≫ p.f (n+1)) b = 0
    rw [← p.comm]
    change (complex R (TopCat.of A)).d n (n+1) (p.f n b) = 0
    rw [hb]
    exact hα
  obtain ⟨y, hy⟩ := evaluated_kernel_element_lift p (n+1) _ hz
  have hcycle : y ∈ cycles R (relativeComplex R X A) (n+1) := by
    apply (ModuleCat.mono_iff_injective ((kernel.ι p).f ((ComplexShape.up ℕ).next (n+1)))).mp inferInstance
    change ((kernel p).d (n+1) _ ≫ (kernel.ι p).f _) y = _
    rw [← (kernel.ι p).comm]
    change (complex R X).d (n+1) _ ((kernel.ι p).f (n+1) y) = _
    rw [hy]
    change ((complex R X).d n (n+1) ≫ (complex R X).d (n+1) _) b = _
    rw [HomologicalComplex.d_comp_d]
    simp
  exact ⟨⟨y, hcycle⟩, hy⟩
end HolomorphicAnosov.SingularCochain

