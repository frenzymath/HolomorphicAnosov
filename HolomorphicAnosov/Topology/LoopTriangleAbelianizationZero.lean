import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Alternating abelianized class of a based-loop triangle

Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof, p.167;
ordered simplex faces, pp.103–104.
-/

noncomputable section
universe u
namespace HolomorphicAnosov.Topology

/-- Three based loops satisfying a triangle homotopy have zero alternating
boundary class in the fundamental group's abelianization. Source: Hatcher,
Algebraic Topology, Theorem 2A.1 proof p.167. The homotopy identifies the
concatenation class with the third class. Mathlib's fundamental-group product
has the reversed path-composition convention; after abelianization its two
factors commute, giving exactly the alternating face order beta-gamma+alpha. -/
theorem loopTriangle_abelianization_zero {X : Type u} [TopologicalSpace X]
    {x : X} (α β γ : Path x x) (h : (α.trans β).Homotopic γ) :
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk β))) -
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk γ))) +
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk α))) = 0 := by
  have heq : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β) *
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) :=
    Quotient.sound h
  have hadd := congrArg (fun a : FundamentalGroup X x ↦
    Additive.ofMul (Abelianization.of a)) heq
  rw [map_mul] at hadd
  change Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk β))) +
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk α))) = _ at hadd
  rw [← hadd]
  abel

end HolomorphicAnosov.Topology
