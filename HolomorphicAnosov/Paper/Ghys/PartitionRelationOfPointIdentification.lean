import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves

namespace HolomorphicAnosov.Ghys
/-- Point-preserving equivalences between intrinsic leaf carriers and specified point sets identify
the partition relation with membership in those sets. (HPS, pp.115–116; Ghys, pp.588–589) -/
theorem partition_relation_of_point_identification
    {M : Type*} (R : Setoid M) (P : M → M → Prop)
    (e : ∀ x : M, IntrinsicFoliationLeaf R (Quotient.mk R x) ≃ {y : M // P x y})
    (he : ∀ x z, (e x z).val = z.val) (x y : M) :
    R.r x y ↔ P x y := by
  constructor
  · intro hxy
    let z : IntrinsicFoliationLeaf R (Quotient.mk R x) :=
      ⟨y, Quotient.sound (R.symm hxy)⟩
    have hp := (e x z).property
    rwa [he x z] at hp
  · intro hxy
    obtain ⟨z, hz⟩ := (e x).surjective ⟨y, hxy⟩
    have hzy : z.val = y := (he x z).symm.trans (congrArg Subtype.val hz)
    have hr : R.r z.val x := Quotient.exact z.property
    exact hzy ▸ R.symm hr

end HolomorphicAnosov.Ghys
