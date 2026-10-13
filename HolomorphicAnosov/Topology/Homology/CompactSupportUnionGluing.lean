import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris

namespace HolomorphicAnosov
open CategoryTheory HolomorphicAnosov.Topology _root_.Topology
universe u

/-- Equal restrictions of local classes glue to a class on the union, with signed pair `(a,-b)`. (Hatcher, Lemma 3.27) -/
theorem compact_support_union_classes_glue (D : CompactSupportMVData.{u}) (q : ℕ)
    (a : supportSingularHomology D.space D.left D.coefficients q)
    (b : supportSingularHomology D.space D.right D.coefficients q)
    (hab : supportSingularHomologyRestrict D.space D.coefficients Set.inter_subset_left q a =
      supportSingularHomologyRestrict D.space D.coefficients Set.inter_subset_right q b) :
    ∃ c : supportSingularHomology D.space (D.left ∪ D.right) D.coefficients q,
      supportSingularHomologyRestrict D.space D.coefficients Set.subset_union_left q c = a ∧
      supportSingularHomologyRestrict D.space D.coefficients Set.subset_union_right q c = b := by
  obtain ⟨δ, hδ, _⟩ := hatcher_compact_support_mayer_vietoris
  have hker : supportMayerVietorisPsi D.space D.coefficients D.left D.right q (a, -b) = 0 := by
    change supportSingularHomologyRestrict D.space D.coefficients Set.inter_subset_left q a +
      supportSingularHomologyRestrict D.space D.coefficients Set.inter_subset_right q (-b) = 0
    rw [map_neg, hab, add_neg_cancel]
  obtain ⟨c, hc⟩ := ((hδ D).1 q).2.1 (a, -b) |>.mp hker
  refine ⟨c, ?_, ?_⟩
  · exact congrArg Prod.fst hc
  · have h := congrArg Prod.snd hc
    exact neg_injective h

end HolomorphicAnosov

