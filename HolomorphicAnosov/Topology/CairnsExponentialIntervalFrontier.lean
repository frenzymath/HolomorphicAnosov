import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace HolomorphicAnosov.Topology.Plane
open Set

/-- The frontier of an exponential interval of length at most one turn is
its two endpoint images. The equality case permits coincident endpoint images.
Compactness computes the closure, openness of the exponential computes the
frontier, and injectivity on either half-open period excludes the endpoints
from the open interval image. -/
theorem cairns_exp_interval_frontier
    (a b : ℝ) (hab : a < b) (hturn : b - a ≤ 2 * Real.pi) :
    frontier (Circle.exp '' Ioo a b) = {Circle.exp a, Circle.exp b} := by
  have hopen : IsOpen (Circle.exp '' Ioo a b) :=
    isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo
  have hclosure : closure (Circle.exp '' Ioo a b) = Circle.exp '' Icc a b := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono Ioo_subset_Icc_self)
        (isCompact_Icc.image Circle.exp.continuous).isClosed
    · rw [← closure_Ioo hab.ne]
      exact image_closure_subset_closure_image Circle.exp.continuous
  rw [hopen.frontier_eq, hclosure]
  ext z
  constructor
  · rintro ⟨⟨t,ht,rfl⟩, hnot⟩
    rcases lt_or_eq_of_le ht.1 with hta | hta
    · rcases lt_or_eq_of_le ht.2 with htb | htb
      · exact (hnot ⟨t,⟨hta,htb⟩,rfl⟩).elim
      · right; exact congrArg Circle.exp htb
    · left; exact congrArg Circle.exp hta.symm
  · intro hz
    rcases hz with rfl | rfl
    · constructor
      · exact ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
      · rintro ⟨t, ht, hte⟩
        have hta : t = a := Circle.exp_injOn_Ico hturn ⟨ht.1.le, ht.2⟩ ⟨le_rfl, hab⟩ hte
        exact (ne_of_gt ht.1) hta
    · constructor
      · exact ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩
      · rintro ⟨t, ht, hte⟩
        have htb : t = b := Circle.exp_injOn_Ioc hturn ⟨ht.1, ht.2.le⟩ ⟨hab, le_rfl⟩ hte
        exact (ne_of_lt ht.2) htb

end HolomorphicAnosov.Topology.Plane
