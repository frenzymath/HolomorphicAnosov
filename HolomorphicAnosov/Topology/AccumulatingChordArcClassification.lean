import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Basic

namespace HolomorphicAnosov

open Set

/-! Circle arc classification used by the countable attached-chord providers. -/

/-- An open connected circle arc lies in one of the two directed arcs joining
its distinct frontier points. -/
theorem circle_arc_subset_directed_path
    (arcs : Set Circle) (u v : Circle)
    (hOpen : IsOpen arcs) (hConnected : IsConnected arcs)
    (hEndpoints : frontier arcs = {u, v}) (huv : u ≠ v) :
    arcs ⊆ (Circle.path u v '' Ioo 0 1) ∨
      arcs ⊆ (Circle.path v u '' Ioo 0 1) := by
  have huf : u ∉ arcs := by
    intro h
    have hi : u ∈ interior arcs := (subset_interior_iff_isOpen.mpr hOpen) h
    have hfr : u ∈ frontier arcs := by
      rw [hEndpoints]
      simp [huv]
    change u ∈ closure arcs \ interior arcs at hfr
    exact hfr.2 hi
  have hvf : v ∉ arcs := by
    intro h
    have hi : v ∈ interior arcs := (subset_interior_iff_isOpen.mpr hOpen) h
    have hfr : v ∈ frontier arcs := by
      rw [hEndpoints]
      simp
    change v ∈ closure arcs \ interior arcs at hfr
    exact hfr.2 hi
  let A : Set Circle := Circle.path u v '' Ioo 0 1
  let B : Set Circle := Circle.path v u '' Ioo 0 1
  have hAo : IsOpen A := by
    change IsOpen (Circle.path u v '' Ioo 0 1)
    rw [← Circle.compl_range_path huv.symm]
    exact (isCompact_range (Circle.path v u).continuous).isClosed.isOpen_compl
  have hBo : IsOpen B := by
    change IsOpen (Circle.path v u '' Ioo 0 1)
    rw [← Circle.compl_range_path huv]
    exact (isCompact_range (Circle.path u v).continuous).isClosed.isOpen_compl
  have hdisj : Disjoint A B := by
    exact (Circle.disjoint_path_image_Ioc huv).mono (image_mono Ioo_subset_Ioc_self)
      (image_mono Ioo_subset_Ioc_self)
  have hcov : arcs ⊆ A ∪ B := by
    intro z hz
    have hz0 : z ≠ u := by
      intro e
      subst z
      exact huf hz
    have hz1 : z ≠ v := by
      intro e
      subst z
      exact hvf hz
    have hz' : z ∈ range (Circle.path u v) ∨ z ∈ range (Circle.path v u) := by
      have hu := (Circle.range_path_union_range_path huv) ▸ (mem_univ z)
      simpa only [mem_union] using hu
    rcases hz' with hz' | hz'
    · left
      have hznot : z ∉ range (Circle.path v u) := by
        intro hboth
        have hend : z ∈ ({u, v} : Set Circle) := by
          rw [← Circle.range_path_inter_range_path huv]
          exact ⟨hz', hboth⟩
        simp [hz0, hz1] at hend
      change z ∈ Circle.path u v '' Ioo 0 1
      rw [← Circle.compl_range_path huv.symm]
      exact hznot
    · right
      have hznot : z ∉ range (Circle.path u v) := by
        intro hboth
        have hend : z ∈ ({u, v} : Set Circle) := by
          rw [← Circle.range_path_inter_range_path huv]
          exact ⟨hboth, hz'⟩
        simp [hz0, hz1] at hend
      change z ∈ Circle.path v u '' Ioo 0 1
      rw [← Circle.compl_range_path huv]
      exact hznot
  have hs : arcs ∩ (A ∩ B) = ∅ := by
    ext z
    constructor
    · intro hz
      exact (Set.disjoint_left.mp hdisj hz.2.1 hz.2.2).elim
    · intro hz
      exact hz.elim
  exact (isPreconnected_iff_subset_of_disjoint.mp hConnected.isPreconnected A B
    hAo hBo hcov hs)

/-- If such an arc is contained in a selected directed path and is nonempty,
then it equals that directed open path. -/
theorem circle_arc_eq_directed_path
    (arcs : Set Circle) (u v : Circle)
    (hOpen : IsOpen arcs) (hConnected : IsConnected arcs)
    (hEndpoints : frontier arcs = {u, v}) (huv : u ≠ v)
    (hsub : arcs ⊆ Circle.path u v '' Ioo 0 1) :
    arcs = Circle.path u v '' Ioo 0 1 := by
  let A : Set Circle := Circle.path u v '' Ioo 0 1
  have hAo : IsOpen A := by
    change IsOpen (Circle.path u v '' Ioo 0 1)
    rw [← Circle.compl_range_path huv.symm]
    exact (isCompact_range (Circle.path v u).continuous).isClosed.isOpen_compl
  have hApre : IsPreconnected A := by
    exact isPreconnected_Ioo.image _ (Circle.path u v).continuous.continuousOn
  have huf : u ∉ A := by
    intro hu
    obtain ⟨t, ht, he⟩ := hu
    have hzero : t = (0 : unitInterval) := by
      apply (Circle.path_injective_of_ne huv).eq_iff.mp
      simpa using he
    exact (by simpa [hzero] using ht.1)
  have hvf : v ∉ A := by
    intro hv
    obtain ⟨t, ht, he⟩ := hv
    have hone : t = (1 : unitInterval) := by
      apply (Circle.path_injective_of_ne huv).eq_iff.mp
      simpa using he
    exact (by simpa [hone] using ht.2)
  have hArc_closure : closure arcs = arcs ∪ {u, v} := by
    rw [closure_eq_self_union_frontier, hEndpoints]
  have hcover : A ⊆ arcs ∪ (closure arcs)ᶜ := by
    intro z hz
    by_cases hzcl : z ∈ closure arcs
    · left
      rw [hArc_closure] at hzcl
      rcases hzcl with hzarc | hzend
      · exact hzarc
      · rcases hzend with rfl | rfl
        · exact (huf hz).elim
        · exact (hvf hz).elim
    · exact Or.inr (show z ∈ (closure arcs)ᶜ from hzcl)
  have hdisj : Disjoint arcs ((closure arcs)ᶜ) := by
    apply Set.disjoint_left.mpr
    intro z hzA hzC
    exact hzC (subset_closure hzA)
  have hnonempty : (A ∩ arcs).Nonempty := by
    obtain ⟨z, hz⟩ := hConnected.nonempty
    exact ⟨z, hsub hz, hz⟩
  have hAarcs : A ⊆ arcs := by
    exact hApre.subset_left_of_subset_union hOpen isClosed_closure.isOpen_compl
      hdisj hcover hnonempty
  exact Subset.antisymm hsub hAarcs

end HolomorphicAnosov
