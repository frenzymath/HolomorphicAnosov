import HolomorphicAnosov.Geometry.Holonomy.SameBoxCompositionGerm

/-! # The original plaque germ comparison across a homotopy cell  Nisoli, Theorem 1.3.8, printed pp.24–25: the two routes around one cell preserve the same transverse coordinate.    The comparison retains actual open plaque maps and requires only that they belong to the same original box. -/

namespace HolomorphicAnosov
open Filter
open scoped Topology _root_.Topology
universe u

/-- The first coordinates needed in one-box composition are forced by the original point equations. (Nisoli) -/
theorem same_box_composition_germ_of_box_eq {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M) {x y z : M}
    (e : LocalPlaqueTransport F x z) (l : LocalPlaqueTransport F x y)
    (r : LocalPlaqueTransport F y z)
    (hl : l.box = e.box) (hr : r.box = e.box) :
    (Germ.ofFun (r.map ∘ l.map) : Germ (𝓝 (F.uPoint x)) (F.ULeaf z)) =
      Germ.ofFun e.map := by
  have hlf := l.first_point
  have hls := l.second_point
  have hrf := r.first_point
  have hrs := r.second_point
  rw [hl] at hlf hls
  rw [hr] at hrf hrs
  have hfirst : l.first = e.first := congrArg Prod.fst
    ((F.box e.box).chart.injective (Subtype.ext (hlf.trans e.first_point.symm)))
  have hmid : l.second = r.first := congrArg Prod.fst
    ((F.box e.box).chart.injective (Subtype.ext (hls.trans hrf.symm)))
  have hlast : r.second = e.second := congrArg Prod.fst
    ((F.box e.box).chart.injective (Subtype.ext (hrs.trans e.second_point.symm)))
  exact same_box_composition_germ F e l r hl hr hfirst hmid hlast

/-- The two routes across a cell in one original plaque have identical germs. (Nisoli, Theorem 1.3.8) -/
theorem same_box_square_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M) {x y z w : M}
    (diagonal : LocalPlaqueTransport F x z)
    (bottom : LocalPlaqueTransport F x y) (right : LocalPlaqueTransport F y z)
    (left : LocalPlaqueTransport F x w) (top : LocalPlaqueTransport F w z)
    (hbottom : bottom.box = diagonal.box) (hright : right.box = diagonal.box)
    (hleft : left.box = diagonal.box) (htop : top.box = diagonal.box) :
    (Germ.ofFun (right.map ∘ bottom.map) : Germ (𝓝 (F.uPoint x)) (F.ULeaf z)) =
      Germ.ofFun (top.map ∘ left.map) := by
  exact (same_box_composition_germ_of_box_eq F diagonal bottom right hbottom hright).trans
    (same_box_composition_germ_of_box_eq F diagonal left top hleft htop).symm

end HolomorphicAnosov
