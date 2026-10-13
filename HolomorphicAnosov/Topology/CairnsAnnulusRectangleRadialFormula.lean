import Mathlib.Analysis.InnerProductSpace.PiL2

open Set
namespace HolomorphicAnosov.Topology
noncomputable section
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The Euclidean radial formula on the closed rectangle before packaging its image as a subtype.
Source: Cairns (1951), preliminary 2(B), p.860, standard polar coordinates. -/
def cairns_annulus_rectangle_radial_formula
    (x : Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![x.1.2 * Real.cos (2 * Real.pi * x.1.1),
      x.1.2 * Real.sin (2 * Real.pi * x.1.1)]

end
end HolomorphicAnosov.Topology
