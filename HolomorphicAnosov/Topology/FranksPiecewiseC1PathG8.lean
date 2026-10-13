import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-piece C¹ paths in an original intrinsic leaf

Source: John Franks, *Anosov Diffeomorphisms*, Global Analysis, Part I (1970),
Proposition 1.1 and the intrinsic length definition, printed p.65, and Lemma 1.2 and
Corollary 1.3, pp.65–66. Hirsch–Pugh–Shub, *Invariant Manifolds* (1977), §7,
pp.115–116 supplies the native intrinsic foliation-chart context.

This module implements the C¹ finite-piece path notion of
`topo.franks_piecewise_c1_path_g8`. Franks's printed length argument uses piecewise smooth
paths; this definition does not assert an identity between that path class and the C¹ class.
No length, coefficient metric, completion, ambient-subspace topology or path existence is
introduced here. The supplied charted-space topology is the topology of the original leaf.
-/

namespace HolomorphicAnosov.Franks

/-- A path in a specified real C¹ manifold leaf, continuous on the closed unit interval and C¹
on each of a positive finite number of closed pieces. The original endpoints and adjacent
piece endpoints refer to the same single function. The division times are strictly increasing
from zero to one; no condition is imposed outside that interval and derivatives need not agree
at division times. This is the literal finite-piece C¹ definition in
`topo.franks_piecewise_c1_path_g8`, motivated by Franks (1970), pp.65–66 and the intrinsic
leaf charts of HPS (1977), pp.115–116. Rank zero and coincident endpoints are permitted;
there is no assertion of existence, completeness, connectedness or smoothness of the path.
-/
structure PiecewiseC1Path {r : ℕ} {L : Type*} [TopologicalSpace L]
    [ChartedSpace (EuclideanSpace ℝ (Fin r)) L]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin r))) 1 L]
    (x y : L) where
  toFun : ℝ → L
  continuousOn : ContinuousOn toFun (Set.Icc 0 1)
  pieces : ℕ
  pieces_pos : 0 < pieces
  division : Fin (pieces + 1) → ℝ
  division_strictMono : StrictMono division
  division_zero : division 0 = 0
  division_one : division (Fin.last pieces) = 1
  contMDiffOn_piece : ∀ i : Fin pieces,
    ContMDiffOn (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin r))) 1 toFun
      (Set.Icc (division i.castSucc) (division i.succ))
  source : toFun 0 = x
  target : toFun 1 = y

end HolomorphicAnosov.Franks
