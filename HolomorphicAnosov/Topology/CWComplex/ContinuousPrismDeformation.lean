import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction
import HolomorphicAnosov.Topology.CWComplex.RadialScaleBounds
import HolomorphicAnosov.Topology.CWComplex.RadialHeightBounds
import HolomorphicAnosov.Topology.CWComplex.RadialNormBound
import HolomorphicAnosov.Topology.CWComplex.RadialProjection
import HolomorphicAnosov.Topology.CWComplex.ContinuousRadialProjection
import HolomorphicAnosov.Topology.CWComplex.RadialBottom
import HolomorphicAnosov.Topology.CWComplex.RadialSide
import HolomorphicAnosov.Topology.CWComplex.RadialBoundaryTarget
import HolomorphicAnosov.Topology.CWComplex.RadialCharacteristicFrontier
import HolomorphicAnosov.Topology.CWComplex.RadialCharacteristicTarget
import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeleta
import HolomorphicAnosov.Topology.CWComplex.SubtypeGlueCharacteristicDoublePrisms
import HolomorphicAnosov.Topology.CWComplex.CellBoundaryNeSameDimInterior
import HolomorphicAnosov.Topology.CWComplex.RadialSameDimCompatible
import HolomorphicAnosov.Topology.CWComplex.PrismDeformation

namespace HolomorphicAnosov

universe u v

/-- The local deformation is jointly continuous in deformation time, disk
coordinate, and prism time. -/
theorem continuous_cw_prism_deform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (cw_prism_deform (E := E)) := by
  let D := Metric.closedBall (0 : E) 1
  let R := cw_prism_radial (E := E)
  have hr : Continuous (fun q : unitInterval × (D × unitInterval) ↦ R q.2) :=
    continuous_cw_prism_radial.comp continuous_snd
  have hs : Continuous (fun q : unitInterval × (D × unitInterval) ↦
      (q.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun q : unitInterval × (D × unitInterval) ↦
      q.2.1.val) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hy : Continuous (fun q : unitInterval × (D × unitInterval) ↦
      (R q.2).1.val) := continuous_subtype_val.comp (continuous_fst.comp hr)
  have hcoeff : Continuous (fun q : unitInterval × (D × unitInterval) ↦
      (1 : ℝ) - (q.1 : ℝ)) := continuous_const.sub hs
  have hdiskraw : Continuous (fun q : unitInterval × (D × unitInterval) ↦
      ((1 : ℝ) - (q.1 : ℝ)) • q.2.1.val +
        (q.1 : ℝ) • (R q.2).1.val) := (hcoeff.smul hx).add (hs.smul hy)
  have hdisk : Continuous (fun q : unitInterval × (D × unitInterval) ↦
      (cw_prism_deform q).1) := by
    convert hdiskraw.subtype_mk (fun q ↦ (cw_prism_deform q).1.property) using 1
    funext q
    apply Subtype.ext
    rfl
  have hheight : Continuous (fun q : unitInterval × (D × unitInterval) ↦
      (cw_prism_deform q).2) := by
    have hraw : Continuous (fun q : unitInterval × (D × unitInterval) ↦
        Set.Icc.convexComb q.2.2 (R q.2).2 q.1) :=
      Set.Icc.continuous_convexComb_prod.comp
        ((continuous_snd.comp continuous_snd).prodMk
          ((continuous_snd.comp hr).prodMk continuous_fst))
    convert hraw using 1
    funext q
    rfl
  exact hdisk.prodMk hheight

end HolomorphicAnosov
