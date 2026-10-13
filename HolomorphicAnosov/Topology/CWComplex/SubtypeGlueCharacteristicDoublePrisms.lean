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

namespace HolomorphicAnosov

universe u v

/-- Two compact interval coordinates descend jointly through the original
characteristic maps of an inherited CW subcomplex. -/
theorem cw_subtype_glue_characteristic_double_prisms
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] (C : Set K) [Topology.CWComplex C]
    (P : ∀ (n : ℕ) (_ : Topology.RelCWComplex.cell C n),
      C(unitInterval × (unitInterval × Metric.closedBall (0 : Fin n → ℝ) 1), Y))
    (hcompat : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n)
      (m : ℕ) (j : Topology.RelCWComplex.cell C m)
      (s t : unitInterval) (z : Metric.closedBall (0 : Fin n → ℝ) 1)
      (w : Metric.closedBall (0 : Fin m → ℝ) 1),
      Topology.RelCWComplex.map n i z.val = Topology.RelCWComplex.map m j w.val →
      P n i (s, (t, z)) = P m j (s, (t, w))) :
    ∃ H : C(unitInterval × (unitInterval × C), Y), ∀ n i s t z,
      H (s, (t, ⟨Topology.RelCWComplex.map n i z.val,
        Topology.RelCWComplex.closedCell_subset_complex n i ⟨z.val, z.property, rfl⟩⟩)) =
      P n i (s, (t, z)) := by
  let Q (n : ℕ) (i : Topology.RelCWComplex.cell C n) :
      C(unitInterval × Metric.closedBall (0 : Fin n → ℝ) 1, C(unitInterval, Y)) :=
    ContinuousMap.curry ⟨fun q ↦ P n i (q.2, q.1),
      (P n i).continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  have hQ : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n)
      (m : ℕ) (j : Topology.RelCWComplex.cell C m)
      (t : unitInterval) (z : Metric.closedBall (0 : Fin n → ℝ) 1)
      (w : Metric.closedBall (0 : Fin m → ℝ) 1),
      Topology.RelCWComplex.map n i z.val = Topology.RelCWComplex.map m j w.val →
      Q n i (t, z) = Q m j (t, w) := by
    intro n i m j t z w heq
    apply ContinuousMap.ext
    intro s
    exact hcompat n i m j s t z w heq
  obtain ⟨G, hG⟩ := cw_subtype_glue_characteristic_prisms C Q hQ
  have hswap : Continuous (fun q : unitInterval × (unitInterval × C) ↦
      ((q.2.1, q.2.2), q.1)) :=
    ((continuous_fst.comp continuous_snd).prodMk
      (continuous_snd.comp continuous_snd)).prodMk continuous_fst
  let H : C(unitInterval × (unitInterval × C), Y) :=
    ⟨fun q ↦ G (q.2.1, q.2.2) q.1,
      (ContinuousMap.uncurry G).continuous.comp hswap⟩
  refine ⟨H, ?_⟩
  intro n i s t z
  exact congrArg (fun f : C(unitInterval, Y) ↦ f s) (hG n i t z)

end HolomorphicAnosov
