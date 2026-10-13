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

namespace HolomorphicAnosov

universe u v

/-- Compatible maps on all finite skeleta glue continuously across the original
CW carrier, including at the accumulating deformation time. -/
theorem cw_prism_of_compatible_skeleta
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)]
    (F : ∀ n : ℕ, C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y))
    (hcompat : ∀ (m n : ℕ) (hmn : m ≤ n) (t : unitInterval)
      (x : (Topology.CWComplex.skeleton (Set.univ : Set K) (m : ℕ∞) : Set K)),
      F m (t, x) = F n (t, ⟨x.val, Topology.CWComplex.skeleton_mono
        (by exact_mod_cast hmn) x.property⟩)) :
    ∃ U : C(unitInterval × K, Y), ∀ (n : ℕ) (t : unitInterval)
      (x : (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)),
      U (t, x.val) = F n (t, x) := by
  classical
  let S : ℕ → Set K := fun n ↦
    (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)
  have hcover : ∀ x : K, ∃ n : ℕ, x ∈ S n := by
    intro x
    have hx : x ∈ ⋃ n : ℕ, S n := by
      rw [show (⋃ n : ℕ, S n) = Set.univ from
        Topology.CWComplex.iUnion_skeleton_eq_complex]
      exact Set.mem_univ _
    exact Set.mem_iUnion.mp hx
  let index : K → ℕ := fun x ↦ (hcover x).choose
  have hindex : ∀ x, x ∈ S (index x) := fun x ↦ (hcover x).choose_spec
  let U : unitInterval × K → Y :=
    fun q ↦ F (index q.2) (q.1, ⟨q.2, hindex q.2⟩)
  have hagree : ∀ n t (x : S n), U (t, x.val) = F n (t, x) := by
    intro n t x
    let N := max (index x.val) n
    have hi := hcompat (index x.val) N (le_max_left _ _) t
      (⟨x.val, hindex x.val⟩ : S (index x.val))
    have hn := hcompat n N (le_max_right _ _) t x
    exact hi.trans hn.symm
  have hcont : Continuous U := by
    apply cw_prism_continuous_of_characteristic
    intro n i
    let χ : C(Metric.closedBall (0 : Fin n → ℝ) 1, S n) :=
      ⟨fun z ↦ ⟨Topology.RelCWComplex.map n i z.val,
        Topology.CWComplex.closedCell_subset_skeleton n i
          ⟨z.val, z.property, rfl⟩⟩,
       ((Topology.RelCWComplex.continuousOn n i).domRestrict).subtype_mk _⟩
    have hc := (F n).continuous.comp
      (continuous_fst.prodMk (χ.continuous.comp continuous_snd))
    convert hc using 1
    funext q
    exact hagree n q.1 (χ q.2)
  exact ⟨⟨U, hcont⟩, hagree⟩

end HolomorphicAnosov
