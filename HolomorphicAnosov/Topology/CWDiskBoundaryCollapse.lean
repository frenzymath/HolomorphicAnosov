import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Compactification.OnePoint.Sphere
import HolomorphicAnosov.Topology.CWComplex.EuclideanSupRadialHomeomorph
import HolomorphicAnosov.Topology.CubicalCharacteristicParameterG8

/-!
# Sphere characteristic disks and their cones

Source: Fritsch–Piccinini, Cellular Structures in Topology (1990), the
punctured-sphere decomposition in §1.1 and cone construction in Lemma 2.3.7,
printed p.67. A one-point compactification constructs the sphere's minimal
characteristic disk; radial coordinates construct its cone in the max norm.
-/

open Set _root_.Topology

namespace HolomorphicAnosov
universe u
noncomputable section

/-- Collapse the complement of an open subset to the added point. -/
def openSubsetCollapse {X : Type*} (U : Set X) (x : X) : OnePoint U := by
  classical
  exact if h : x ∈ U then OnePoint.some ⟨x, h⟩ else OnePoint.infty

@[simp] theorem openSubsetCollapse_coe {X : Type*} (U : Set X) (x : U) :
    openSubsetCollapse U x = OnePoint.some x := by
  simp [openSubsetCollapse, x.property]

theorem continuous_openSubsetCollapse {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : Set X} (hU : IsOpen U) : Continuous (openSubsetCollapse U) := by
  classical
  apply continuous_def.mpr
  intro S hS
  by_cases hi : OnePoint.infty ∈ S
  · have hcompact := ((OnePoint.isOpen_iff_of_mem hi).mp hS).2
    have heq : openSubsetCollapse U ⁻¹' S =
        (Subtype.val '' ((OnePoint.some ⁻¹' S : Set U)ᶜ))ᶜ := by
      ext x
      by_cases hx : x ∈ U
      · simp only [mem_preimage, openSubsetCollapse, dite_eq_left hx, mem_compl_iff,
          mem_image, mem_preimage]
        constructor
        · intro hs ⟨y, hy, hyx⟩
          have hey : y = ⟨x, hx⟩ := Subtype.ext hyx
          exact hy (hey ▸ hs)
        · intro hn
          by_contra hs
          exact hn ⟨⟨x, hx⟩, hs, rfl⟩
      · simp only [mem_preimage, openSubsetCollapse, dite_eq_right hx, hi, mem_compl_iff,
          mem_image, true_iff]
        rintro ⟨y, _, hyx⟩
        exact hx (hyx ▸ y.property)
    rw [heq]
    exact (hcompact.image continuous_subtype_val).isClosed.isOpen_compl
  · have heq : openSubsetCollapse U ⁻¹' S =
        Subtype.val '' (OnePoint.some ⁻¹' S : Set U) := by
      ext x
      by_cases hx : x ∈ U
      · simp only [mem_preimage, openSubsetCollapse, dite_eq_left hx, mem_image]
        constructor
        · intro hs
          exact ⟨⟨x, hx⟩, hs, rfl⟩
        · rintro ⟨y, hy, hyx⟩
          have hey : y = ⟨x, hx⟩ := Subtype.ext hyx
          exact hey ▸ hy
      · simp only [mem_preimage, openSubsetCollapse, dite_eq_right hx, hi, mem_image,
          false_iff, not_exists, not_and]
        intro y hy hyx
        exact hx (hyx ▸ y.property)
    rw [heq]
    exact hU.isOpenEmbedding_subtypeVal.isOpenMap _
      ((OnePoint.isOpen_iff_of_notMem hi).mp hS)

/-- The closed characteristic disk mapped to the one-point compactification,
with its boundary sent to infinity. -/
def diskBoundaryCollapse (d : ℕ) (v : Fin d → ℝ) : OnePoint (Fin d → ℝ) :=
  (Homeomorph.unitBall (E := Fin d → ℝ)).symm.onePointCongr
    (openSubsetCollapse (Metric.ball (0 : Fin d → ℝ) 1) v)

theorem continuous_diskBoundaryCollapse (d : ℕ) : Continuous (diskBoundaryCollapse d) :=
  (Homeomorph.unitBall (E := Fin d → ℝ)).symm.onePointCongr.continuous.comp
    (continuous_openSubsetCollapse Metric.isOpen_ball)

theorem diskBoundaryCollapse_interior (d : ℕ) (v : Metric.ball (0 : Fin d → ℝ) 1) :
    diskBoundaryCollapse d v =
      OnePoint.some ((Homeomorph.unitBall (E := Fin d → ℝ)).symm v) := by
  dsimp only [diskBoundaryCollapse]
  rw [openSubsetCollapse_coe]
  rfl

theorem diskBoundaryCollapse_boundary (d : ℕ) (v : Fin d → ℝ)
    (hv : v ∈ Metric.sphere 0 1) : diskBoundaryCollapse d v = OnePoint.infty := by
  have hv' : v ∉ Metric.ball (0 : Fin d → ℝ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, show ‖v‖ = 1 by simpa using hv]
    exact lt_irrefl 1
  dsimp only [diskBoundaryCollapse, openSubsetCollapse]
  rw [dite_eq_right hv']
  rfl

/-- The interior chart underlying the boundary collapse. -/
def diskInteriorChart (d : ℕ) :
    OpenPartialHomeomorph (Fin d → ℝ) (OnePoint (Fin d → ℝ)) :=
  OpenPartialHomeomorph.univUnitBall.symm.trans
    (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph OnePoint.some)

@[simp] theorem diskInteriorChart_source (d : ℕ) :
    (diskInteriorChart d).source = Metric.ball 0 1 := by
  simp [diskInteriorChart, OpenPartialHomeomorph.univUnitBall]

@[simp] theorem diskInteriorChart_target (d : ℕ) :
    (diskInteriorChart d).target = Set.range OnePoint.some := by
  simp [diskInteriorChart, OpenPartialHomeomorph.univUnitBall]

theorem diskBoundaryCollapse_eq_chart (d : ℕ) {v : Fin d → ℝ}
    (hv : v ∈ Metric.ball 0 1) : diskBoundaryCollapse d v = diskInteriorChart d v := by
  rw [show diskBoundaryCollapse d v =
    OnePoint.some ((Homeomorph.unitBall (E := Fin d → ℝ)).symm ⟨v, hv⟩) from
      diskBoundaryCollapse_interior d ⟨v, hv⟩]
  rfl

/-- The total characteristic map is changed only off its open source, to make
all boundary values the point at infinity. -/
def diskBoundaryCollapsePartialEquiv (d : ℕ) :
    PartialEquiv (Fin d → ℝ) (OnePoint (Fin d → ℝ)) where
  toFun := diskBoundaryCollapse d
  invFun := (diskInteriorChart d).symm
  source := (diskInteriorChart d).source
  target := (diskInteriorChart d).target
  map_source' := by
    intro v hv
    rw [diskBoundaryCollapse_eq_chart d (by simpa using hv)]
    exact (diskInteriorChart d).map_source hv
  map_target' := fun _ hx ↦ (diskInteriorChart d).map_target hx
  left_inv' := by
    intro v hv
    rw [diskBoundaryCollapse_eq_chart d (by simpa using hv)]
    exact (diskInteriorChart d).left_inv hv
  right_inv' := by
    intro v hv
    rw [diskBoundaryCollapse_eq_chart d
      (by simpa using (diskInteriorChart d).map_target hv)]
    exact (diskInteriorChart d).right_inv hv

/-- One-point compactification in the native max-norm characteristic coordinates. -/
def onePointSupSphereHomeomorph (d : ℕ) :
    OnePoint (Fin d → ℝ) ≃ₜ Metric.sphere (0 : Fin (d + 1) → ℝ) 1 := by
  let e := (euclidean_sup_radial_homeomorph (d + 1)).choose
  have he := (euclidean_sup_radial_homeomorph (d + 1)).choose_spec
  let es : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 ≃ₜ
      Metric.sphere (0 : Fin (d + 1) → ℝ) 1 :=
    e.subtype (by
      intro z
      simp only [Metric.mem_sphere, dist_zero_right]
      change ‖z‖ = 1 ↔ ‖(euclidean_sup_radial_homeomorph (d + 1)).choose z‖ = 1
      rw [he])
  exact (onePointEquivSphereOfFinrankEq (by simp)).trans es

/-- The characteristic map of the positive cell in the minimal sphere structure. -/
def sphereDiskCharacteristic (d : ℕ) :
    PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin (d + 1) → ℝ) 1) :=
  (diskBoundaryCollapsePartialEquiv d).transEquiv (onePointSupSphereHomeomorph d).toEquiv

@[simp] theorem sphereDiskCharacteristic_source (d : ℕ) :
    (sphereDiskCharacteristic d).source = Metric.ball 0 1 :=
  diskInteriorChart_source d

theorem sphereDiskCharacteristic_target (d : ℕ) :
    (sphereDiskCharacteristic d).target =
      {onePointSupSphereHomeomorph d OnePoint.infty}ᶜ := by
  ext z
  change (onePointSupSphereHomeomorph d).symm z ∈ (diskInteriorChart d).target ↔ _
  rw [diskInteriorChart_target, ← OnePoint.compl_infty]
  simp only [mem_compl_iff, mem_singleton_iff]
  exact not_congr (Homeomorph.symm_apply_eq _)

theorem sphereDiskCharacteristic_continuous (d : ℕ) :
    Continuous (sphereDiskCharacteristic d) :=
  (onePointSupSphereHomeomorph d).continuous.comp (continuous_diskBoundaryCollapse d)

theorem sphereDiskCharacteristic_continuousOn_symm (d : ℕ) :
    ContinuousOn (sphereDiskCharacteristic d).symm (sphereDiskCharacteristic d).target := by
  exact (diskInteriorChart d).continuousOn_symm.comp
    (onePointSupSphereHomeomorph d).symm.continuous.continuousOn (fun _ hz ↦ hz)

theorem sphereDiskCharacteristic_boundary (d : ℕ) {v : Fin d → ℝ}
    (hv : v ∈ Metric.sphere 0 1) :
    sphereDiskCharacteristic d v = onePointSupSphereHomeomorph d OnePoint.infty := by
  change onePointSupSphereHomeomorph d (diskBoundaryCollapse d v) = _
  rw [diskBoundaryCollapse_boundary d v hv]

/-- The minimal sphere characteristic disk has precisely the usual open cell;
its entire boundary maps to the omitted sphere vertex. Source: Fritsch–Piccinini,
Cellular Structures in Topology, §1.1 sphere decomposition (printed p.11), and Lemma 2.3.7 p.67.

Proof: collapse the complement of the open disk to infinity in its one-point
compactification. This map is continuous: an open neighborhood of infinity
pulls back to the complement of the compact image of a closed compact set in
the open disk; an open set avoiding infinity pulls back to an open subset of
the open disk. The usual ball homeomorphism identifies that open disk with
Euclidean coordinate space. The one-point sphere homeomorphism, followed by
norm-preserving radial conversion, gives the stated max-norm sphere chart.
The original interior charts give the inverse continuity and bijection laws.
Boundary points are outside the open disk, so all map to the sphere vertex.
This includes d=0, where the disk is a point and its boundary is empty. -/
theorem cw_minimal_sphere_characteristic (d : ℕ) :
    ∃ (θ : Metric.sphere (0 : Fin (d + 1) → ℝ) 1)
      (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin (d + 1) → ℝ) 1)),
      χ.source = Metric.ball 0 1 ∧ χ.target = {θ}ᶜ ∧
      Continuous χ ∧ ContinuousOn χ.symm χ.target ∧
      ∀ v ∈ Metric.sphere (0 : Fin d → ℝ) 1, χ v = θ := by
  exact ⟨onePointSupSphereHomeomorph d OnePoint.infty, sphereDiskCharacteristic d,
    sphereDiskCharacteristic_source d, sphereDiskCharacteristic_target d,
    sphereDiskCharacteristic_continuous d, sphereDiskCharacteristic_continuousOn_symm d,
    fun _ hv ↦ sphereDiskCharacteristic_boundary d hv⟩

/-- Radial direction, with a prescribed value at the origin. -/
def sphereDirection (n : ℕ) (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (y : Fin n → ℝ) : Metric.sphere (0 : Fin n → ℝ) 1 := by
  classical
  exact if hy : y = 0 then θ else
    ⟨‖y‖⁻¹ • y, by simp [norm_smul, hy]⟩

theorem sphereDirection_smul (n : ℕ)
    (θ s : Metric.sphere (0 : Fin n → ℝ) 1) {t : ℝ} (ht : 0 < t) :
    sphereDirection n θ (t • s.val) = s := by
  have hs : ‖s.val‖ = 1 := by simp
  have hs0 : s.val ≠ 0 := by intro h; simp [h] at hs
  have hne : t • s.val ≠ 0 := smul_ne_zero ht.ne' hs0
  apply Subtype.ext
  simp [sphereDirection, hne, norm_smul, hs, abs_of_pos ht, smul_smul, ht.ne']

/-- Full characteristic parameter for the cone over the punctured sphere cell. -/
def coneCharacteristicMap (d n : ℕ)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    (v : Fin (d + 1) → ℝ) : Fin n → ℝ :=
  ((v 0 + 1) / 2) • (χ (Fin.tail v)).val

def coneCharacteristicInverse (d n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    (y : Fin n → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons (2 * ‖y‖ - 1) (χ.symm (sphereDirection n θ y))

theorem coneCharacteristic_coordinates (d : ℕ) {v : Fin (d + 1) → ℝ}
    (hv : v ∈ Metric.ball 0 1) :
    0 < (v 0 + 1) / 2 ∧ (v 0 + 1) / 2 < 1 ∧
      Fin.tail v ∈ Metric.ball (0 : Fin d → ℝ) 1 := by
  have hcoord : ∀ j, |v j| < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff zero_lt_one,
      Real.norm_eq_abs] using hv
  have h0 := abs_lt.mp (hcoord 0)
  refine ⟨by linarith, by linarith, ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff zero_lt_one,
    Real.norm_eq_abs, Fin.tail] using fun j : Fin d ↦ hcoord j.succ

theorem coneCharacteristic_left_inverse (d n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    (hs : χ.source = Metric.ball 0 1) {v : Fin (d + 1) → ℝ}
    (hv : v ∈ Metric.ball 0 1) :
    coneCharacteristicInverse d n θ χ (coneCharacteristicMap d n χ v) = v := by
  have hc := coneCharacteristic_coordinates d hv
  have hnorm : ‖coneCharacteristicMap d n χ v‖ = (v 0 + 1) / 2 := by
    rw [coneCharacteristicMap, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1,
      show ‖(χ (Fin.tail v)).val‖ = 1 by simp, mul_one]
  have hdir : sphereDirection n θ (coneCharacteristicMap d n χ v) = χ (Fin.tail v) :=
    sphereDirection_smul n θ _ hc.1
  simp only [coneCharacteristicInverse, hnorm, hdir, χ.left_inv (hs ▸ hc.2.2)]
  rw [show 2 * ((v 0 + 1) / 2) - 1 = v 0 by ring, Fin.cons_self_tail]


def coneCharacteristicTarget (d n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1)) :
    Set (Fin n → ℝ) :=
  {y | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ sphereDirection n θ y ∈ χ.target}

theorem coneCharacteristic_mapsTo (d n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    (hs : χ.source = Metric.ball 0 1) :
    MapsTo (coneCharacteristicMap d n χ) (Metric.ball 0 1) (coneCharacteristicTarget d n θ χ) := by
  intro v hv
  have hc := coneCharacteristic_coordinates d hv
  have hnorm : ‖coneCharacteristicMap d n χ v‖ = (v 0 + 1) / 2 := by
    rw [coneCharacteristicMap, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1,
      show ‖(χ (Fin.tail v)).val‖ = 1 by simp, mul_one]
  refine ⟨by rw [hnorm]; exact hc.1, by rw [hnorm]; exact hc.2.1, ?_⟩
  change sphereDirection n θ (((v 0 + 1) / 2) • (χ (Fin.tail v)).val) ∈ χ.target
  rw [sphereDirection_smul n θ _ hc.1]
  exact χ.map_source (hs ▸ hc.2.2)

theorem coneCharacteristic_inverse_mapsTo (d n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    (hs : χ.source = Metric.ball 0 1) :
    MapsTo (coneCharacteristicInverse d n θ χ) (coneCharacteristicTarget d n θ χ)
      (Metric.ball 0 1) := by
  intro y hy
  have htail := χ.map_target hy.2.2
  rw [hs, Metric.mem_ball, dist_zero_right, pi_norm_lt_iff zero_lt_one] at htail
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff zero_lt_one]
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · change ‖2 * ‖y‖ - 1‖ < 1
    rw [Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2.1]⟩
  · exact htail k

theorem coneCharacteristic_right_inverse (d n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    {y : Fin n → ℝ} (hy : y ∈ coneCharacteristicTarget d n θ χ) :
    coneCharacteristicMap d n χ (coneCharacteristicInverse d n θ χ y) = y := by
  have hy0 : y ≠ 0 := norm_pos_iff.mp hy.1
  simp only [coneCharacteristicMap, coneCharacteristicInverse, Fin.cons_zero,
    Fin.tail_cons, χ.right_inv hy.2.2]
  rw [show (2 * ‖y‖ - 1 + 1) / 2 = ‖y‖ by ring]
  simp [sphereDirection, hy0, smul_smul, hy.1.ne']

def coneCharacteristicPartialEquiv (d n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    (hs : χ.source = Metric.ball 0 1) :
    PartialEquiv (Fin (d + 1) → ℝ) (Fin n → ℝ) where
  toFun := coneCharacteristicMap d n χ
  invFun := coneCharacteristicInverse d n θ χ
  source := Metric.ball 0 1
  target := coneCharacteristicTarget d n θ χ
  map_source' := fun _ hv ↦ coneCharacteristic_mapsTo d n θ χ hs hv
  map_target' := fun _ hv ↦ coneCharacteristic_inverse_mapsTo d n θ χ hs hv
  left_inv' := fun _ hv ↦ coneCharacteristic_left_inverse d n θ χ hs hv
  right_inv' := fun _ hv ↦ coneCharacteristic_right_inverse d n θ χ hv

theorem coneCharacteristicMap_continuous (d n : ℕ)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    (hχ : Continuous χ) : Continuous (coneCharacteristicMap d n χ) := by
  exact (((continuous_apply 0).add continuous_const).div_const 2).smul
    (continuous_subtype_val.comp (hχ.comp (continuous_pi (fun j ↦ continuous_apply j.succ))))

theorem sphereDirection_continuousOn (n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1) :
    ContinuousOn (sphereDirection n θ) {y : Fin n → ℝ | y ≠ 0} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply Continuous.subtype_mk
  have hc : Continuous (fun y : {y : Fin n → ℝ | y ≠ 0} ↦ ‖y.val‖⁻¹ • y.val) :=
    ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun y ↦ norm_ne_zero_iff.mpr y.property)).smul continuous_subtype_val
  apply hc.congr
  intro y
  change ‖y.val‖⁻¹ • y.val = (sphereDirection n θ y.val).val
  simp only [sphereDirection, dite_eq_right y.property]

theorem coneCharacteristicInverse_continuousOn (d n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    (hχ : ContinuousOn χ.symm χ.target) :
    ContinuousOn (coneCharacteristicInverse d n θ χ) (coneCharacteristicTarget d n θ χ) := by
  have hd : ContinuousOn (sphereDirection n θ) (coneCharacteristicTarget d n θ χ) :=
    (sphereDirection_continuousOn n θ).mono (fun _ hy ↦ norm_pos_iff.mp hy.1)
  have ht : ContinuousOn (fun y ↦ χ.symm (sphereDirection n θ y))
      (coneCharacteristicTarget d n θ χ) := hχ.comp hd (fun _ hy ↦ hy.2.2)
  apply continuousOn_pi.mpr
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · exact (continuousOn_const.mul continuous_norm.continuousOn).sub continuousOn_const
  · exact (continuous_apply k).continuousOn.comp ht (mapsTo_univ _ _)


theorem coneCharacteristicMap_closedBall (d n : ℕ)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1)) :
    MapsTo (coneCharacteristicMap d n χ) (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
  intro v hv
  have hcoord : |v 0| ≤ 1 := by
    have h := (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mp
      (show ‖v‖ ≤ 1 by simpa using hv)
    exact h 0
  have h0 := abs_le.mp hcoord
  have ht : 0 ≤ (v 0 + 1) / 2 := by linarith
  rw [Metric.mem_closedBall, dist_zero_right, coneCharacteristicMap, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht, show ‖(χ (Fin.tail v)).val‖ = 1 by simp, mul_one]
  linarith

theorem coneCharacteristicMap_boundary (d n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1)
    (χ : PartialEquiv (Fin d → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1))
    (hb : ∀ v ∈ Metric.sphere (0 : Fin d → ℝ) 1, χ v = θ)
    {v : Fin (d + 1) → ℝ} (hv : v ∈ Metric.sphere 0 1) :
    coneCharacteristicMap d n χ v = 0 ∨
      coneCharacteristicMap d n χ v ∈ Metric.sphere 0 1 ∨
      ∃ t ∈ Icc (0 : ℝ) 1, coneCharacteristicMap d n χ v = t • θ.val := by
  let w : CubicalCharacteristicParameterG8.ClosedDisk (d + 1) :=
    ⟨v, Metric.sphere_subset_closedBall hv⟩
  have hh := (CubicalCharacteristicParameterG8.diskPrismHomeomorph_boundary_iff d w).mp hv
  rcases hh with h | h | h
  · left
    change (v 0 + 1) / 2 = 0 at h
    simp [coneCharacteristicMap, h]
  · right; left
    change (v 0 + 1) / 2 = 1 at h
    simp [coneCharacteristicMap, h]
  · right; right
    change Fin.tail v ∈ Metric.sphere 0 1 at h
    refine ⟨(v 0 + 1) / 2,
      (CubicalCharacteristicParameterG8.diskPrismHomeomorph d w).2.property, ?_⟩
    simp [coneCharacteristicMap, hb _ h]

/-- The zero-dimensional sphere cell at a prescribed point. -/
def sphereVertexCharacteristic (n : ℕ) (θ : Metric.sphere (0 : Fin n → ℝ) 1) :
    PartialEquiv (Fin 0 → ℝ) (Metric.sphere (0 : Fin n → ℝ) 1) :=
  PartialEquiv.single 0 θ

theorem sphereVertexCharacteristic_source (n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1) :
    (sphereVertexCharacteristic n θ).source = Metric.ball 0 1 := by
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  simp [sphereVertexCharacteristic, hv]

theorem sphereVertexCharacteristic_continuous (n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1) :
    Continuous (sphereVertexCharacteristic n θ) := continuous_const

theorem sphereVertexCharacteristic_continuousOn_symm (n : ℕ)
    (θ : Metric.sphere (0 : Fin n → ℝ) 1) :
    ContinuousOn (sphereVertexCharacteristic n θ).symm
      (sphereVertexCharacteristic n θ).target := continuousOn_const



end
end HolomorphicAnosov

