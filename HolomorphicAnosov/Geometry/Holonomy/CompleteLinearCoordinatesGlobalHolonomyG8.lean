import HolomorphicAnosov.Geometry.FinitePlaqueHolonomy
import Mathlib.Topology.LocallyConstant.Basic
import HolomorphicAnosov.Geometry.TopologyGeneratedByOpenPlaqueCoverG10
import HolomorphicAnosov.Geometry.FinitePlaqueChainsOfLocalCoverG10
import HolomorphicAnosov.Topology.OpenCoverPathSubdivision
import HolomorphicAnosov.Analysis.DiffeomorphContinuousProjection
import HolomorphicAnosov.Analysis.FiniteLinearCoordinateGermComposition
import HolomorphicAnosov.Analysis.LocalLinearCoordinateParameterGerm
import HolomorphicAnosov.Geometry.Holonomy.LocalPlaqueLinearGermOfParameter
import HolomorphicAnosov.Topology.OpenCoverPathStripSubdivision
import HolomorphicAnosov.Geometry.Holonomy.GermTransportStrip
import HolomorphicAnosov.Geometry.Holonomy.SameBoxSquareGerm
import HolomorphicAnosov.Geometry.Holonomy.IntrinsicPlaqueSquareSubdivision
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Geometry.GlobalHolonomy
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Algebra.Module.Basic

import HolomorphicAnosov.Geometry.UnstablePlaqueOpenG10
import HolomorphicAnosov.Geometry.StablePlaqueOpenG10
import HolomorphicAnosov.Geometry.SameBoxPlaqueGermG10

/-! # Global holonomy from complete linearizing coordinates  Zhang Lemmas 2.7–2.10 and Nisoli §1.3 pp.21–25.    Complete coordinates extend each linear plaque germ to an entire biholomorphism. -/
noncomputable section
open scoped ContDiff Manifold _root_.Topology
open Set Filter _root_.Topology
universe u
namespace HolomorphicAnosov
local instance (k : ℕ) : Nonempty (FoliationCoordinateDisk k) := ⟨⟨0, by simp⟩⟩


section EntireLinearCoordinates

variable {E E' E'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E'']

/-- The coefficient of a linear germ at zero is unique. (Zhang, Lemma 2.8) -/
private theorem linear_germ_coefficient_unique (D D' : E ≃L[ℂ] E')
    (h : (fun v : E ↦ D v) =ᶠ[𝓝 (0 : E)] (fun v ↦ D' v)) : D = D' := by
  have hd := h.fderiv_eq (𝕜 := ℂ)
  change fderiv ℂ D.toContinuousLinearMap 0 =
    fderiv ℂ D'.toContinuousLinearMap 0 at hd
  have he : D.toContinuousLinearMap = D'.toContinuousLinearMap := by
    simpa only [ContinuousLinearMap.fderiv] using hd
  ext v
  exact congrArg (fun L : E →L[ℂ] E' ↦ L v) he


/-- Complete intrinsic coordinates and an invertible linear coefficient construct an actual entire-leaf biholomorphism. (Zhang, Lemma 2.10) -/
private theorem entire_map_of_complete_coordinates
    {k l : ℕ} {L L' : Type*} [TopologicalSpace L] [TopologicalSpace L']
    [ChartedSpace (ComplexModel k) L] [ChartedSpace (ComplexModel l) L']
    (φ : Diffeomorph (complexModel k) 𝓘(ℂ, E) L E ∞)
    (ψ : Diffeomorph (complexModel l) 𝓘(ℂ, E') L' E' ∞)
    (D : E ≃L[ℂ] E') :
    ∃ H : Biholomorph k l L L',
      (∀ z, H z = ψ.symm (D (φ z))) ∧
      (∀ w, H.symm w = φ.symm (D.symm (ψ w))) ∧
      (∀ z, ψ (H z) = D (φ z)) := by
  let H := (φ.trans D.toDiffeomorph).trans ψ.symm
  refine ⟨H, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  intro z
  exact ψ.apply_symm_apply _


/-- A linearized local representative has exactly the germ of the entire coordinate map at the ORIGINAL base point. (Zhang) -/
private theorem entire_coordinate_map_extends_linear_germ
    {k l : ℕ} {L L' : Type*} [TopologicalSpace L] [TopologicalSpace L']
    [ChartedSpace (ComplexModel k) L] [ChartedSpace (ComplexModel l) L']
    (φ : Diffeomorph (complexModel k) 𝓘(ℂ, E) L E ∞)
    (ψ : Diffeomorph (complexModel l) 𝓘(ℂ, E') L' E' ∞)
    (D : E ≃L[ℂ] E') (x : L) (hφ : φ x = 0) (h : L → L')
    (hh : ∀ᶠ v in 𝓝 (0 : E), ψ (h (φ.symm v)) = D v) :
    (fun z ↦ ψ.symm (D (φ z))) =ᶠ[𝓝 x] h := by
  have ht : Tendsto φ (𝓝 x) (𝓝 (0 : E)) := by
    simpa only [hφ] using φ.continuous.tendsto x
  filter_upwards [ht.eventually hh] with z hz
  apply ψ.injective
  change ψ (ψ.symm (D (φ z))) = ψ (h z)
  simpa only [ψ.apply_symm_apply, φ.symm_apply_apply] using hz.symm


/-- For fixed complete coordinates, agreement of two entire linear-coordinate maps on the base germ forces equality on EVERY point of the whole leaf. (Zhang, Lemma 2.8) -/
private theorem entire_linear_maps_unique_of_germ
    {k l : ℕ} {L L' : Type*} [TopologicalSpace L] [TopologicalSpace L']
    [ChartedSpace (ComplexModel k) L] [ChartedSpace (ComplexModel l) L']
    (φ : Diffeomorph (complexModel k) 𝓘(ℂ, E) L E ∞)
    (ψ : Diffeomorph (complexModel l) 𝓘(ℂ, E') L' E' ∞)
    (D D' : E ≃L[ℂ] E') (x : L) (hφ : φ x = 0)
    (H H' : L → L')
    (hH : ∀ z, ψ (H z) = D (φ z))
    (hH' : ∀ z, ψ (H' z) = D' (φ z))
    (hg : H =ᶠ[𝓝 x] H') : H = H' := by
  have hzero : φ.symm (0 : E) = x := by
    rw [← hφ, φ.symm_apply_apply]
  have ht : Tendsto φ.symm (𝓝 (0 : E)) (𝓝 x) := by
    simpa only [hzero] using φ.symm.continuous.tendsto (0 : E)
  have he : (fun v : E ↦ D v) =ᶠ[𝓝 (0 : E)] (fun v ↦ D' v) := by
    filter_upwards [ht.eventually hg] with v hv
    calc
      D v = ψ (H (φ.symm v)) := by simp only [hH, φ.apply_symm_apply]
      _ = ψ (H' (φ.symm v)) := congrArg ψ hv
      _ = D' v := by simp only [hH', φ.apply_symm_apply]
  have hD := linear_germ_coefficient_unique D D' he
  funext z
  apply ψ.injective
  change ψ (H z) = ψ (H' z)
  rw [hH, hH', hD]


/-- Coordinate composition is literal composition of the coefficient maps. (Zhang, Lemma 2.10) -/
private theorem entire_maps_compose
    {k l m : ℕ} {L L' L'' : Type*}
    [TopologicalSpace L] [TopologicalSpace L'] [TopologicalSpace L'']
    [ChartedSpace (ComplexModel k) L] [ChartedSpace (ComplexModel l) L']
    [ChartedSpace (ComplexModel m) L'']
    (φ : Diffeomorph (complexModel k) 𝓘(ℂ, E) L E ∞)
    (ψ : Diffeomorph (complexModel l) 𝓘(ℂ, E') L' E' ∞)
    (χ : Diffeomorph (complexModel m) 𝓘(ℂ, E'') L'' E'' ∞)
    (D : E ≃L[ℂ] E') (K : E' ≃L[ℂ] E'')
    (H : L → L') (J : L' → L'')
    (hH : ∀ z, ψ (H z) = D (φ z))
    (hJ : ∀ z, χ (J z) = K (ψ z)) :
    ∀ z, χ (J (H z)) = (D.trans K) (φ z) := by
  intro z
  rw [hJ, hH]
  rfl


end EntireLinearCoordinates

/-- Finite continuation of linearized local germs uses the SAME complete coordinate at each switch. (Zhang, Lemma 2.8) -/
private theorem plaque_chain_linear_coefficient {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (φ : ∀ x : M, F.ULeaf x ≃ₜ ℂ)
    (hloc : ∀ (x y : M) (e : LocalPlaqueTransport F x y),
      ∃ D : ℂ ≃L[ℂ] ℂ,
        ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e.map z) = D (φ x z))
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {a b : unitInterval}
    {e : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)}
    (h : PlaqueChainAlong F γ a b e) :
    ∃ D : ℂ ≃L[ℂ] ℂ,
      ∀ᶠ z in 𝓝 (F.uPoint (γ a).val),
        φ (γ b).val (e z) = D (φ (γ a).val z) := by
  induction h with
  | single a b hab e hs => exact hloc _ _ e
  | @compose a b c el er hab hbc left right ihl ihr =>
    obtain ⟨D, hD⟩ := ihl
    obtain ⟨K, hK⟩ := ihr
    have hp := plaque_chain_pointed F γ left
    have ht : Tendsto el (𝓝 (F.uPoint (γ a).val)) (𝓝 (F.uPoint (γ b).val)) := by
      simpa only [hp.2] using (el.continuousAt hp.1).tendsto
    refine ⟨D.trans K, ?_⟩
    filter_upwards [hD, ht.eventually hK] with z hz hzz
    change φ (γ c).val (er (el z)) = K (D (φ (γ a).val z))
    rw [hzz, hz]


/-- The entire candidate for an ordered subpath extends EVERY actual representative. (Zhang) -/
private theorem entire_subpath_extension {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (C : IntrinsicComplexUnstableLeaves F)
    (φ : ∀ x : M, letI := C.charts (Quotient.mk F.unstablePartition x)
      Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ) (F.ULeaf x) ℂ ∞)
    (hloc : ∀ (x y : M) (e : LocalPlaqueTransport F x y),
      ∃ D : ℂ ≃L[ℂ] ℂ,
        ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e.map z) = D (φ x z))
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (hab : a ≤ b) :
    ∃ D : ℂ ≃L[ℂ] ℂ,
      ∃ H : IntrinsicLeafBiholomorph F C (γ a).val (γ b).val,
        (∀ z, φ (γ b).val (H z) = D (φ (γ a).val z)) ∧
        (∀ e : PathHolonomyRepresentative F γ a b,
          (fun z ↦ H z) =ᶠ[𝓝 (F.uPoint (γ a).val)] (fun z ↦ e.map z)) := by
  let := C.charts (Quotient.mk F.unstablePartition (γ a).val)
  let := C.charts (Quotient.mk F.unstablePartition (γ b).val)
  obtain ⟨e⟩ := path_holonomy_subinterval_representative_exists F γ a b hab
  obtain ⟨D, hD⟩ := plaque_chain_linear_coefficient F
    (fun x ↦ letI := C.charts (Quotient.mk F.unstablePartition x)
      (φ x).toHomeomorph) hloc γ e.chain
  obtain ⟨H, hH, _, hcoord⟩ :=
    entire_map_of_complete_coordinates (φ (γ a).val) (φ (γ b).val) D
  refine ⟨D, H, hcoord, ?_⟩
  intro e'
  have hsame := Filter.Germ.coe_eq.mp
    (same_subpath_plaque_chain_germ F γ e.chain e'.map e'.chain)
  filter_upwards [hD, hsame] with z hz hzz
  apply (φ (γ b).val).injective
  change φ (γ b).val (H z) = φ (γ b).val (e'.map z)
  rw [hcoord, ← hzz]
  exact hz.symm


/-- Two entire linear-coordinate extensions of the same subpath are equal everywhere. (Zhang, Lemma 2.10) -/
private theorem entire_subpath_extension_unique {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (C : IntrinsicComplexUnstableLeaves F)
    (φ : ∀ x : M, letI := C.charts (Quotient.mk F.unstablePartition x)
      Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ) (F.ULeaf x) ℂ ∞)
    (hzero : ∀ x, φ x (F.uPoint x) = 0)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (e : PathHolonomyRepresentative F γ a b)
    (D D' : ℂ ≃L[ℂ] ℂ)
    (H H' : F.ULeaf (γ a).val → F.ULeaf (γ b).val)
    (hH : ∀ z, φ (γ b).val (H z) = D (φ (γ a).val z))
    (hH' : ∀ z, φ (γ b).val (H' z) = D' (φ (γ a).val z))
    (he : H =ᶠ[𝓝 (F.uPoint (γ a).val)] (fun z ↦ e.map z))
    (he' : H' =ᶠ[𝓝 (F.uPoint (γ a).val)] (fun z ↦ e.map z)) : H = H' := by
  let := C.charts (Quotient.mk F.unstablePartition (γ a).val)
  let := C.charts (Quotient.mk F.unstablePartition (γ b).val)
  exact entire_linear_maps_unique_of_germ (φ (γ a).val) (φ (γ b).val)
    D D' (F.uPoint (γ a).val) (hzero _) H H' hH hH' (he.trans he'.symm)


/-- The entire extensions satisfy chronological restriction on the WHOLE source leaf. (Zhang, Lemma 2.10) -/
private theorem entire_subpath_extensions_compose {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (C : IntrinsicComplexUnstableLeaves F)
    (φ : ∀ x : M, letI := C.charts (Quotient.mk F.unstablePartition x)
      Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ) (F.ULeaf x) ℂ ∞)
    (hzero : ∀ x, φ x (F.uPoint x) = 0)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c)
    (l : PathHolonomyRepresentative F γ a b) (r : PathHolonomyRepresentative F γ b c)
    (e : PathHolonomyRepresentative F γ a c)
    (D K J : ℂ ≃L[ℂ] ℂ)
    (H : IntrinsicLeafBiholomorph F C (γ a).val (γ b).val)
    (H' : IntrinsicLeafBiholomorph F C (γ b).val (γ c).val)
    (H'' : IntrinsicLeafBiholomorph F C (γ a).val (γ c).val)
    (hH : ∀ z, φ (γ b).val (H z) = D (φ (γ a).val z))
    (hH' : ∀ z, φ (γ c).val (H' z) = K (φ (γ b).val z))
    (hH'' : ∀ z, φ (γ c).val (H'' z) = J (φ (γ a).val z))
    (hl : (fun z ↦ H z) =ᶠ[𝓝 (F.uPoint (γ a).val)] (fun z ↦ l.map z))
    (hr : (fun z ↦ H' z) =ᶠ[𝓝 (F.uPoint (γ b).val)] (fun z ↦ r.map z))
    (he : (fun z ↦ H'' z) =ᶠ[𝓝 (F.uPoint (γ a).val)] (fun z ↦ e.map z)) :
    ∀ z, H'' z = H' (H z) := by
  let := C.charts (Quotient.mk F.unstablePartition (γ a).val)
  let := C.charts (Quotient.mk F.unstablePartition (γ b).val)
  let := C.charts (Quotient.mk F.unstablePartition (γ c).val)
  have hp : H (F.uPoint (γ a).val) = F.uPoint (γ b).val := by
    apply (φ (γ b).val).injective
    change φ (γ b).val (H (F.uPoint (γ a).val)) = φ (γ b).val (F.uPoint (γ b).val)
    rw [hH, hzero, map_zero, hzero]
  have ht : Tendsto H (𝓝 (F.uPoint (γ a).val)) (𝓝 (F.uPoint (γ b).val)) := by
    simpa only [hp] using H.continuous.tendsto (F.uPoint (γ a).val)
  have hcomp : (fun z ↦ H' (H z)) =ᶠ[𝓝 (F.uPoint (γ a).val)]
      (fun z ↦ r.map (l.map z)) := by
    filter_upwards [hl, ht.eventually hr] with z hz hzz
    rw [hzz, hz]
  have hrep := Filter.Germ.coe_eq.mp
    (local_representative_concatenation_germ F γ a b c hab hbc l r e)
  have huniq := entire_subpath_extension_unique F C φ hzero γ a c e J (D.trans K)
    (fun z ↦ H'' z) (fun z ↦ H' (H z)) hH''
    (entire_maps_compose (φ (γ a).val) (φ (γ b).val) (φ (γ c).val)
      D K H H' hH hH') he (hcomp.trans hrep)
  exact fun z ↦ congrFun huniq z


/-- The subpath candidate has the exact endpoint carriers and cast convention of `GlobalSHolonomyData.extends_local`, and extends every representative of the path. (Zhang, Lemma 2.10) -/
theorem entire_path_extension {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (C : IntrinsicComplexUnstableLeaves F)
    (φ : ∀ x : M, letI := C.charts (Quotient.mk F.unstablePartition x)
      Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ) (F.ULeaf x) ℂ ∞)
    (hloc : ∀ (x y : M) (e : LocalPlaqueTransport F x y),
      ∃ D : ℂ ≃L[ℂ] ℂ,
        ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e.map z) = D (φ x z))
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) :
    ∃ D : ℂ ≃L[ℂ] ℂ, ∃ H : IntrinsicLeafBiholomorph F C x.val y.val,
      (∀ z, φ y.val (H z) = D (φ x.val z)) ∧
      (∀ e : PathHolonomyRepresentative F γ 0 1,
        (Filter.Germ.ofFun (fun z : F.ULeaf x.val ↦ H z) :
          Filter.Germ (𝓝 (F.uPoint x.val)) (F.ULeaf y.val)) =
          Filter.Germ.ofFun (fun z : F.ULeaf x.val ↦
            castIntrinsicULeaf F (congrArg Subtype.val γ.target)
              (e.map (castIntrinsicULeaf F
                (congrArg Subtype.val γ.source).symm z)))) := by
  let := C.charts (Quotient.mk F.unstablePartition x.val)
  let := C.charts (Quotient.mk F.unstablePartition y.val)
  obtain ⟨D, H, hH, he⟩ := entire_subpath_extension F C φ hloc γ 0 1 (by simp)
  obtain ⟨J, _, _, hJ⟩ := entire_map_of_complete_coordinates (φ x.val) (φ y.val) D
  refine ⟨D, J, hJ, ?_⟩
  intro e
  have hcast : ∀ {p r : M} (h : p = r) (z : F.ULeaf p),
      φ r (castIntrinsicULeaf F h z) = φ p z := by
    intro p r h z
    subst r
    rfl
  have hct : ∀ {p r : M} (h : p = r),
      Tendsto (castIntrinsicULeaf F h) (𝓝 (F.uPoint p)) (𝓝 (F.uPoint r)) := by
    intro p r h
    subst r
    exact tendsto_id
  have hmap : ∀ᶠ z in 𝓝 (F.uPoint (γ 0).val),
      φ (γ 1).val (e.map z) = D (φ (γ 0).val z) := by
    filter_upwards [he e] with z hz
    rw [← hz]
    exact hH z
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [(hct (congrArg Subtype.val γ.source).symm).eventually hmap] with z hz
  apply (φ y.val).injective
  change φ y.val (J z) = φ y.val (castIntrinsicULeaf F (congrArg Subtype.val γ.target)
    (e.map (castIntrinsicULeaf F (congrArg Subtype.val γ.source).symm z)))
  rw [hJ, hcast, hz, hcast]


/-- The entire linear extension of a constant path is the identity on every leaf point. (Zhang, Remark 1.3.2) -/
theorem entire_constant_path_identity {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (C : IntrinsicComplexUnstableLeaves F)
    (φ : ∀ x : M, letI := C.charts (Quotient.mk F.unstablePartition x)
      Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ) (F.ULeaf x) ℂ ∞)
    (hzero : ∀ x, φ x (F.uPoint x) = 0)
    {q : Quotient F.stablePartition} (x : IntrinsicFoliationLeaf F.stablePartition q)
    (a b : unitInterval) (e : PathHolonomyRepresentative F (Path.refl x) a b)
    (D : ℂ ≃L[ℂ] ℂ) (H : F.ULeaf x.val → F.ULeaf x.val)
    (hH : ∀ z, φ x.val (H z) = D (φ x.val z))
    (he : H =ᶠ[𝓝 (F.uPoint x.val)] (fun z ↦ e.map z)) : ∀ z, H z = z := by
  have hid := Filter.Germ.coe_eq.mp (constant_path_representative_identity_germ F x a b e)
  have hh := entire_subpath_extension_unique F C φ hzero (Path.refl x) a b e
    D (ContinuousLinearEquiv.refl ℂ ℂ) H id hH (fun _ ↦ rfl) he hid.symm
  exact fun z ↦ congrFun hh z


/-- Reverse a one-box transport on its actual open target. (Zhang, Remark 1.3.2) -/
private theorem inverse_local_plaque_transport {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M) {x y : M}
    (e : LocalPlaqueTransport F x y) :
    ∃ r : LocalPlaqueTransport F y x,
      r.map = e.map.symm ∧ r.box = e.box ∧ r.transverse = e.transverse := by
  refine ⟨{ map := e.map.symm
            source_point := ?_
            map_point := ?_
            box := e.box
            first := e.second
            second := e.first
            transverse := e.transverse
            first_point := e.second_point
            second_point := e.first_point
            source_in_plaque := ?_
            coordinate_map := ?_ }, rfl, rfl, rfl⟩
  · rw [← e.map_point]
    exact e.map.map_source e.source_point
  · rw [← e.map_point]
    exact e.map.left_inv e.source_point
  · intro z hz
    obtain ⟨w, hw⟩ := e.source_in_plaque (e.map.symm z) (e.map.map_target hz)
    refine ⟨w, ?_⟩
    have h := e.coordinate_map (e.map.symm z) w (e.map.map_target hz) hw
    simpa only [e.map.right_inv hz] using h.symm
  · intro z w hz hw
    obtain ⟨v, hv⟩ := e.source_in_plaque (e.map.symm z) (e.map.map_target hz)
    have h := e.coordinate_map (e.map.symm z) v (e.map.map_target hz) hv
    have he : (F.box e.box).chart (e.second, v) =
        (F.box e.box).chart (e.second, w) := by
      apply Subtype.ext
      exact h.symm.trans ((congrArg Subtype.val (e.map.right_inv hz)).trans hw.symm)
    have hvw : v = w := congrArg Prod.snd ((F.box e.box).chart.injective he)
    exact hv.symm.trans (congrArg (fun v ↦ ((F.box e.box).chart (e.first, v)).val) hvw)


/-- Reverse an actual finite plaque chain, including its chronological order and open partial map. (Nisoli, Remark 1.3.2) -/
private theorem reverse_plaque_chain {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {a b : unitInterval}
    {e : OpenPartialHomeomorph (F.ULeaf (γ.symm a).val) (F.ULeaf (γ.symm b).val)}
    (h : PlaqueChainAlong F γ.symm a b e) :
    PlaqueChainAlong F γ (unitInterval.symm b) (unitInterval.symm a) e.symm := by
  induction h with
  | single a b hab e hseg =>
      obtain ⟨r, hr, hbox, htrans⟩ := inverse_local_plaque_transport F e
      rw [← hr]
      refine PlaqueChainAlong.single _ _ (unitInterval.symm_le_symm.mpr hab) r ?_
      intro v hbv hva
      obtain ⟨z, hz⟩ := hseg (unitInterval.symm v)
        (unitInterval.le_symm_comm.mpr hva) (unitInterval.symm_le_comm.mp hbv)
      refine ⟨z, ?_⟩
      have hh := congrArg (fun j ↦ ((F.box j).chart (z, e.transverse)).val) hbox
      apply (show ((F.box r.box).chart (z, r.transverse)).val =
          ((F.box e.box).chart (z, e.transverse)).val by simpa only [htrans] using hh).trans
      simpa only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm] using hz
  | compose hab hbc left right ihleft ihright =>
      exact PlaqueChainAlong.compose (unitInterval.symm_le_symm.mpr hbc)
        (unitInterval.symm_le_symm.mpr hab) ihright ihleft


/-- Reversing a finite path representative uses precisely the inverse open partial map. (Nisoli) -/
private theorem reverse_path_representative {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (e : PathHolonomyRepresentative F γ.symm a b) :
    ∃ r : PathHolonomyRepresentative F γ (unitInterval.symm b) (unitInterval.symm a),
      r.map = e.map.symm := by
  have h := reverse_plaque_chain F γ e.chain
  have hp := plaque_chain_pointed F γ h
  exact ⟨{ map := e.map.symm, source_point := hp.1, map_point := hp.2, chain := h }, rfl⟩


/-- Every representative of a reversed interval has the inverse germ of every forward representative. (Nisoli) -/
private theorem reverse_path_representative_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (e : PathHolonomyRepresentative F γ.symm a b)
    (r : PathHolonomyRepresentative F γ (unitInterval.symm b) (unitInterval.symm a)) :
    (Filter.Germ.ofFun r.map : Filter.Germ (𝓝 (F.uPoint (γ (unitInterval.symm b)).val))
      (F.ULeaf (γ (unitInterval.symm a)).val)) = Filter.Germ.ofFun e.map.symm := by
  exact (same_subpath_plaque_chain_germ F γ
    (reverse_plaque_chain F γ e.chain) r.map r.chain).symm


/-- Inverting an entire extension preserves the inverse local germ at its actual receiving point. (Zhang, Lemma 2.10) -/
private theorem entire_inverse_extends_local
    {L L' : Type*} [TopologicalSpace L] [TopologicalSpace L']
    (H : L ≃ₜ L') (e : OpenPartialHomeomorph L L') (x : L) (y : L')
    (hsource : x ∈ e.source) (hpoint : H x = y)
    (he : (fun z ↦ H z) =ᶠ[𝓝 x] (fun z ↦ e z)) :
    (fun z ↦ H.symm z) =ᶠ[𝓝 y] (fun z ↦ e.symm z) := by
  have hinv : H.symm y = x := by rw [← hpoint, H.symm_apply_apply]
  have ht : Tendsto H.symm (𝓝 y) (𝓝 x) := by
    simpa only [hinv] using H.symm.continuous.tendsto y
  filter_upwards [ht.eventually he,
    ht.eventually (e.open_source.mem_nhds hsource)] with z hz hs
  have hh := e.left_inv hs
  rw [← hz, H.apply_symm_apply] at hh
  exact hh.symm


/-- The inverse of a whole linear-coordinate extension has the inverse coefficient, and extends the inverse of every local representative that the forward map extends. (Zhang, Lemma 2.10) -/
theorem entire_linear_inverse {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (C : IntrinsicComplexUnstableLeaves F)
    (φ : ∀ x : M, letI := C.charts (Quotient.mk F.unstablePartition x)
      Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ) (F.ULeaf x) ℂ ∞)
    (hzero : ∀ x, φ x (F.uPoint x) = 0)
    {x y : M} (D : ℂ ≃L[ℂ] ℂ)
    (H : IntrinsicLeafBiholomorph F C x y)
    (e : PointedLeafHomeomorph F x y)
    (hH : ∀ z, φ y (H z) = D (φ x z))
    (he : (fun z ↦ H z) =ᶠ[𝓝 (F.uPoint x)] (fun z ↦ e.map z)) :
    (∀ z, φ x (inverseIntrinsicLeafBiholomorph F C H z) = D.symm (φ y z)) ∧
    (fun z ↦ inverseIntrinsicLeafBiholomorph F C H z) =ᶠ[𝓝 (F.uPoint y)]
      (fun z ↦ e.map.symm z) := by
  let := C.charts (Quotient.mk F.unstablePartition x)
  let := C.charts (Quotient.mk F.unstablePartition y)
  have hp : H (F.uPoint x) = F.uPoint y := by
    apply (φ y).injective
    change φ y (H (F.uPoint x)) = φ y (F.uPoint y)
    rw [hH, hzero, map_zero, hzero]
  constructor
  · intro z
    have hz := hH (H.symm z)
    rw [H.apply_symm_apply] at hz
    change φ x (H.symm z) = D.symm (φ y z)
    rw [hz, D.symm_apply_apply]
  · exact entire_inverse_extends_local H.toHomeomorph e.map
      (F.uPoint x) (F.uPoint y) e.source_point hp he


/-- Entire linear-coordinate extensions of opposite subpaths are inverse on the whole intrinsic leaf. (Zhang, Lemma 2.10) -/
theorem entire_reversed_subpath_inverse {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (C : IntrinsicComplexUnstableLeaves F)
    (φ : ∀ x : M, letI := C.charts (Quotient.mk F.unstablePartition x)
      Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ) (F.ULeaf x) ℂ ∞)
    (hzero : ∀ x, φ x (F.uPoint x) = 0)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (e : PathHolonomyRepresentative F γ.symm a b)
    (r : PathHolonomyRepresentative F γ (unitInterval.symm b) (unitInterval.symm a))
    (D K : ℂ ≃L[ℂ] ℂ)
    (H : IntrinsicLeafBiholomorph F C (γ.symm a).val (γ.symm b).val)
    (H' : IntrinsicLeafBiholomorph F C (γ (unitInterval.symm b)).val
      (γ (unitInterval.symm a)).val)
    (hH : ∀ z, φ (γ.symm b).val (H z) = D (φ (γ.symm a).val z))
    (hH' : ∀ z, φ (γ (unitInterval.symm a)).val (H' z) =
      K (φ (γ (unitInterval.symm b)).val z))
    (he : (fun z ↦ H z) =ᶠ[𝓝 (F.uPoint (γ.symm a).val)] (fun z ↦ e.map z))
    (hr : (fun z ↦ H' z) =ᶠ[𝓝 (F.uPoint (γ (unitInterval.symm b)).val)]
      (fun z ↦ r.map z)) :
    ∀ z, H' z = inverseIntrinsicLeafBiholomorph F C H z := by
  obtain ⟨hcoord, hinv⟩ := entire_linear_inverse F C φ hzero D H
    e.toPointedLeafHomeomorph hH he
  have hg := Filter.Germ.coe_eq.mp (reverse_path_representative_germ F γ a b e r)
  have hh := entire_subpath_extension_unique F C φ hzero γ
    (unitInterval.symm b) (unitInterval.symm a) r K D.symm
    (fun z ↦ H' z) (fun z ↦ inverseIntrinsicLeafBiholomorph F C H z)
    hH' hcoord hr (hinv.trans hg.symm)
  exact fun z ↦ congrFun hh z


/-- Uniqueness of a linear holonomy coefficient in fixed centered coordinates. (Zhang, Lemma 2.8) -/
theorem holonomy_linear_coefficient_unique {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (φ : ∀ x : M, F.ULeaf x ≃ₜ ℂ) (hzero : ∀ x, φ x (F.uPoint x) = 0)
    {x y : M} (e : F.ULeaf x → F.ULeaf y) (D K : ℂ ≃L[ℂ] ℂ)
    (hD : ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e z) = D (φ x z))
    (hK : ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e z) = K (φ x z)) : D = K := by
  have he : (φ x).symm 0 = F.uPoint x := by rw [← hzero x, (φ x).symm_apply_apply]
  have ht : Tendsto (φ x).symm (𝓝 0) (𝓝 (F.uPoint x)) := by
    simpa only [he] using (φ x).symm.continuous.tendsto 0
  apply linear_germ_coefficient_unique
  filter_upwards [ht.eventually hD, ht.eventually hK] with z hz hk
  simpa only [(φ x).apply_symm_apply] using hz.symm.trans hk

/-- The linear coefficient of a two-map germ is the chronological product. (Zhang, Lemma 2.8) -/
theorem holonomy_linear_coefficient_comp {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (φ : ∀ x : M, F.ULeaf x ≃ₜ ℂ)
    {x y z : M} (e : PointedLeafHomeomorph F x y) (f : PointedLeafHomeomorph F y z)
    (D K : ℂ ≃L[ℂ] ℂ)
    (hD : ∀ᶠ w in 𝓝 (F.uPoint x), φ y (e.map w) = D (φ x w))
    (hK : ∀ᶠ w in 𝓝 (F.uPoint y), φ z (f.map w) = K (φ y w)) :
    ∀ᶠ w in 𝓝 (F.uPoint x), φ z (f.map (e.map w)) = (D.trans K) (φ x w) := by
  have ht : Tendsto e.map (𝓝 (F.uPoint x)) (𝓝 (F.uPoint y)) := by
    simpa only [e.map_point] using (e.map.continuousAt e.source_point).tendsto
  filter_upwards [hD, ht.eventually hK] with w hw hw'
  rw [hw', hw]
  rfl

/-- Coefficients of whole subinterval representatives multiply under subdivision. (Nisoli) -/
theorem holonomy_linear_coefficient_subdivide {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (φ : ∀ x : M, F.ULeaf x ≃ₜ ℂ) (hzero : ∀ x, φ x (F.uPoint x) = 0)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c)
    (l : PathHolonomyRepresentative F γ a b) (r : PathHolonomyRepresentative F γ b c)
    (e : PathHolonomyRepresentative F γ a c) (D K J : ℂ ≃L[ℂ] ℂ)
    (hl : ∀ᶠ z in 𝓝 (F.uPoint (γ a).val), φ (γ b).val (l.map z) = D (φ (γ a).val z))
    (hr : ∀ᶠ z in 𝓝 (F.uPoint (γ b).val), φ (γ c).val (r.map z) = K (φ (γ b).val z))
    (he : ∀ᶠ z in 𝓝 (F.uPoint (γ a).val), φ (γ c).val (e.map z) = J (φ (γ a).val z)) :
    J = D.trans K := by
  have hcomp := holonomy_linear_coefficient_comp F φ l.toPointedLeafHomeomorph
    r.toPointedLeafHomeomorph D K hl hr
  have hg := Filter.Germ.coe_eq.mp
    (local_representative_concatenation_germ F γ a b c hab hbc l r e)
  apply holonomy_linear_coefficient_unique F φ hzero e.map J (D.trans K) he
  filter_upwards [hcomp, hg] with z hz hgz
  rw [← hgz]
  exact hz


set_option backward.isDefEq.respectTransparency false in
/-- The actual holonomy representatives along the four edges of one intrinsic plaque rectangle satisfy the commuting-square germ identity. (Nisoli, Theorem 1.3.8) -/
theorem plaque_rectangle_representatives_commute {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    {q : Quotient F.stablePartition}
    (H : unitInterval × unitInterval → IntrinsicFoliationLeaf F.stablePartition q)
    (hH : Continuous H) (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (box : F.boxIndex) (w : FoliationCoordinateDisk t)
    (hcell : ∀ z ∈ Icc a b ×ˢ Icc c d, ∃ r : FoliationCoordinateDisk s,
      ((F.box box).chart (r,w)).val = (H z).val)
    (bottom : PathHolonomyRepresentative F
      ⟨⟨fun v ↦ H (a,v), hH.comp (continuous_const.prodMk continuous_id)⟩, rfl, rfl⟩ c d)
    (top : PathHolonomyRepresentative F
      ⟨⟨fun v ↦ H (b,v), hH.comp (continuous_const.prodMk continuous_id)⟩, rfl, rfl⟩ c d)
    (left : PathHolonomyRepresentative F
      ⟨⟨fun v ↦ H (v,c), hH.comp (continuous_id.prodMk continuous_const)⟩, rfl, rfl⟩ a b)
    (right : PathHolonomyRepresentative F
      ⟨⟨fun v ↦ H (v,d), hH.comp (continuous_id.prodMk continuous_const)⟩, rfl, rfl⟩ a b) :
    (fun z ↦ right.map (bottom.map z)) =ᶠ[𝓝 (F.uPoint (H (a,c)).val)]
      (fun z ↦ top.map (left.map z)) := by
  obtain ⟨ac, hac⟩ := hcell (a,c) ⟨⟨le_rfl,hab⟩,⟨le_rfl,hcd⟩⟩
  obtain ⟨ad, had⟩ := hcell (a,d) ⟨⟨le_rfl,hab⟩,⟨hcd,le_rfl⟩⟩
  obtain ⟨bc, hbc⟩ := hcell (b,c) ⟨⟨hab,le_rfl⟩,⟨le_rfl,hcd⟩⟩
  obtain ⟨bd, hbd⟩ := hcell (b,d) ⟨⟨hab,le_rfl⟩,⟨hcd,le_rfl⟩⟩
  obtain ⟨B,hBb,_,_,hBw,_⟩ := local_plaque_transport_of_box F box ac ad w _ _ hac had
  obtain ⟨T,hTb,_,_,hTw,_⟩ := local_plaque_transport_of_box F box bc bd w _ _ hbc hbd
  obtain ⟨L,hLb,_,_,hLw,_⟩ := local_plaque_transport_of_box F box ac bc w _ _ hac hbc
  obtain ⟨R,hRb,_,_,hRw,_⟩ := local_plaque_transport_of_box F box ad bd w _ _ had hbd
  obtain ⟨D,hDb,_,_,_,_⟩ := local_plaque_transport_of_box F box ac bd w _ _ hac hbd
  have hB := plaque_chain_germ_in_one_plaque F _ bottom.chain B (by
    intro v hv hv'
    obtain ⟨z,hz⟩ := hcell (a,v) ⟨⟨le_rfl,hab⟩,⟨hv,hv'⟩⟩
    refine ⟨z, ?_⟩
    rw [hBw]
    exact (congrArg (fun j ↦ ((F.box j).chart (z,w)).val) hBb).trans hz)
  have hT := plaque_chain_germ_in_one_plaque F _ top.chain T (by
    intro v hv hv'
    obtain ⟨z,hz⟩ := hcell (b,v) ⟨⟨hab,le_rfl⟩,⟨hv,hv'⟩⟩
    refine ⟨z, ?_⟩
    rw [hTw]
    exact (congrArg (fun j ↦ ((F.box j).chart (z,w)).val) hTb).trans hz)
  have hL := plaque_chain_germ_in_one_plaque F _ left.chain L (by
    intro v hv hv'
    obtain ⟨z,hz⟩ := hcell (v,c) ⟨⟨hv,hv'⟩,⟨le_rfl,hcd⟩⟩
    refine ⟨z, ?_⟩
    rw [hLw]
    exact (congrArg (fun j ↦ ((F.box j).chart (z,w)).val) hLb).trans hz)
  have hR := plaque_chain_germ_in_one_plaque F _ right.chain R (by
    intro v hv hv'
    obtain ⟨z,hz⟩ := hcell (v,d) ⟨⟨hv,hv'⟩,⟨hcd,le_rfl⟩⟩
    refine ⟨z, ?_⟩
    rw [hRw]
    exact (congrArg (fun j ↦ ((F.box j).chart (z,w)).val) hRb).trans hz)
  have hbottom : Tendsto bottom.map (𝓝 (F.uPoint (H (a,c)).val))
      (𝓝 (F.uPoint (H (a,d)).val)) := by
    have ht := (bottom.map.continuousAt bottom.source_point).tendsto
    have hp := bottom.map_point
    simp only [Path.coe_mk_mk] at ht hp
    rw [hp] at ht
    exact ht
  have hleft : Tendsto left.map (𝓝 (F.uPoint (H (a,c)).val))
      (𝓝 (F.uPoint (H (b,c)).val)) := by
    have ht := (left.map.continuousAt left.source_point).tendsto
    have hp := left.map_point
    simp only [Path.coe_mk_mk] at ht hp
    rw [hp] at ht
    exact ht
  exact Germ.coe_eq.mp ((pointed_composition_germ_congr bottom.map B.map right.map R.map
    hbottom hB hR).trans ((same_box_square_germ F D B R L T
      (hBb.trans hDb.symm) (hRb.trans hDb.symm) (hLb.trans hDb.symm)
      (hTb.trans hDb.symm)).trans
        (pointed_composition_germ_congr left.map L.map top.map T.map hleft hL hT).symm))


section PathCoefficients
variable {s t : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (Fin (s+t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,u} s t M)
  (φ : ∀ x : M, F.ULeaf x ≃ₜ ℂ)
  (hzero : ∀ x, φ x (F.uPoint x) = 0)
  (hloc : ∀ (x y : M) (e : LocalPlaqueTransport F x y),
    ∃ D : ℂ ≃L[ℂ] ℂ,
      ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e.map z) = D (φ x z))
  {q : Quotient F.stablePartition}
  {x y : IntrinsicFoliationLeaf F.stablePartition q}

include hloc

/-- The coefficient furnished by a finite chain belongs to every representative of the original subpath. (Zhang, Remark 1.3.5) -/
theorem holonomy_coefficient_exists (γ : Path x y) (a b : unitInterval) (hab : a ≤ b) :
    ∃ D : ℂ ≃L[ℂ] ℂ, ∀ e : PathHolonomyRepresentative F γ a b,
      ∀ᶠ z in 𝓝 (F.uPoint (γ a).val),
        φ (γ b).val (e.map z) = D (φ (γ a).val z) := by
  obtain ⟨e⟩ := path_holonomy_subinterval_representative_exists F γ a b hab
  obtain ⟨D,hD⟩ := plaque_chain_linear_coefficient F φ hloc γ e.chain
  refine ⟨D,?_⟩
  intro r
  have hg := Germ.coe_eq.mp (same_subpath_plaque_chain_germ F γ e.chain r.map r.chain)
  filter_upwards [hD,hg] with z hz hgz
  rw [← hgz]
  exact hz

private def pathCoefficient (γ : Path x y) (a b : unitInterval) (hab : a ≤ b) :
    ℂ ≃L[ℂ] ℂ := (holonomy_coefficient_exists F φ hloc γ a b hab).choose

private theorem pathCoefficient_spec (γ : Path x y) (a b : unitInterval) (hab : a ≤ b)
    (e : PathHolonomyRepresentative F γ a b) :
    ∀ᶠ z in 𝓝 (F.uPoint (γ a).val),
      φ (γ b).val (e.map z) = pathCoefficient F φ hloc γ a b hab (φ (γ a).val z) :=
  (holonomy_coefficient_exists F φ hloc γ a b hab).choose_spec e

include hzero

private theorem pathCoefficient_subdivide (γ : Path x y)
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) :
    pathCoefficient F φ hloc γ a c (hab.trans hbc) =
      (pathCoefficient F φ hloc γ a b hab).trans
        (pathCoefficient F φ hloc γ b c hbc) := by
  obtain ⟨l⟩ := path_holonomy_subinterval_representative_exists F γ a b hab
  obtain ⟨r⟩ := path_holonomy_subinterval_representative_exists F γ b c hbc
  obtain ⟨e⟩ := path_holonomy_subinterval_representative_exists F γ a c (hab.trans hbc)
  exact holonomy_linear_coefficient_subdivide F φ hzero γ a b c hab hbc l r e _ _ _
    (pathCoefficient_spec F φ hloc γ a b hab l)
    (pathCoefficient_spec F φ hloc γ b c hbc r)
    (pathCoefficient_spec F φ hloc γ a c (hab.trans hbc) e)

private theorem pathCoefficient_self (γ : Path x y) (a : unitInterval) :
    pathCoefficient F φ hloc γ a a le_rfl = ContinuousLinearEquiv.refl ℂ ℂ := by
  let D := pathCoefficient F φ hloc γ a a le_rfl
  have hh : D = D.trans D := pathCoefficient_subdivide F φ hzero hloc γ a a a le_rfl le_rfl
  ext z
  have h := congrArg (fun K : ℂ ≃L[ℂ] ℂ ↦ K (D.symm z)) hh
  simpa only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.refl_apply] using h.symm

private theorem pathCoefficient_constant (γ : Path x y) (hc : ∀ v, γ v = x)
    (a b : unitInterval) (hab : a ≤ b) :
    pathCoefficient F φ hloc γ a b hab = ContinuousLinearEquiv.refl ℂ ℂ := by
  have hy : y = x := γ.target.symm.trans (hc 1)
  subst y
  have hγ : γ = Path.refl x := by
    apply Path.ext
    funext v
    exact hc v
  subst γ
  obtain ⟨e⟩ := path_holonomy_subinterval_representative_exists F (Path.refl x) a b hab
  have hg := Germ.coe_eq.mp (constant_path_representative_identity_germ F x a b e)
  apply holonomy_linear_coefficient_unique F φ hzero e.map _ _
    (pathCoefficient_spec F φ hloc (Path.refl x) a b hab e)
  filter_upwards [hg] with z hz
  change e.map z = z at hz
  exact congrArg (φ x.val) hz

end PathCoefficients


private def squareRow {X : Type*} [TopologicalSpace X]
    (H : unitInterval × unitInterval → X) (hH : Continuous H) (a : unitInterval) :
    Path (H (a,0)) (H (a,1)) :=
  ⟨⟨fun v ↦ H (a,v), hH.comp (continuous_const.prodMk continuous_id)⟩, rfl, rfl⟩

private def squareColumn {X : Type*} [TopologicalSpace X]
    (H : unitInterval × unitInterval → X) (hH : Continuous H) (a : unitInterval) :
    Path (H (0,a)) (H (1,a)) :=
  ⟨⟨fun v ↦ H (v,a), hH.comp (continuous_id.prodMk continuous_const)⟩, rfl, rfl⟩

section SquareCoefficients
variable {s t : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (Fin (s+t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,u} s t M)
  (φ : ∀ x : M, F.ULeaf x ≃ₜ ℂ)
  (hzero : ∀ x, φ x (F.uPoint x) = 0)
  (hloc : ∀ (x y : M) (e : LocalPlaqueTransport F x y),
    ∃ D : ℂ ≃L[ℂ] ℂ,
      ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e.map z) = D (φ x z))
  {q : Quotient F.stablePartition}
  (H : unitInterval × unitInterval → IntrinsicFoliationLeaf F.stablePartition q)
  (hH : Continuous H)

include hzero in
private theorem pathCoefficient_rectangle
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (box : F.boxIndex) (w : FoliationCoordinateDisk t)
    (hcell : ∀ z ∈ Icc a b ×ˢ Icc c d, ∃ r : FoliationCoordinateDisk s,
      ((F.box box).chart (r,w)).val = (H z).val) :
    (pathCoefficient F φ hloc (squareRow H hH a) c d hcd).trans
      (pathCoefficient F φ hloc (squareColumn H hH d) a b hab) =
    (pathCoefficient F φ hloc (squareColumn H hH c) a b hab).trans
      (pathCoefficient F φ hloc (squareRow H hH b) c d hcd) := by
  obtain ⟨B⟩ := path_holonomy_subinterval_representative_exists F (squareRow H hH a) c d hcd
  obtain ⟨T⟩ := path_holonomy_subinterval_representative_exists F (squareRow H hH b) c d hcd
  obtain ⟨L⟩ := path_holonomy_subinterval_representative_exists F (squareColumn H hH c) a b hab
  obtain ⟨R⟩ := path_holonomy_subinterval_representative_exists F (squareColumn H hH d) a b hab
  have hg := plaque_rectangle_representatives_commute F H hH a b c d hab hcd box w hcell B T L R
  have hBR := holonomy_linear_coefficient_comp F φ B.toPointedLeafHomeomorph
    R.toPointedLeafHomeomorph _ _ (pathCoefficient_spec F φ hloc _ c d hcd B)
    (pathCoefficient_spec F φ hloc _ a b hab R)
  have hLT := holonomy_linear_coefficient_comp F φ L.toPointedLeafHomeomorph
    T.toPointedLeafHomeomorph _ _ (pathCoefficient_spec F φ hloc _ a b hab L)
    (pathCoefficient_spec F φ hloc _ c d hcd T)
  apply holonomy_linear_coefficient_unique F φ hzero (fun z ↦ R.map (B.map z)) _ _ hBR
  filter_upwards [hg,hLT] with z hz hz'
  change R.map (B.map z) = T.map (L.map z) at hz
  exact (congrArg (φ (H (b,d)).val) hz).trans hz'


include hzero in
private theorem pathCoefficient_strip
    {n : ℕ} (a : Fin (n+2) → unitInterval) (ha : StrictMono a)
    (j : Fin (n+1))
    (hcells : ∀ k : Fin (n+1), ∃ box : F.boxIndex, ∃ w : FoliationCoordinateDisk t,
      ∀ z ∈ Icc (a j.castSucc) (a j.succ) ×ˢ Icc (a k.castSucc) (a k.succ),
        ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (H z).val) :
    (pathCoefficient F φ hloc (squareRow H hH (a j.castSucc)) (a 0) (a (Fin.last (n+1)))
      (ha.monotone (Fin.zero_le _))).trans
      (pathCoefficient F φ hloc (squareColumn H hH (a (Fin.last (n+1))))
        (a j.castSucc) (a j.succ) (ha.monotone (Fin.castSucc_le_succ j))) =
    (pathCoefficient F φ hloc (squareColumn H hH (a 0))
      (a j.castSucc) (a j.succ) (ha.monotone (Fin.castSucc_le_succ j))).trans
      (pathCoefficient F φ hloc (squareRow H hH (a j.succ)) (a 0) (a (Fin.last (n+1)))
        (ha.monotone (Fin.zero_le _))) := by
  let bot (k : Fin (n+2)) := pathCoefficient F φ hloc (squareRow H hH (a j.castSucc))
    (a 0) (a k) (ha.monotone (Fin.zero_le k))
  let top (k : Fin (n+2)) := pathCoefficient F φ hloc (squareRow H hH (a j.succ))
    (a 0) (a k) (ha.monotone (Fin.zero_le k))
  let vert (k : Fin (n+2)) := pathCoefficient F φ hloc (squareColumn H hH (a k))
    (a j.castSucc) (a j.succ) (ha.monotone (Fin.castSucc_le_succ j))
  have hs : ∀ k : Fin (n+2), (bot k).trans (vert k) = (vert 0).trans (top k) := by
    apply Fin.induction
    · have hb : bot 0 = ContinuousLinearEquiv.refl ℂ ℂ :=
        pathCoefficient_self F φ hzero hloc _ _
      have ht : top 0 = ContinuousLinearEquiv.refl ℂ ℂ :=
        pathCoefficient_self F φ hzero hloc _ _
      rw [hb,ht]
      rfl
    · intro k ih
      obtain ⟨box,w,hw⟩ := hcells k
      let B := pathCoefficient F φ hloc (squareRow H hH (a j.castSucc))
        (a k.castSucc) (a k.succ) (ha.monotone (Fin.castSucc_le_succ k))
      let T := pathCoefficient F φ hloc (squareRow H hH (a j.succ))
        (a k.castSucc) (a k.succ) (ha.monotone (Fin.castSucc_le_succ k))
      have hb : bot k.succ = (bot k.castSucc).trans B :=
        pathCoefficient_subdivide F φ hzero hloc _ _ _ _
          (ha.monotone (Fin.zero_le _)) (ha.monotone (Fin.castSucc_le_succ k))
      have ht : top k.succ = (top k.castSucc).trans T :=
        pathCoefficient_subdivide F φ hzero hloc _ _ _ _
          (ha.monotone (Fin.zero_le _)) (ha.monotone (Fin.castSucc_le_succ k))
      have he : B.trans (vert k.succ) = (vert k.castSucc).trans T :=
        pathCoefficient_rectangle F φ hzero hloc H hH _ _ _ _
          (ha.monotone (Fin.castSucc_le_succ j))
          (ha.monotone (Fin.castSucc_le_succ k)) box w hw
      rw [hb,ht]
      ext z
      change vert k.succ (B (bot k.castSucc z)) = T (top k.castSucc (vert 0 z))
      exact (congrArg (fun K : ℂ ≃L[ℂ] ℂ ↦ K (bot k.castSucc z)) he).trans
        (congrArg T (congrArg (fun K : ℂ ≃L[ℂ] ℂ ↦ K z) ih))
  exact hs (Fin.last (n+1))

private theorem pathCoefficient_interval_congr
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b a' b' : unitInterval) (hab : a ≤ b) (hab' : a' ≤ b')
    (ha : a = a') (hb : b = b') :
    pathCoefficient F φ hloc γ a b hab = pathCoefficient F φ hloc γ a' b' hab' := by
  subst a'
  subst b'
  rfl

private theorem pathCoefficient_row_congr (r r' : unitInterval) (hr : r = r') :
    pathCoefficient F φ hloc (squareRow H hH r) 0 1 zero_le_one =
      pathCoefficient F φ hloc (squareRow H hH r') 0 1 zero_le_one := by
  subst r'
  rfl

private theorem pathCoefficient_column_congr (r r' : unitInterval) (hr : r = r')
    (a b : unitInterval) (hab : a ≤ b) :
    pathCoefficient F φ hloc (squareColumn H hH r) a b hab =
      pathCoefficient F φ hloc (squareColumn H hH r') a b hab := by
  subst r'
  rfl

include hzero in
/-- A fixed-endpoint intrinsic homotopy preserves the linear holonomy coefficient. (Zhang, Theorem 1.3.8) -/
theorem pathCoefficient_homotopy_square
    (hleft : ∀ r, H (r,0) = H (0,0)) (hright : ∀ r, H (r,1) = H (0,1)) :
    pathCoefficient F φ hloc (squareRow H hH 0) 0 1 zero_le_one =
      pathCoefficient F φ hloc (squareRow H hH 1) 0 1 zero_le_one := by
  obtain ⟨n,a,ha,h0,h1,hcells⟩ := intrinsic_plaque_square_subdivision F q H hH
  have hadj (j : Fin (n+1)) :
      pathCoefficient F φ hloc (squareRow H hH (a j.castSucc)) 0 1 zero_le_one =
        pathCoefficient F φ hloc (squareRow H hH (a j.succ)) 0 1 zero_le_one := by
    have hs := pathCoefficient_strip F φ hzero hloc H hH a ha j (fun k ↦ by
      obtain ⟨box,w,_,hw⟩ := hcells j k
      exact ⟨box,w,hw⟩)
    have hn (r : unitInterval) := pathCoefficient_interval_congr F φ hloc
      (squareRow H hH r) (a 0) (a (Fin.last (n+1))) 0 1
      (ha.monotone (Fin.zero_le _)) zero_le_one h0 h1
    rw [hn,hn] at hs
    have hl := pathCoefficient_constant F φ hzero hloc (squareColumn H hH 0)
      (fun v ↦ hleft v) (a j.castSucc) (a j.succ)
      (ha.monotone (Fin.castSucc_le_succ j))
    have hr := pathCoefficient_constant F φ hzero hloc (squareColumn H hH 1)
      (fun v ↦ hright v) (a j.castSucc) (a j.succ)
      (ha.monotone (Fin.castSucc_le_succ j))
    have hl' := (pathCoefficient_column_congr F φ hloc H hH _ _ h0 _ _
      (ha.monotone (Fin.castSucc_le_succ j))).trans hl
    have hr' := (pathCoefficient_column_congr F φ hloc H hH _ _ h1 _ _
      (ha.monotone (Fin.castSucc_le_succ j))).trans hr
    rw [hl',hr'] at hs
    exact hs
  have hall : ∀ k : Fin (n+2),
      pathCoefficient F φ hloc (squareRow H hH (a 0)) 0 1 zero_le_one =
        pathCoefficient F φ hloc (squareRow H hH (a k)) 0 1 zero_le_one := by
    apply Fin.induction
    · rfl
    · intro k ih
      exact ih.trans (hadj k)
  exact (pathCoefficient_row_congr F φ hloc H hH _ _ h0).symm.trans
    ((hall (Fin.last (n+1))).trans (pathCoefficient_row_congr F φ hloc H hH _ _ h1))


private theorem pathCoefficient_path_congr
    {x y x' y' : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (η : Path x' y') (he : ∀ v, γ v = η v)
    (a b : unitInterval) (hab : a ≤ b) :
    pathCoefficient F φ hloc γ a b hab = pathCoefficient F φ hloc η a b hab := by
  have hx : x = x' := γ.source.symm.trans ((he 0).trans η.source)
  have hy : y = y' := γ.target.symm.trans ((he 1).trans η.target)
  subst x'
  subst y'
  have hγη : γ = η := Path.ext (funext he)
  subst η
  rfl

include hzero in
/-- Homotopic paths have equal normalized linear coefficients. (Nisoli, Theorem 1.3.8) -/
theorem pathCoefficient_homotopy
    {x y : IntrinsicFoliationLeaf F.stablePartition q}
    (γ η : Path x y) (h : γ.Homotopy η) :
    pathCoefficient F φ hloc γ 0 1 zero_le_one =
      pathCoefficient F φ hloc η 0 1 zero_le_one := by
  have he := pathCoefficient_homotopy_square F φ hzero hloc h h.continuous
    (fun r ↦ (h.source r).trans (h.source 0).symm)
    (fun r ↦ (h.target r).trans (h.target 0).symm)
  have hγ := pathCoefficient_path_congr F φ hloc (squareRow h h.continuous 0) γ
    (fun v ↦ h.apply_zero v) 0 1 zero_le_one
  have hη := pathCoefficient_path_congr F φ hloc (squareRow h h.continuous 1) η
    (fun v ↦ h.apply_one v) 0 1 zero_le_one
  exact hγ.symm.trans (he.trans hη)

end SquareCoefficients


section ReparamCoefficients
variable {s t : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (Fin (s+t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,u} s t M)
  (φ : ∀ x : M, F.ULeaf x ≃ₜ ℂ)
  (hzero : ∀ x, φ x (F.uPoint x) = 0)
  (hloc : ∀ (x y : M) (e : LocalPlaqueTransport F x y),
    ∃ D : ℂ ≃L[ℂ] ℂ,
      ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e.map z) = D (φ x z))
  {q : Quotient F.stablePartition}

include hzero in
private theorem local_coefficients_same_box
    {x y x' y' : M} (hx : x = x') (hy : y = y')
    (e : LocalPlaqueTransport F x y) (e' : LocalPlaqueTransport F x' y')
    (hb : e.box = e'.box) (D K : ℂ ≃L[ℂ] ℂ)
    (hD : ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e.map z) = D (φ x z))
    (hK : ∀ᶠ z in 𝓝 (F.uPoint x'), φ y' (e'.map z) = K (φ x' z)) : D = K := by
  subst x'
  subst y'
  have hfirst : e.first = e'.first := by
    have h := e.first_point
    rw [hb] at h
    exact congrArg Prod.fst ((F.box e'.box).chart.injective
      (Subtype.ext (h.trans e'.first_point.symm)))
  have hsecond : e.second = e'.second := by
    have h := e.second_point
    rw [hb] at h
    exact congrArg Prod.fst ((F.box e'.box).chart.injective
      (Subtype.ext (h.trans e'.second_point.symm)))
  have hg := Germ.coe_eq.mp (same_box_plaque_germ_g10 F e e' hb hfirst hsecond)
  apply holonomy_linear_coefficient_unique F φ hzero e.map D K hD
  filter_upwards [hg,hK] with z hz hk
  rw [hz]
  exact hk

include hzero in
private theorem pathCoefficient_eq_local
    {x y : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (a b : unitInterval) (hab : a ≤ b)
    (e : LocalPlaqueTransport F (γ a).val (γ b).val)
    (hin : ∀ v : unitInterval, a ≤ v → v ≤ b →
      ∃ r : FoliationCoordinateDisk s, ((F.box e.box).chart (r,e.transverse)).val = (γ v).val)
    (D : ℂ ≃L[ℂ] ℂ)
    (hD : ∀ᶠ z in 𝓝 (F.uPoint (γ a).val), φ (γ b).val (e.map z) = D (φ (γ a).val z)) :
    pathCoefficient F φ hloc γ a b hab = D := by
  obtain ⟨r⟩ := path_holonomy_subinterval_representative_exists F γ a b hab
  have hg := Germ.coe_eq.mp (plaque_chain_germ_in_one_plaque F γ r.chain e hin)
  apply holonomy_linear_coefficient_unique F φ hzero r.map _ D
    (pathCoefficient_spec F φ hloc γ a b hab r)
  filter_upwards [hg,hD] with z hz hd
  rw [hz]
  exact hd

include hzero in
private theorem pathCoefficient_same_plaque
    {x y x' y' : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (η : Path x' y') (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (hx : γ a = η c) (hy : γ b = η d)
    (box : F.boxIndex) (w : FoliationCoordinateDisk t)
    (hγ : ∀ v : unitInterval, a ≤ v → v ≤ b →
      ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (γ v).val)
    (hη : ∀ v : unitInterval, c ≤ v → v ≤ d →
      ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (η v).val) :
    pathCoefficient F φ hloc γ a b hab = pathCoefficient F φ hloc η c d hcd := by
  obtain ⟨ga,hga⟩ := hγ a le_rfl hab
  obtain ⟨gb,hgb⟩ := hγ b hab le_rfl
  obtain ⟨ec,hec⟩ := hη c le_rfl hcd
  obtain ⟨ed,hed⟩ := hη d hcd le_rfl
  obtain ⟨e,heb,_,_,hew,_⟩ := local_plaque_transport_of_box F box ga gb w _ _ hga hgb
  obtain ⟨e',he'b,_,_,he'w,_⟩ := local_plaque_transport_of_box F box ec ed w _ _ hec hed
  obtain ⟨D,hD⟩ := hloc _ _ e
  obtain ⟨K,hK⟩ := hloc _ _ e'
  have heγ : pathCoefficient F φ hloc γ a b hab = D :=
    pathCoefficient_eq_local F φ hzero hloc γ a b hab e (by
      intro v hv hv'
      obtain ⟨r,hr⟩ := hγ v hv hv'
      refine ⟨r,?_⟩
      rw [hew]
      exact (congrArg (fun j ↦ ((F.box j).chart (r,w)).val) heb).trans hr) D hD
  have heη : pathCoefficient F φ hloc η c d hcd = K :=
    pathCoefficient_eq_local F φ hzero hloc η c d hcd e' (by
      intro v hv hv'
      obtain ⟨r,hr⟩ := hη v hv hv'
      refine ⟨r,?_⟩
      rw [he'w]
      exact (congrArg (fun j ↦ ((F.box j).chart (r,w)).val) he'b).trans hr) K hK
  exact heγ.trans ((local_coefficients_same_box F φ hzero
    (congrArg Subtype.val hx) (congrArg Subtype.val hy) e e' (heb.trans he'b.symm)
    D K hD hK).trans heη.symm)


include hzero in
/-- Increasing continuous changes of parameter preserve the subpath coefficient. (Nisoli) -/
theorem pathCoefficient_reparam
    {x y x' y' : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (η : Path x' y') (ρ : unitInterval → unitInterval)
    (hc : Continuous ρ) (hm : Monotone ρ) (he : ∀ v, η v = γ (ρ v)) :
    pathCoefficient F φ hloc γ (ρ 0) (ρ 1) (hm zero_le_one) =
      pathCoefficient F φ hloc η 0 1 zero_le_one := by
  let H : unitInterval × unitInterval → IntrinsicFoliationLeaf F.stablePartition q :=
    fun z ↦ η z.2
  have hH : Continuous H := η.continuous.comp continuous_snd
  obtain ⟨n,a,ha,h0,h1,hcells⟩ := intrinsic_plaque_square_subdivision F q H hH
  have hp : ∀ k : Fin (n+2),
      pathCoefficient F φ hloc γ (ρ (a 0)) (ρ (a k)) (hm (ha.monotone (Fin.zero_le _))) =
        pathCoefficient F φ hloc η (a 0) (a k) (ha.monotone (Fin.zero_le _)) := by
    apply Fin.induction
    · rw [pathCoefficient_self F φ hzero hloc, pathCoefficient_self F φ hzero hloc]
    · intro k ih
      obtain ⟨box,w,_,hw⟩ := hcells 0 k
      have hη : ∀ v : unitInterval, a k.castSucc ≤ v → v ≤ a k.succ →
          ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (η v).val := by
        intro v hv hv'
        exact hw (a 0,v) ⟨⟨le_rfl,ha.monotone (Fin.zero_le _)⟩,⟨hv,hv'⟩⟩
      have hγ : ∀ v : unitInterval, ρ (a k.castSucc) ≤ v → v ≤ ρ (a k.succ) →
          ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (γ v).val := by
        intro v hv hv'
        have hsv := (hc.continuousOn.surjOn_Icc
          (show a k.castSucc ∈ Icc (a k.castSucc) (a k.succ) from
            ⟨le_rfl,ha.monotone (Fin.castSucc_le_succ k)⟩)
          (show a k.succ ∈ Icc (a k.castSucc) (a k.succ) from
            ⟨ha.monotone (Fin.castSucc_le_succ k),le_rfl⟩)) ⟨hv,hv'⟩
        obtain ⟨u,hu,hρu⟩ := hsv
        obtain ⟨r,hr⟩ := hη u hu.1 hu.2
        exact ⟨r,hr.trans (congrArg Subtype.val ((he u).trans (congrArg γ hρu)))⟩
      have hseg := pathCoefficient_same_plaque F φ hzero hloc γ η
        (ρ (a k.castSucc)) (ρ (a k.succ)) (a k.castSucc) (a k.succ)
        (hm (ha.monotone (Fin.castSucc_le_succ k)))
        (ha.monotone (Fin.castSucc_le_succ k)) (he _).symm (he _).symm box w hγ hη
      have hγsplit := pathCoefficient_subdivide F φ hzero hloc γ
        (ρ (a 0)) (ρ (a k.castSucc)) (ρ (a k.succ))
        (hm (ha.monotone (Fin.zero_le _))) (hm (ha.monotone (Fin.castSucc_le_succ k)))
      have hηsplit := pathCoefficient_subdivide F φ hzero hloc η
        (a 0) (a k.castSucc) (a k.succ)
        (ha.monotone (Fin.zero_le _)) (ha.monotone (Fin.castSucc_le_succ k))
      exact hγsplit.trans ((congrArg₂ ContinuousLinearEquiv.trans ih hseg).trans hηsplit.symm)
  have hγ := pathCoefficient_interval_congr F φ hloc γ
    (ρ (a 0)) (ρ (a (Fin.last (n+1)))) (ρ 0) (ρ 1)
    (hm (ha.monotone (Fin.zero_le _))) (hm zero_le_one)
    (congrArg ρ h0) (congrArg ρ h1)
  have hη := pathCoefficient_interval_congr F φ hloc η
    (a 0) (a (Fin.last (n+1))) 0 1
    (ha.monotone (Fin.zero_le _)) zero_le_one h0 h1
  exact hγ.symm.trans ((hp (Fin.last (n+1))).trans hη)


include hzero in
private theorem pathCoefficient_subpath
    {x y : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (a b : unitInterval) (hab : a ≤ b) :
    pathCoefficient F φ hloc (γ.subpath a b) 0 1 zero_le_one =
      pathCoefficient F φ hloc γ a b hab := by
  have hm : Monotone (Icc.convexComb a b) := by
    intro u v huv
    change (1 - (u : ℝ)) * a + u * b ≤ (1 - (v : ℝ)) * a + v * b
    have hab' : (a : ℝ) ≤ b := hab
    have huv' : (u : ℝ) ≤ v := huv
    nlinarith
  have hh := pathCoefficient_reparam F φ hzero hloc γ (γ.subpath a b)
    (Icc.convexComb a b) (by fun_prop) hm (fun _ ↦ rfl)
  have hi := pathCoefficient_interval_congr F φ hloc γ
    (Icc.convexComb a b 0) (Icc.convexComb a b 1) a b (hm zero_le_one) hab
    (Icc.convexComb_zero a b) (Icc.convexComb_one a b)
  exact hh.symm.trans hi

include hzero in
private theorem pathCoefficient_trans
    {x y z : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (η : Path y z) :
    pathCoefficient F φ hloc (γ.trans η) 0 1 zero_le_one =
      (pathCoefficient F φ hloc γ 0 1 zero_le_one).trans
        (pathCoefficient F φ hloc η 0 1 zero_le_one) := by
  let m : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
  let l : unitInterval → unitInterval := Icc.convexComb 0 m
  let r : unitInterval → unitInterval := Icc.convexComb m 1
  have hl : Monotone l := by
    intro u v huv
    change (1 - (u : ℝ)) * 0 + u * (1/2) ≤ (1 - (v : ℝ)) * 0 + v * (1/2)
    have huv' : (u : ℝ) ≤ v := huv
    linarith
  have hr : Monotone r := by
    intro u v huv
    change (1 - (u : ℝ)) * (1/2) + u * 1 ≤ (1 - (v : ℝ)) * (1/2) + v * 1
    have huv' : (u : ℝ) ≤ v := huv
    linarith
  have hle : ∀ v, γ v = (γ.trans η) (l v) := by
    intro v
    rw [Path.trans_apply, dite_eq_left (show ((l v : unitInterval) : ℝ) ≤ 1/2 by
      change (1-(v:ℝ))*0+(v:ℝ)*(1/2) ≤ 1/2
      linarith [v.property.2])]
    congr 1
    apply Subtype.ext
    change (v : ℝ) = 2*((1-(v:ℝ))*0+(v:ℝ)*(1/2))
    ring
  have hre : ∀ v, η v = (γ.trans η) (r v) := by
    intro v
    have hv : (1/2 : ℝ) ≤ r v := by
      change (1/2 : ℝ) ≤ (1-(v:ℝ))*(1/2)+(v:ℝ)*1
      linarith [v.property.1]
    calc
      η v = η.extend (2 * (r v : ℝ) - 1) := by
        have ht : 2 * (r v : ℝ) - 1 = (v : ℝ) := by
          change 2*((1-(v:ℝ))*(1/2)+(v:ℝ)*1)-1 = (v:ℝ)
          ring
        rw [ht, η.extend_extends']
      _ = (γ.trans η).extend (r v : ℝ) := (Path.extend_trans_of_half_le γ η hv).symm
      _ = (γ.trans η) (r v) := (γ.trans η).extend_extends' _
  have hL := pathCoefficient_reparam F φ hzero hloc (γ.trans η) γ l (by dsimp [l]; fun_prop) hl hle
  have hR := pathCoefficient_reparam F φ hzero hloc (γ.trans η) η r (by dsimp [r]; fun_prop) hr hre
  have hLi := pathCoefficient_interval_congr F φ hloc (γ.trans η)
    (l 0) (l 1) 0 m (hl zero_le_one) (by exact m.property.1)
    (Icc.convexComb_zero 0 m) (Icc.convexComb_one 0 m)
  have hRi := pathCoefficient_interval_congr F φ hloc (γ.trans η)
    (r 0) (r 1) m 1 (hr zero_le_one) (by exact m.property.2)
    (Icc.convexComb_zero m 1) (Icc.convexComb_one m 1)
  exact (pathCoefficient_subdivide F φ hzero hloc (γ.trans η) 0 m 1 m.property.1 m.property.2).trans
    (congrArg₂ ContinuousLinearEquiv.trans (hLi.symm.trans hL) (hRi.symm.trans hR))

end ReparamCoefficients


/-- Centered complete coordinates with linear plaque germs give global holonomy when the source leaves have endpoint-fixed path homotopies. (Zhang, Lemma 2.10) -/
theorem global_holonomy_of_complete_linear_coordinates
    {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (C : IntrinsicComplexUnstableLeaves F)
    (φ : ∀ x : M, letI := C.charts (Quotient.mk F.unstablePartition x)
      Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ) (F.ULeaf x) ℂ ∞)
    (hzero : ∀ x, φ x (F.uPoint x) = 0)
    (hloc : ∀ (x y : M) (e : LocalPlaqueTransport F x y),
      ∃ D : ℂ ≃L[ℂ] ℂ,
        ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e.map z) = D (φ x z))
    (hpaths : ∀ (q : Quotient F.stablePartition)
      (x y : IntrinsicFoliationLeaf F.stablePartition q) (γ η : Path x y),
      Nonempty (γ.Homotopy η)) :
    ∃ G : GlobalSHolonomyData F C,
      (∀ (q : Quotient F.stablePartition)
        (x y : IntrinsicFoliationLeaf F.stablePartition q)
        (γ η : Path x y) (z : F.ULeaf x.val), G.transport γ z = G.transport η z) ∧
      (∀ (q : Quotient F.stablePartition)
        (x : IntrinsicFoliationLeaf F.stablePartition q) (z : F.ULeaf x.val),
        G.transport (Path.refl x) z = z) ∧
      (∀ (q : Quotient F.stablePartition)
        (x y : IntrinsicFoliationLeaf F.stablePartition q) (γ : Path x y)
        (e : PathHolonomyRepresentative F γ 0 1),
        (Germ.ofFun (fun z : F.ULeaf x.val ↦ G.transport γ z) :
          Germ (𝓝 (F.uPoint x.val)) (F.ULeaf y.val)) =
          Germ.ofFun (fun z : F.ULeaf x.val ↦
            castIntrinsicULeaf F (congrArg Subtype.val γ.target)
              (e.map (castIntrinsicULeaf F (congrArg Subtype.val γ.source).symm z)))) := by
  classical
  let ψ : ∀ x : M, F.ULeaf x ≃ₜ ℂ := fun x ↦
    letI := C.charts (Quotient.mk F.unstablePartition x)
    (φ x).toHomeomorph
  let T {q : Quotient F.stablePartition}
      {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) :
      IntrinsicLeafBiholomorph F C x.val y.val :=
    letI := C.charts (Quotient.mk F.unstablePartition x.val)
    letI := C.charts (Quotient.mk F.unstablePartition y.val)
    ((φ x.val).trans (pathCoefficient F ψ hloc γ 0 1 zero_le_one).toDiffeomorph).trans
      (φ y.val).symm
  have ht {q : Quotient F.stablePartition}
      {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) (z : F.ULeaf x.val) :
      φ y.val (T γ z) = pathCoefficient F ψ hloc γ 0 1 zero_le_one (φ x.val z) := by
    let := C.charts (Quotient.mk F.unstablePartition y.val)
    exact (φ y.val).apply_symm_apply _
  have hind {q : Quotient F.stablePartition}
      {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ η : Path x y) (z : F.ULeaf x.val) :
      T γ z = T η z := by
    obtain ⟨h⟩ := hpaths q x y γ η
    apply (φ y.val).injective
    change φ y.val (T γ z) = φ y.val (T η z)
    rw [ht,ht,pathCoefficient_homotopy F ψ hzero hloc γ η h]
  have hid {q : Quotient F.stablePartition}
      (x : IntrinsicFoliationLeaf F.stablePartition q) (z : F.ULeaf x.val) :
      T (Path.refl x) z = z := by
    apply (φ x.val).injective
    change φ x.val (T (Path.refl x) z) = φ x.val z
    rw [ht,pathCoefficient_constant F ψ hzero hloc (Path.refl x) (fun _ ↦ rfl)]
    rfl
  have hconcat {q : Quotient F.stablePartition}
      {x y z : IntrinsicFoliationLeaf F.stablePartition q}
      (γ : Path x y) (η : Path y z) (w : F.ULeaf x.val) :
      T (γ.trans η) w = T η (T γ w) := by
    apply (φ z.val).injective
    change φ z.val (T (γ.trans η) w) = φ z.val (T η (T γ w))
    rw [ht,ht,ht,pathCoefficient_trans F ψ hzero hloc γ η]
    rfl
  have hext {q : Quotient F.stablePartition}
      {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
      (e : PathHolonomyRepresentative F γ 0 1) :
      (Germ.ofFun (fun z : F.ULeaf x.val ↦ T γ z) :
        Germ (𝓝 (F.uPoint x.val)) (F.ULeaf y.val)) =
        Germ.ofFun (fun z : F.ULeaf x.val ↦
          castIntrinsicULeaf F (congrArg Subtype.val γ.target)
            (e.map (castIntrinsicULeaf F (congrArg Subtype.val γ.source).symm z))) := by
    have hcast : ∀ {p r : M} (h : p = r) (z : F.ULeaf p),
        φ r (castIntrinsicULeaf F h z) = φ p z := by
      intro p r h z
      subst r
      rfl
    have hct : ∀ {p r : M} (h : p = r),
        Tendsto (castIntrinsicULeaf F h) (𝓝 (F.uPoint p)) (𝓝 (F.uPoint r)) := by
      intro p r h
      subst r
      exact tendsto_id
    have hmap := pathCoefficient_spec F ψ hloc γ 0 1 zero_le_one e
    apply Germ.coe_eq.mpr
    filter_upwards [(hct (congrArg Subtype.val γ.source).symm).eventually hmap] with z hz
    apply (φ y.val).injective
    change φ y.val (T γ z) = φ y.val
      (castIntrinsicULeaf F (congrArg Subtype.val γ.target)
        (e.map (castIntrinsicULeaf F (congrArg Subtype.val γ.source).symm z)))
    rw [ht,hcast]
    change _ = ψ (γ 1).val (e.map _)
    rw [hz]
    exact congrArg (pathCoefficient F ψ hloc γ 0 1 zero_le_one)
      (hcast (congrArg Subtype.val γ.source).symm z).symm
  let G : GlobalSHolonomyData F C := {
    localContinuation := fun γ ↦ Classical.choice (local_holonomy_continuation_exists_g9 F γ)
    transport := T
    extends_local := fun γ ↦ hext γ _
    restriction := by
      intro q x y γ a b c hab hbc z
      apply (φ (γ c).val).injective
      change φ (γ c).val (T (γ.subpath a c) z) =
        φ (γ c).val (T (γ.subpath b c) (T (γ.subpath a b) z))
      rw [ht,ht,ht,pathCoefficient_subpath F ψ hzero hloc γ a c (hab.trans hbc),
        pathCoefficient_subpath F ψ hzero hloc γ b c hbc,
        pathCoefficient_subpath F ψ hzero hloc γ a b hab,
        pathCoefficient_subdivide F ψ hzero hloc γ a b c hab hbc]
      rfl
    concatenation := hconcat
    reversal := by
      intro q x y γ z
      let := C.charts (Quotient.mk F.unstablePartition x.val)
      let := C.charts (Quotient.mk F.unstablePartition y.val)
      apply (T γ).injective
      change T γ (T γ.symm z) = T γ ((T γ).symm z)
      rw [← hconcat,hind (γ.symm.trans γ) (Path.refl y),hid]
      exact ((T γ).apply_symm_apply z).symm }
  exact ⟨G,fun _ _ _ γ η z ↦ hind γ η z,fun _ x z ↦ hid x z,
    fun _ _ _ γ e ↦ hext γ e⟩




end HolomorphicAnosov
