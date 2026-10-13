import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Geometry.HPSNativePlaqueFamilyData
import HolomorphicAnosov.Dynamics.Anosov.FiniteC1NativePlaqueFamily
import HolomorphicAnosov.Dynamics.Anosov.FiniteOrderNativePlaqueCoherence
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import Mathlib.Logic.Function.Iterate
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-! Source-bound original-f plaque transports and intrinsic stage topology.
Source: HPS pp.61--63,111--116 and the current parent GL8--GL10.
All operators and charts are actual data. These declarations assert no
existence of global laminations or equality of unrelated source families. -/

open scoped ContDiff Manifold Topology _root_.Topology Bundle ENNReal
open TopologicalSpace Set

universe u
namespace HolomorphicAnosov.HPS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Concrete source-disc to leaf-stage binding.

Source: HPS (5.5), pp.61--63; (6B.1)--(6B.4), pp.111--114; intrinsic
topology pp.115--116 and the parent GL8--GL10. The smooth leaf structures are
parameters, and stage subtypes keep their induced INTRINSIC leaf topology.
The ambient inclusion is not assumed to embed the entire leaf. Each source
plaque and each transported stage, however, is a genuine local embedding.

The same `f` is used in every iterate, and `sourceMap` is the external chosen
HPS family. The all-stage factorization forces the chart to be exactly the
inverse iterate of that source chart, including at stage zero. The label
capture law prevents an independent choice of a different leaf at a point.
`stage_zero` identifies the selected native source plaque with stage zero;
no arbitrary ambient set `plaque : M → Set M` remains in this interface. -/
structure NativeSourcePlaqueStages
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (inclusion : ∀ i, L i → M) (label : M → ι)
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (sourceDisc : ∀ x, Opens (Fin (r (label x)) → ℝ))
    (sourceMap : ∀ x, sourceDisc x → M) where
  label_capture : ∀ i y, label (inclusion i y) = i
  center : ∀ x, sourceDisc x
  center_zero : ∀ x, (center x : Fin (r (label x)) → ℝ) = 0
  sourceDisc_connected : ∀ x, IsConnected (sourceDisc x : Set (Fin (r (label x)) → ℝ))
  nativePlaque : ∀ x, Opens (L (label x))
  nativeChart : ∀ x, Diffeomorph 𝓘(ℝ, Fin (r (label x)) → ℝ)
    𝓘(ℝ, Fin (r (label x)) → ℝ) (sourceDisc x) (nativePlaque x) ∞
  native_factorization : ∀ x v,
    inclusion (label x) (nativeChart x v) = sourceMap x v
  centered : ∀ x, sourceMap x (center x) = x
  source_embedding : ∀ x, Manifold.IsSmoothEmbedding
    𝓘(ℝ, Fin (r (label x)) → ℝ) 𝓘(ℝ, E) ∞ (sourceMap x)
  trapped : ∀ x, f '' Set.range (sourceMap x) ⊆ Set.range (sourceMap (f x))
  stage : ∀ x, ℕ → Opens (L (label x))
  stage_zero : ∀ x, stage x 0 = nativePlaque x
  stageChart : ∀ x n, Diffeomorph
    𝓘(ℝ, Fin (r (label (((f : M → M)^[n]) x))) → ℝ)
    𝓘(ℝ, Fin (r (label x)) → ℝ)
    (sourceDisc (((f : M → M)^[n]) x)) (stage x n) ∞
  stage_factorization : ∀ x n v,
    inclusion (label x) (stageChart x n v) =
      ((f.symm : M → M)^[n]) (sourceMap (((f : M → M)^[n]) x) v)
  stage_image : ∀ x n, inclusion (label x) '' (stage x n : Set (L (label x))) =
    ((f.symm : M → M)^[n]) '' Set.range (sourceMap (((f : M → M)^[n]) x))
  increasing : ∀ x n, (stage x n : Set (L (label x))) ⊆ stage x (n + 1)
  exhaustive : ∀ x, ⋃ n, (stage x n : Set (L (label x))) = Set.univ
  stage_embedding : ∀ x n, Manifold.IsSmoothEmbedding
    𝓘(ℝ, Fin (r (label x)) → ℝ) 𝓘(ℝ, E) ∞
    (fun y : stage x n ↦ inclusion (label x) y)
  topology_generated : ∀ x (W : Set (L (label x))), IsOpen W ↔
    ∀ n, IsOpen ((Subtype.val : stage x n → L (label x)) ⁻¹' W)

/-- Source-faithful weaker alternative when only the common centred germ is
identified. Both sides are actual native open restrictions of the two disc
parameter domains. HPS self-coherence and continuation use this local
agreement; requiring equality of whole original cutoff discs would add a
stronger unprinted constraint. All source stages above still use the ONE
fixed sourceMap, while local finite-C¹ family maps may be restricted here. -/
structure SelectedFamilyGermRestriction
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (label : M → ι)
    (sourceDisc : ∀ x, Opens (Fin (r (label x)) → ℝ))
    (sourceMap : ∀ x, sourceDisc x → M)
    (sourceCenter : ∀ x, sourceDisc x)
    (d : ℕ) (U : Set M) (familyDisc : Opens (Fin d → ℝ))
    (familyMap : U × familyDisc → M) (familyCenter : familyDisc) where
  sourceInner : ∀ p : U, Opens (sourceDisc p)
  familyInner : ∀ _p : U, Opens familyDisc
  source_center_mem : ∀ p : U, sourceCenter p ∈ sourceInner p
  family_center_mem : ∀ p : U, familyCenter ∈ familyInner p
  comparison : ∀ p : U, Diffeomorph
    𝓘(ℝ, Fin (r (label (p : M))) → ℝ) 𝓘(ℝ, Fin d → ℝ)
    (sourceInner p) (familyInner p) ∞
  centered : ∀ p : U,
    ((comparison p ⟨sourceCenter p, source_center_mem p⟩ : familyInner p) : familyDisc) =
      familyCenter
  same_map : ∀ (p : U) (v : sourceInner p),
    familyMap (p, (comparison p v : familyDisc)) = sourceMap p (v : sourceDisc p)

/--
 Asymptotic identification for the supplied ambient distance function.

Source: GL8--GL9 of `g9.hps_anosov_global_lamination`. This extra output belongs only to the
distance clause. It imposes no equation between this distance and a tensor-induced distance, and
is not part of the independent tensor export.
-/
structure DistanceLeafIdentification
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (F : LeafPartition D ι L r) (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (distance : M → M → ℝ≥0∞) where
  label : M → ι
  equality : ∀ x, Set.range (F.leaf (label x)).inclusion =
    {y | Filter.Tendsto (fun n : ℕ ↦ distance
      (realIterate 𝓘(ℝ, E) f n y) (realIterate 𝓘(ℝ, E) f n x))
      Filter.atTop (nhds 0)}

/-- Source-bound original-f transported stages and asymptotic identification.

Source: HPS self-coherence and native continuation pp.111--116, expanded by
GL8--GL9 of the current node. Every stage chart is the actual inverse iterate
of one selected source chart, and every stored local finite-C¹ family agrees
with that same chart germ by an explicit centred native diffeomorphism. -/
def SourceBoundDistanceOutput
    {D : RealTangentDistribution 𝓘(ℝ, E) M}
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (F : LeafPartition D ι L r) (families : SelectedFiniteC1NativePlaqueFamilies F)
    (coherent : SelectedFiniteOrderNativePlaqueFamilies F)
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (distance : M → M → ℝ≥0∞) : Prop :=
  ∃ (label : M → ι) (sourceDisc : ∀ x, Opens (Fin (r (label x)) → ℝ))
    (sourceMap : ∀ x, sourceDisc x → M),
    ∃ stages : NativeSourcePlaqueStages (fun i ↦ (F.leaf i).inclusion)
      label f sourceDisc sourceMap,
      (∃ identification : DistanceLeafIdentification F f distance,
        identification.label = label) ∧
      (∀ p₀,
        let Φ := families.family p₀
        Nonempty (SelectedFamilyGermRestriction (L := L) label sourceDisc sourceMap stages.center
          (families.dimension p₀) Φ.family.centerDomain
          ⟨Metric.ball 0 Φ.family.radius, Metric.isOpen_ball⟩
          (fun z ↦ (Φ.family.plaque z.1).param z.2.val)
          ⟨0, Metric.mem_ball_self Φ.family.radius_pos⟩) ∧
        ∀ p : Φ.family.centerDomain, Φ.label p = label p) ∧
      ∀ N p₀,
        let Φ := coherent.family N p₀
        Nonempty (SelectedFamilyGermRestriction (L := L) label sourceDisc sourceMap stages.center
          (coherent.dimension N p₀) Φ.family.centerDomain
          ⟨Metric.ball 0 Φ.family.radius, Metric.isOpen_ball⟩
          (fun z ↦ (Φ.family.plaque z.1).param z.2.val)
          ⟨0, Metric.mem_ball_self Φ.family.radius_pos⟩) ∧
        ∀ p : Φ.family.centerDomain, Φ.label p = label p

end HolomorphicAnosov.HPS
