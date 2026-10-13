import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Select the leaf through each point from a native lamination and transport it.

Source context: HPS (1977), §6B pp.111–114 and §7 pp.127–129.
This Lean interface conversion is an agent-written expansion: choose a label
and a point from the covering partition. Disjointness identifies the labels
for transport and rebasing. Transport uses the given dynamical diffeomorphism;
rebasing uses the identity on the selected leaf after substituting label equality.
The local auxiliary equalities concern only these chosen representatives.
-/
noncomputable def nativeInvariantLeafSystemOfPartition
    {ι : Type v} {L : ι → Type v} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (F : HPS.LeafPartition D ι L r) (dyn : HPS.LeafDynamicalInvariance F g) :
    NativeInvariantLeafSystem 𝓘(ℝ, E) D g := by
  classical
  let top : ∀ i, TopologicalSpace (L i) := inferInstance
  let charts : ∀ i, ChartedSpace (Fin (r i) → ℝ) (L i) := inferInstance
  let smooth : ∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i) := inferInstance
  choose label point hpoint using F.cover
  let leaf (p : M) : NativeSmoothLeaf 𝓘(ℝ, E) D p :=
    { rank := r (label p)
      Carrier := L (label p)
      topology := top (label p)
      hausdorff := (F.leaf (label p)).hausdorff
      secondCountable := (F.leaf (label p)).countable
      connected := (F.leaf (label p)).connected
      charted := charts (label p)
      smoothManifold := smooth (label p)
      point := point p
      inclusion := (F.leaf (label p)).inclusion
      inclusion_point := hpoint p
      inclusion_smooth := (F.leaf (label p)).immersion.contMDiff
      inclusion_injective := (F.leaf (label p)).injective
      inclusion_immersed := (F.leaf (label p)).immersion.mfderiv_injective (by simp)
      inclusion_tangent := (F.leaf (label p)).tangent }
  have hadvance (p : M) : ∃ a : Diffeomorph 𝓘(ℝ, Fin (leaf p).rank → ℝ)
      𝓘(ℝ, Fin (leaf (g p)).rank → ℝ) (leaf p).Carrier (leaf (g p)).Carrier ∞,
      ∀ y, (leaf (g p)).inclusion (a y) = g ((leaf p).inclusion y) := by
    have hlabel : dyn.permutation (label p) = label (g p) :=
      F.disjoint _ _ (dyn.transport (label p) (point p)) (point (g p)) (by
        rw [dyn.intertwining, hpoint, hpoint])
    change ∃ a : Diffeomorph 𝓘(ℝ, Fin (r (label p)) → ℝ)
        𝓘(ℝ, Fin (r (label (g p))) → ℝ) (L (label p)) (L (label (g p))) ∞,
      ∀ y, (F.leaf (label (g p))).inclusion (a y) = g ((F.leaf (label p)).inclusion y)
    rw [← hlabel]
    exact ⟨dyn.transport (label p), dyn.intertwining (label p)⟩
  have hrebase (p : M) (y : (leaf p).Carrier) :
      ∃ a : Diffeomorph 𝓘(ℝ, Fin (leaf p).rank → ℝ)
        𝓘(ℝ, Fin (leaf ((leaf p).inclusion y)).rank → ℝ)
        (leaf p).Carrier (leaf ((leaf p).inclusion y)).Carrier ∞,
        ∀ z, (leaf ((leaf p).inclusion y)).inclusion (a z) = (leaf p).inclusion z := by
    have hlabel : label p = label ((F.leaf (label p)).inclusion y) :=
      F.disjoint _ _ y (point ((F.leaf (label p)).inclusion y)) (hpoint _).symm
    change ∃ a : Diffeomorph 𝓘(ℝ, Fin (r (label p)) → ℝ)
        𝓘(ℝ, Fin (r (label ((F.leaf (label p)).inclusion y))) → ℝ)
        (L (label p)) (L (label ((F.leaf (label p)).inclusion y))) ∞,
      ∀ z, (F.leaf (label ((F.leaf (label p)).inclusion y))).inclusion (a z) =
        (F.leaf (label p)).inclusion z
    rw [← hlabel]
    exact ⟨Diffeomorph.refl _ _ ∞, fun _ ↦ rfl⟩
  choose advance inclusion_advance using hadvance
  choose rebase inclusion_rebase using hrebase
  exact { leaf := leaf
          advance := advance
          inclusion_advance := inclusion_advance
          rebase := rebase
          inclusion_rebase := inclusion_rebase }

theorem nativeInvariantLeafSystem_of_hasNativeLamination (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hLam : HPS.HasNativeLamination D g (fun _ _ _ ↦ True)) :
    Nonempty (NativeInvariantLeafSystem 𝓘(ℝ, E) D g) := by
  obtain ⟨ι, L, r, top, charts, smooth, F, boxes, ⟨dyn⟩, families, coherent, _⟩ := hLam
  let := top
  let := charts
  let := smooth
  exact ⟨nativeInvariantLeafSystemOfPartition D g F dyn⟩

section CarrierEquations
variable {ι : Type v} {L : ι → Type v} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (F : HPS.LeafPartition D ι L r) (dyn : HPS.LeafDynamicalInvariance F g)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem nativeInvariantLeafSystemOfPartition_carrier (p : M) :
    ((nativeInvariantLeafSystemOfPartition D g F dyn).leaf p).Carrier =
      L (Classical.choose (F.cover p)) := rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem nativeInvariantLeafSystemOfPartition_rank (p : M) :
    ((nativeInvariantLeafSystemOfPartition D g F dyn).leaf p).rank =
      r (Classical.choose (F.cover p)) := rfl
end CarrierEquations

end HolomorphicAnosov
