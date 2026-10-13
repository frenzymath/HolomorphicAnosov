import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Lemmas

noncomputable section
open Set Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.HPS
universe u
open scoped ContDiff Manifold Bundle
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ,E) ∞ M]
variable {D : RealTangentDistribution 𝓘(ℝ,E) M}
variable {ι κ : Type u} {L : ι → Type u} {K : κ → Type u} {r : ι → ℕ} {q : κ → ℕ}
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ,Fin (r i) → ℝ) ∞ (L i)]
variable [∀ k, TopologicalSpace (K k)] [∀ k, ChartedSpace (Fin (q k) → ℝ) (K k)]
variable [∀ k, IsManifold 𝓘(ℝ,Fin (q k) → ℝ) ∞ (K k)]


omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A covering family of native boxes generates the original intrinsic leaf
topologies. Each plaque map is an open embedding, and the partition law puts
any point of a covered leaf into one such plaque of that same leaf. -/
theorem native_boxes_topology_generated
    (F : LeafPartition D ι L r)
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (B : ∀ b, NativeProductBox F (d b) (T b))
    (hcover : ∀ p : M, ∃ b, p ∈ (B b).ambient)
    (i : ι) (W : Set (L i)) : IsOpen W ↔
      ∀ b t (h : (B b).label t = i),
        IsOpen ((fun v : (B b).disc ↦
          (h ▸ ((B b).chart t v).val : L i)) ⁻¹' W) := by
  constructor
  · intro hW b t h
    have hh (j : ι) (h : (B b).label t = j) (W : Set (L j)) (hW : IsOpen W) :
        IsOpen ((fun v : (B b).disc ↦ (h ▸ ((B b).chart t v).val : L j)) ⁻¹' W) := by
      subst j
      exact hW.preimage (continuous_subtype_val.comp ((B b).chart t).continuous)
    exact hh i h W hW
  · intro hW
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨b,hb⟩ := hcover ((F.leaf i).inclusion x)
    let c := (B b).box.symm ⟨(F.leaf i).inclusion x,hb⟩
    have hc : (F.leaf ((B b).label c.2)).inclusion ((B b).chart c.2 c.1) =
        (F.leaf i).inclusion x := by
      rw [← (B b).factorization,Prod.mk.eta]
      exact congrArg Subtype.val ((B b).box.apply_symm_apply _)
    have hi := F.disjoint _ _ ((B b).chart c.2 c.1).val x hc
    have hh (j : ι) (hj : (B b).label c.2 = j) (V : Set (L j))
        (hV : IsOpen ((fun v : (B b).disc ↦
          (hj ▸ ((B b).chart c.2 v).val : L j)) ⁻¹' V)) :
        IsOpen (V ∩ (fun z : L ((B b).label c.2) ↦ (hj ▸ z : L j)) ''
          ((B b).plaque c.2 : Set (L ((B b).label c.2)))) := by
      subst j
      simp only [Set.image_id']
      have ho : IsOpen ((Subtype.val : (B b).plaque c.2 → L ((B b).label c.2)) ⁻¹' V) := by
        exact (((B b).chart c.2).toHomeomorph.isOpen_preimage).mp hV
      have hout := ((B b).plaque c.2).isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ ho
      convert hout using 1
      ext z
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage, Subtype.exists,
        exists_prop]
      constructor
      · rintro ⟨hz,hzp⟩
        exact ⟨z,hzp,hz,rfl⟩
      · rintro ⟨z,hzp,hz,rfl⟩
        exact ⟨hz,hzp⟩
    have hopen := hh i hi W (hW b c.2 hi)
    apply Filter.mem_of_superset (hopen.mem_nhds ⟨hx,?_⟩) Set.inter_subset_left
    refine ⟨((B b).chart c.2 c.1).val,((B b).chart c.2 c.1).property,?_⟩
    apply (F.leaf i).injective
    have hcast (j : ι) (h : (B b).label c.2 = j) :
        (F.leaf j).inclusion (h ▸ ((B b).chart c.2 c.1).val) =
        (F.leaf ((B b).label c.2)).inclusion ((B b).chart c.2 c.1) := by
      subst j
      rfl
    exact (hcast i hi).trans hc


end HolomorphicAnosov.HPS
