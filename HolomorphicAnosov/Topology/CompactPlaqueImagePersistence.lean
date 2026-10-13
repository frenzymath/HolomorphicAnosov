import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Compact plaque image persistence

Source: HPS, Invariant Manifolds, §7 pp.115–116. The agent-written compact
boundary and immersion arguments below supply the native plaque compatibility
steps in the direct proof of Ghys Proposition 4.1.
-/ 

open Set Filter _root_.Topology
open scoped Topology
namespace HolomorphicAnosov

/-- A compact plaque image continues to cover a fixed connected receiving
core under a continuous parameter change, provided the plaque interior maps
openly, the boundary avoids that core, and one interior point lands inside it.

The compact boundary stays outside the closed receiving core for all nearby
parameters by the tube lemma. The marked point remains in the core by
continuity. At each such parameter the compact whole-plaque image is closed,
the interior image is open, and their intersections with the core coincide
because the boundary is excluded. A nonempty subset of a connected core that
is both open and closed is the entire core. No differentiability in the
transverse parameter or uniform inverse-function theorem is assumed.

Source: agent-written source-core construction in the Markov-free proof of
Ghys Proposition 4.1, using the HPS finite C1 native plaques and their open
intrinsic receiving branches, HPS §7 pp.115–116. -/
theorem compact_plaque_image_persists
    {X T Y : Type*} [TopologicalSpace X] [TopologicalSpace T]
    [TopologicalSpace Y] [T2Space Y]
    (K O : Set X) (hK : IsCompact K) (hO : IsOpen O) (hOK : O ⊆ K)
    (H : X × T → Y) (hH : Continuous H)
    (hopen : ∀ t, IsOpen ((fun x ↦ H (x,t)) '' O))
    (B : Set Y) (hB : IsClosed B) (hconn : IsPreconnected B)
    (t₀ : T) (x₀ : X) (hx₀ : x₀ ∈ O) (hcenter : H (x₀,t₀) ∈ interior B)
    (hboundary : ∀ x ∈ K \ O, H (x,t₀) ∉ B) :
    ∀ᶠ t in 𝓝 t₀, B ⊆ (fun x ↦ H (x,t)) '' O := by
  obtain ⟨U,V,_,hV,hKU,htV,hUV⟩ :=
    generalized_tube_lemma (hK.inter_right hO.isClosed_compl) isCompact_singleton
      (hB.isOpen_compl.preimage hH) (by
        rintro ⟨x,t⟩ ⟨hx,ht⟩
        rcases Set.mem_singleton_iff.mp ht with rfl
        exact hboundary x hx)
  have hc : Continuous (fun t ↦ H (x₀,t)) :=
    hH.comp (continuous_const.prodMk continuous_id)
  filter_upwards [hV.mem_nhds (htV (mem_singleton t₀)),
    hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hcenter)] with t ht hct
  let F : X → Y := fun x ↦ H (x,t)
  have hF : Continuous F := hH.comp (continuous_id.prodMk continuous_const)
  have hclosed : IsClosed (F '' K) := (hK.image hF).isClosed
  have hbdy : ∀ x ∈ K \ O, F x ∉ B := fun x hx ↦ hUV ⟨hKU hx,ht⟩
  apply hconn.subset_of_closure_inter_subset (hopen t)
  · exact ⟨F x₀, interior_subset hct, x₀,hx₀,rfl⟩
  · intro y hy
    have hyK : y ∈ F '' K :=
      closure_minimal (image_mono hOK) hclosed hy.1
    obtain ⟨x,hx,rfl⟩ := hyK
    refine ⟨x,?_,rfl⟩
    by_contra hxo
    exact hbdy x ⟨hx,hxo⟩ hy.2


/-- A continuous family of open plaque images covers one fixed receiving ball
for all nearby parameters. Choose that ball inside the central interior image;
central injectivity excludes the compact source boundary. The preceding tube
and connectedness argument then gives one neighborhood valid on the whole ball.
This works also for a zero-dimensional receiving vector space. -/
theorem compact_plaque_family_covers_ball
    {X T Y : Type*} [TopologicalSpace X] [TopologicalSpace T]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (K O : Set X) (hK : IsCompact K) (hO : IsOpen O) (hOK : O ⊆ K)
    (H : X × T → Y) (hH : Continuous H)
    (hopen : ∀ t, IsOpen ((fun x ↦ H (x,t)) '' O))
    (t₀ : T) (hinj : InjOn (fun x ↦ H (x,t₀)) K)
    (x₀ : X) (hx₀ : x₀ ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ t in 𝓝 t₀,
      Metric.closedBall (H (x₀,t₀)) ε ⊆ (fun x ↦ H (x,t)) '' O := by
  obtain ⟨ε,hε,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hopen t₀).mem_nhds ⟨x₀,hx₀,rfl⟩)
  refine ⟨ε,hε,compact_plaque_image_persists K O hK hO hOK H hH hopen
    (Metric.closedBall (H (x₀,t₀)) ε) Metric.isClosed_closedBall
    (convex_closedBall _ _).isPreconnected t₀ x₀ hx₀ ?_ ?_⟩
  · exact mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ hε)
  · intro x hx hmem
    obtain ⟨y,hy,heq⟩ := hsub hmem
    exact hx.2 ((hinj (hOK hy) hx.1 heq) ▸ hy)


/-- A jointly continuous family of open embeddings with locally compact source
is an open embedding after retaining its parameter coordinate. Compact source
cores and the preceding fixed-ball coverage prove openness of the total map;
no transverse derivative is assumed. This supplies the local product property
of the source plaque family used for the finite cover.
Source: the compact boundary/tube proof above, applied at each source point. -/
theorem continuous_family_open_embedding_prod
    {X T Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [TopologicalSpace T] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (H : X × T → Y) (hH : Continuous H)
    (hemb : ∀ t, IsOpenEmbedding (fun x ↦ H (x,t))) :
    IsOpenEmbedding (fun p : X × T ↦ (H p,p.2)) := by
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨hH.prodMk continuous_snd, ?_, ?_⟩
  · rintro ⟨x,t⟩ ⟨x',t'⟩ h
    have ht : t = t' := congrArg Prod.snd h
    subst t'
    exact Prod.ext ((hemb t).injective (congrArg Prod.fst h)) rfl
  · intro W hW
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨⟨x,t⟩,hxt,rfl⟩
    obtain ⟨U,V,hU,hx,hV,ht,hUV⟩ := mem_nhds_prod_iff'.mp (hW.mem_nhds hxt)
    obtain ⟨K,hK,hxK,hKU⟩ := exists_compact_subset hU hx
    obtain ⟨ε,hε,hevent⟩ := compact_plaque_family_covers_ball K (interior K)
      hK isOpen_interior interior_subset H hH
      (fun t ↦ (hemb t).isOpenMap _ isOpen_interior) t
      (hemb t).injective.injOn x hxK
    apply Filter.mem_of_superset
      (show Metric.closedBall (H (x,t)) ε ×ˢ
          (V ∩ {t' | Metric.closedBall (H (x,t)) ε ⊆
            (fun x ↦ H (x,t')) '' interior K}) ∈ 𝓝 (H (x,t),t) from
        mem_nhds_prod_iff.mpr ⟨_,Metric.closedBall_mem_nhds _ hε,_,
          inter_mem (hV.mem_nhds ht) hevent,subset_rfl⟩)
    rintro ⟨y,t'⟩ ⟨hy,htV,hcover⟩
    obtain ⟨x',hx',heq⟩ := hcover hy
    exact ⟨(x',t'),hUV ⟨hKU (interior_subset hx'),htV⟩,Prod.ext heq rfl⟩

end HolomorphicAnosov
