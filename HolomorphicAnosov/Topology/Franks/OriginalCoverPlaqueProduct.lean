import HolomorphicAnosov.Topology.Franks.OriginalCoverGlobalProduct
import HolomorphicAnosov.Topology.Franks.CompactContinuation
import HolomorphicAnosov.Topology.Franks.ContinuationBoundary
import HolomorphicAnosov.Topology.Franks.UniformLeafDecay

namespace HolomorphicAnosov.FranksOriginalCover
open scoped _root_.Topology

/-- Affine subspace differences propagate along finite plaque chains.
Reversal negates the difference and concatenation adds differences. -/
theorem affine_image_eqvGen
    {P W : Type*} [AddCommGroup W] [Module ℝ W]
    (R : P → P → Prop) (H : P → W) (S : Submodule ℝ W)
    (hR : ∀ x y, R x y → H y - H x ∈ S)
    {x y : P} (hxy : Relation.EqvGen R x y) : H y - H x ∈ S := by
  induction hxy with
  | rel x y hxy => exact hR x y hxy
  | refl x => simpa only [sub_self] using S.zero_mem
  | symm x y _ ih => simpa only [neg_sub] using S.neg_mem ih
  | trans x y z _ _ ih ih' =>
    simpa only [sub_add_sub_cancel] using S.add_mem ih' ih

/-- Global intersections for the actual finite-plaque-chain relations.
Source: Franks (1969), Lemma 1.6, pp.121–122. Actual rectangular open embeddings
supply open saturations, paths within each generated leaf, and joint boxes.
Their affine image differences propagate along chains. Properness of H and
the complementary linear projections give compact confinement for every
parameter rectangle. The proved maximal-domain continuation and connectedness
argument then yields all-pairs intersections. Uniqueness is the independent
homoclinic splicing input; no global product or injectivity of H is assumed. -/
theorem global_product_of_native_rectangular_plaques
    {P W ι : Type*} {Us Vs : ι → Type*}
    [TopologicalSpace P] [T2Space P] [FirstCountableTopology P] [PreconnectedSpace P]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [∀ i, TopologicalSpace (Us i)] [∀ i, TopologicalSpace (Vs i)]
    [∀ i, PathConnectedSpace (Us i)] [∀ i, PathConnectedSpace (Vs i)]
    (B : ∀ i, Us i × Vs i → P)
    (hB : ∀ i, _root_.Topology.IsOpenEmbedding (B i))
    (hcover : ∀ x, ∃ i, x ∈ Set.range (B i))
    (H : P → W) (hproper : IsProperMap H)
    (S U : Submodule ℝ W) (hSU : IsCompl S U)
    (hrow : ∀ i u u' v, H (B i (u',v)) - H (B i (u,v)) ∈ S)
    (hcol : ∀ i u v v', H (B i (u,v')) - H (B i (u,v)) ∈ U)
    (hunique : ∀ a b z z',
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) a z →
      Relation.EqvGen (rectangularPlaqueRel B) b z →
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) a z' →
      Relation.EqvGen (rectangularPlaqueRel B) b z' → z = z') :
    ∀ a b, ∃ p,
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) a p ∧
      Relation.EqvGen (rectangularPlaqueRel B) b p := by
  let C : ∀ i, Vs i × Us i → P := fun i w ↦ B i (w.2,w.1)
  let Lu := Relation.EqvGen.setoid (rectangularPlaqueRel C)
  let Ls := Relation.EqvGen.setoid (rectangularPlaqueRel B)
  have hC (i) : _root_.Topology.IsOpenEmbedding (C i) :=
    (hB i).comp (Homeomorph.prodComm (Vs i) (Us i)).isOpenEmbedding
  have hu (x y) (hxy : Lu x y) : H y - H x ∈ U := by
    apply affine_image_eqvGen (rectangularPlaqueRel C) H U ?_ hxy
    rintro a b ⟨i,v,v',u,rfl,rfl⟩
    exact hcol i u v v'
  have hs (x y) (hxy : Ls x y) : H y - H x ∈ S := by
    apply affine_image_eqvGen (rectangularPlaqueRel B) H S ?_ hxy
    rintro a b ⟨i,u,u',v,rfl,rfl⟩
    exact hrow i u u' v
  apply global_intersection_of_rectangular_box_cover Lu Ls hunique ?_ ?_
    (fun x ↦ rectangularPlaque_joint_box B hB x (hcover x)) ?_ ?_ ?_
  · intro O hO
    convert isOpen_rectangularPlaque_saturation C (fun i ↦ (hC i).continuous)
      (fun i ↦ (hC i).isOpenMap) O hO using 1
    ext x
    exact exists_congr fun y ↦ and_congr_right fun _ ↦ ⟨Lu.symm,Lu.symm⟩
  · intro O hO
    convert isOpen_rectangularPlaque_saturation B (fun i ↦ (hB i).continuous)
      (fun i ↦ (hB i).isOpenMap) O hO using 1
    ext x
    exact exists_congr fun y ↦ and_congr_right fun _ ↦ ⟨Ls.symm,Ls.symm⟩
  · exact fun x y hxy ↦ rectangularPlaque_path_in_class C (fun i ↦ (hC i).continuous) hxy
  · exact fun x y hxy ↦ rectangularPlaque_path_in_class B (fun i ↦ (hB i).continuous) hxy
  · exact fun γ ρ hγ hρ ↦ compact_intersections_of_complementary_affine_images
      Lu Ls H hproper S U hSU hu hs γ ρ hγ hρ

/-- Uniform decay along rows gives locally uniform decay for all generated
same-leaf pairs near a generating pair or a diagonal pair. Source: the local
one-plaque consequence of global intersection uniqueness in Franks (1969),
Lemma 1.6 and §1.8. Two same-leaf points in one product box have the same row
label: crossing their coordinates supplies a second intersection otherwise.
The box range is open, so the row estimate holds on a whole pair neighborhood. -/
theorem rectangularPlaque_local_uniform_generators
    {P ι : Type*} {Us Vs : ι → Type*} [TopologicalSpace P]
    [∀ i, TopologicalSpace (Us i)] [∀ i, TopologicalSpace (Vs i)]
    (B : ∀ i, Us i × Vs i → P)
    (hB : ∀ i, _root_.Topology.IsOpenEmbedding (B i))
    (hcover : ∀ x, ∃ i, x ∈ Set.range (B i))
    (d : ℕ → P → P → ℝ)
    (hrow : ∀ i ε, 0 < ε → ∃ N : ℕ, ∀ u u' v, ∀ n ≥ N,
      d n (B i (u,v)) (B i (u',v)) < ε)
    (hunique : ∀ a b z z',
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) a z →
      Relation.EqvGen (rectangularPlaqueRel B) b z →
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) a z' →
      Relation.EqvGen (rectangularPlaqueRel B) b z' → z = z') :
    (∀ x ε, 0 < ε → ∃ N : ℕ, ∀ᶠ z : P × P in 𝓝 (x,x),
      Relation.EqvGen (rectangularPlaqueRel B) z.1 z.2 →
        ∀ n ≥ N, d n z.1 z.2 < ε) ∧
    (∀ x y, rectangularPlaqueRel B x y → ∀ ε, 0 < ε →
      ∃ N : ℕ, ∀ᶠ z : P × P in 𝓝 (x,y),
      Relation.EqvGen (rectangularPlaqueRel B) z.1 z.2 →
        ∀ n ≥ N, d n z.1 z.2 < ε) := by
  have hlocal (i : ι) (x y : P) (hx : x ∈ Set.range (B i))
      (hy : y ∈ Set.range (B i)) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ᶠ z : P × P in 𝓝 (x,y),
        Relation.EqvGen (rectangularPlaqueRel B) z.1 z.2 →
          ∀ n ≥ N, d n z.1 z.2 < ε := by
    obtain ⟨N,hN⟩ := hrow i ε hε
    refine ⟨N, ?_⟩
    have hleft : ∀ᶠ z : P × P in 𝓝 (x,y), z.1 ∈ Set.range (B i) :=
      continuous_fst.tendsto (x,y) ((hB i).isOpen_range.mem_nhds hx)
    have hright : ∀ᶠ z : P × P in 𝓝 (x,y), z.2 ∈ Set.range (B i) :=
      continuous_snd.tendsto (x,y) ((hB i).isOpen_range.mem_nhds hy)
    filter_upwards [hleft,hright] with z hz₁ hz₂ hrel n hn
    obtain ⟨a,ha⟩ := hz₁
    obtain ⟨b,hb⟩ := hz₂
    have hcross : B i (b.1,a.2) = B i b := by
      apply hunique (B i b) (B i a) (B i (b.1,a.2)) (B i b)
      · exact Relation.EqvGen.rel _ _ ⟨i,b.2,a.2,b.1,rfl,rfl⟩
      · exact Relation.EqvGen.rel _ _ ⟨i,a.1,b.1,a.2,rfl,rfl⟩
      · exact Relation.EqvGen.refl _
      · simpa only [ha,hb] using hrel
    have hpair : (b.1,a.2) = b := (hB i).injective hcross
    have hlabel := congrArg (fun w : Us i × Vs i ↦ w.2) hpair
    change a.2 = b.2 at hlabel
    rw [← ha,← hb,show b = (b.1,a.2) by rw [hlabel]]
    exact hN a.1 b.1 a.2 n hn
  constructor
  · intro x ε hε
    obtain ⟨i,hx⟩ := hcover x
    exact hlocal i x x hx hx ε hε
  · rintro x y ⟨i,u,u',v,rfl,rfl⟩ ε hε
    exact hlocal i _ _ (Set.mem_range_self _) (Set.mem_range_self _) ε hε

/-- The actual rectangular family gives a continuous global crossing and
closed row/column relations after global intersections have been proved.
The same open saturation and box calculations as in global continuation apply;
uniqueness identifies each relation with an equality locus of the crossing. -/
theorem continuous_rectangularPlaque_product
    {P ι : Type*} {Us Vs : ι → Type*} [TopologicalSpace P] [T2Space P]
    [∀ i, TopologicalSpace (Us i)] [∀ i, TopologicalSpace (Vs i)]
    (B : ∀ i, Us i × Vs i → P)
    (hB : ∀ i, _root_.Topology.IsOpenEmbedding (B i))
    (hcover : ∀ x, ∃ i, x ∈ Set.range (B i))
    (hunique : ∀ a b z z',
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) a z →
      Relation.EqvGen (rectangularPlaqueRel B) b z →
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) a z' →
      Relation.EqvGen (rectangularPlaqueRel B) b z' → z = z')
    (hproduct : ∀ a b, ∃ p,
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) a p ∧
      Relation.EqvGen (rectangularPlaqueRel B) b p) :
    (∃ J : C(P × P,P), ∀ a b,
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) a (J (a,b)) ∧
      Relation.EqvGen (rectangularPlaqueRel B) b (J (a,b))) ∧
    IsClosed {z : P × P |
      Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1))) z.1 z.2} ∧
    IsClosed {z : P × P | Relation.EqvGen (rectangularPlaqueRel B) z.1 z.2} := by
  let C : ∀ i, Vs i × Us i → P := fun i w ↦ B i (w.2,w.1)
  let Lu := Relation.EqvGen.setoid (rectangularPlaqueRel C)
  let Ls := Relation.EqvGen.setoid (rectangularPlaqueRel B)
  have hC (i) : _root_.Topology.IsOpenEmbedding (C i) :=
    (hB i).comp (Homeomorph.prodComm (Vs i) (Us i)).isOpenEmbedding
  apply continuous_global_intersection_and_closed_relations Lu Ls hunique ?_ ?_
    (fun x ↦ rectangularPlaque_joint_box B hB x (hcover x)) hproduct
  · intro O hO
    convert isOpen_rectangularPlaque_saturation C (fun i ↦ (hC i).continuous)
      (fun i ↦ (hC i).isOpenMap) O hO using 1
    ext x
    exact exists_congr fun y ↦ and_congr_right fun _ ↦ ⟨Lu.symm,Lu.symm⟩
  · intro O hO
    convert isOpen_rectangularPlaque_saturation B (fun i ↦ (hB i).continuous)
      (fun i ↦ (hB i).isOpenMap) O hO using 1
    ext x
    exact exists_congr fun y ↦ and_congr_right fun _ ↦ ⟨Ls.symm,Ls.symm⟩

end HolomorphicAnosov.FranksOriginalCover
