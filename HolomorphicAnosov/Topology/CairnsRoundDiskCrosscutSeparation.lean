import HolomorphicAnosov.Topology.RoundDiskComponentBoundaryContactG9
import HolomorphicAnosov.Topology.CircleChordSignsG9
import HolomorphicAnosov.Topology.SimpleArcNonseparation
import HolomorphicAnosov.Topology.TwoArcsCircleEmbedding
import HolomorphicAnosov.Topology.RoundDiskCrosscutGeometry
import HolomorphicAnosov.Topology.CairnsBoundedComponentDiskExtension
import HolomorphicAnosov.Topology.CairnsRoundDiskCrosscutOppositeSide
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Separation of the round disk by an arbitrary embedded crosscut

Source: S. S. Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
Lemma 5.1 and its polygonal-path contradiction, printed p.866, after reduction by Theorem 4.1;
disk-cell amalgamation §4(D), printed pp.865–866.
DAG node: `topo.cairns_round_disk_crosscut_separation`.

All sets below are literal subsets of the original complex plane. In particular, the two
closed circle arcs are the intersections of the unit circle with the two closed half-planes
bounded by the chord of the distinct endpoints. This description includes antipodal endpoints.
The crosscut itself is only a topological embedding of Mathlib's `unitInterval` in the closed
unit disk; no piecewise linearity, smoothness, or local connectedness premise is imposed.
-/

open Set Metric
open scoped ComplexConjugate

namespace HolomorphicAnosov

/-- An embedded crosscut of the round disk separates it into exactly two nonempty connected
components. Their frontiers are the full crosscut together with the two respective circle arcs,
their closures are closed disks meeting exactly in the full crosscut, and every prescribed
homeomorphism of either cut boundary to the circle extends over the corresponding closed disk.

Source: Cairns (1951), Lemma 5.1, printed p.866, and Theorem 4.1 with its disk-cell amalgamation
corollary §4(D), printed pp.865–866. The two signs of the endpoint-chord determinant merely
index the two genuine closed circle arcs in the source. `connectedComponentIn` is Mathlib's
actual connected-component construction: its full image on the complement is exactly the two
returned sets. All frontiers and closures use the ambient plane topology. Each returned disk
homeomorphism identifies the component with the open disk and its frontier with the circle.
The final universal quantifier retains arbitrary prescribed boundary values, rather than
selecting a convenient boundary map. Local accessibility or prior Jordan separation is not a
hypothesis. No source claim of transitive proof completion is inferred from this statement.

Complete natural-language proof (agent-written assembly of the cited sources):

1. The crosscut image K is compact, is contained in the closed disk, and meets
its circle only at its two endpoints. Removing the full image or just the open
crosscut from the open disk therefore gives the same open set Ω. Transport
Whyburn's independent simple-arc nonseparation theorem (III(1.1), pp.29–30) from
the real Euclidean plane to ℂ: the plane complement of K is connected. This
source theorem uses polygon separation, not arbitrary Jordan separation.

2. Parametrize the two circle arcs by the signed chord half-planes. The chord
line meets the circle only at its endpoints: writing z=u+t(v-u), equality of
squared norms gives t(t-1)‖v-u‖²=0. Both determinant signs occur, as witnessed
by the two unit normals to the chord. The determinant is continuous and nonzero
on each open circle arc, so has constant sign there. The ordinary two-arc split
of Circle, reindexed by sign, gives the stated closed arcs even for antipodal
endpoints. Their open arcs are nonempty and connected and cover the circle
minus the endpoint pair.

3. Every component of Ω accumulates at a circle point outside K. Otherwise
its frontier would lie in K, making it relatively closed as well as open in
the connected plane complement of K. It would equal that complement, which
is impossible since Ω is bounded and K lies in the unit disk. At each circle
point outside K a small inward convex cap lies in a unique Ω component.
The incident component is constant along each connected open circle arc.
Consequently all components are the two collar components. The existing
Cairns polygon-crossing contradiction gives two distinct Ω components, so
these two collar components are distinct, disjoint, and exhaust Ω. Uniqueness
of the incident component puts the frontier of component i inside K∪A_i.

4. Concatenating the embedded crosscut and the embedded arc A_i gives an
embedded circle with image C_i=K∪A_i: the interior crosscut misses the circle,
so the two arcs meet only at their endpoints. Component V_i is open, connected,
bounded and disjoint from C_i. Its frontier lies in C_i, so it is relatively
closed in C_i's complement; component maximality identifies it with a full
plane complementary component of C_i. Apply Cairns's provisional bounded-
component disk-extension theorem to this supplied component. It gives the
full frontier equality, closure(V_i)=V_i∪C_i, and extension of every prescribed
homeomorphism C_i→Circle, mapping V_i exactly to the open disk.

5. The exact two-component cover gives the displayed connected-component
image. Disjointness of the components and avoidance of the circle show that
their closures can meet only in C_0∩C_1=K; both contain K by the frontier
equalities. The supplied disk extensions preserve the boundary as well as
the interior, since the boundary and interior partition each closed disk.
Subtype transport retains the literal prescribed boundary values.

This closes this module's proof using the named source prerequisites. The
axioms of the full theorem still reflect any unproved source prerequisites;
no claim of transitive Jordan–Schoenflies completion is made.
-/
theorem cairns_round_disk_crosscut_separation
    (g : unitInterval → closedBall (0 : ℂ) 1) (hg : Topology.IsEmbedding g)
    (h0 : (g 0 : ℂ) ∈ sphere (0 : ℂ) 1)
    (h1 : (g 1 : ℂ) ∈ sphere (0 : ℂ) 1) (h01 : g 0 ≠ g 1)
    (hinterior : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      (g t : ℂ) ∈ ball (0 : ℂ) 1) :
    let γ : unitInterval → ℂ := fun t ↦ (g t : ℂ)
    let K : Set ℂ := range γ
    let Kopen : Set ℂ := γ '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
    let Ω : Set ℂ := ball (0 : ℂ) 1 \ Kopen
    let A : Fin 2 → Set ℂ := fun i ↦
      {z | z ∈ sphere (0 : ℂ) 1 ∧
        if i = 0 then (conj (γ 1 - γ 0) * (z - γ 0)).im ≤ 0
        else 0 ≤ (conj (γ 1 - γ 0) * (z - γ 0)).im}
    ∃ V : Fin 2 → Set ℂ,
      (∀ i, (V i).Nonempty ∧ IsConnected (V i) ∧ IsOpen (V i)) ∧
      Disjoint (V 0) (V 1) ∧ (⋃ i, V i) = Ω ∧
      (fun z : ℂ ↦ connectedComponentIn Ω z) '' Ω = range V ∧
      (∀ i, frontier (V i) = K ∪ A i) ∧
      closure (V 0) ∩ closure (V 1) = K ∧
      (∀ i, ∃ H : closure (V i) ≃ₜ closedBall (0 : ℂ) 1,
        (∀ z : closure (V i), (z : ℂ) ∈ V i ↔ (H z : ℂ) ∈ ball (0 : ℂ) 1) ∧
        (∀ z : closure (V i),
          (z : ℂ) ∈ K ∪ A i ↔ (H z : ℂ) ∈ sphere (0 : ℂ) 1)) ∧
      (∀ i (b : {z : ℂ // z ∈ K ∪ A i} ≃ₜ sphere (0 : ℂ) 1),
        ∃ H : closure (V i) ≃ₜ closedBall (0 : ℂ) 1,
          (∀ z : closure (V i), (z : ℂ) ∈ V i ↔ (H z : ℂ) ∈ ball (0 : ℂ) 1) ∧
          (∀ z : {z : ℂ // z ∈ K ∪ A i}, ∃ hz : (z : ℂ) ∈ closure (V i),
            (H ⟨(z : ℂ), hz⟩ : ℂ) = (b z : ℂ))) := by
  classical
  dsimp only
  let γ : unitInterval → ℂ := fun t ↦ (g t : ℂ)
  let K : Set ℂ := range γ
  let A : Fin 2 → Set ℂ := fun i ↦ {z | z ∈ sphere (0 : ℂ) 1 ∧
    if i = 0 then (conj (γ 1-γ 0)*(z-γ 0)).im ≤ 0
    else 0 ≤ (conj (γ 1-γ 0)*(z-γ 0)).im}
  have hγ : Topology.IsEmbedding γ := Topology.IsEmbedding.subtypeVal.comp hg
  have huv : γ 0 ≠ γ 1 := fun h ↦ h01 (Subtype.ext h)
  obtain ⟨hKcompact, _, hcontacts, _, hdiff, _, _⟩ :=
    roundDiskCrosscutGeometry γ hγ.continuous h0 h1 hinterior
  have hKsub : K ⊆ closedBall (0 : ℂ) 1 := by
    rintro z ⟨t,rfl⟩
    exact (g t).property
  let E : EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).toHomeomorph.trans
      ((Homeomorph.piFinTwo (fun _ : Fin 2 ↦ ℝ)).trans
        Complex.equivRealProdCLM.toHomeomorph.symm)
  have hKconn : IsPreconnected Kᶜ := by
    have hc := simpleArc_compl_isConnected (E.symm ∘ γ) (E.symm.isEmbedding.comp hγ)
    have heq : E '' (range (E.symm ∘ γ))ᶜ = Kᶜ := by
      rw [E.image_compl, range_comp, Set.image_image]
      simp only [Homeomorph.apply_symm_apply]
      change (id '' range γ)ᶜ = (range γ)ᶜ
      rw [Set.image_id]
    exact heq ▸ (hc.image E E.continuous.continuousOn).isPreconnected
  have hout : ∃ z ∉ closedBall (0 : ℂ) 1, z ∉ K := by
    have ht : (2 : ℂ) ∉ closedBall (0 : ℂ) 1 := by norm_num [mem_closedBall]
    exact ⟨2, ht, fun h ↦ ht (hKsub h)⟩
  obtain ⟨b, hb, hend, hrange⟩ := circle_chord_signed_arcs h0 h1 huv
  have hAs (i) : A i ⊆ sphere (0 : ℂ) 1 := fun _ hz ↦ hz.1
  have hAr (i) : range (b i) = A i := hrange i
  let B : Fin 2 → Set ℂ := fun i ↦ A i \ {γ 0,γ 1}
  have hB (i) : IsConnected (B i) := by
    have heq : B i = b i '' Ioo 0 1 := by
      rw [show B i = range (b i) \ {γ 0,γ 1} by rw [hAr]]
      exact Topology.cairns_embedded_seam_relative_interior _ _ _ _ (hb i) rfl
        (hend i).1 (hend i).2
    rw [heq]
    exact (isConnected_Ioo (show (0 : unitInterval) < 1 by norm_num)).image
      _ (hb i).continuous.continuousOn
  have hBs (i) : B i ⊆ sphere (0 : ℂ) 1 \ K := by
    intro z hz
    refine ⟨hAs i hz.1, ?_⟩
    intro hzK
    exact hz.2 (hcontacts ▸ ⟨hzK,hAs i hz.1⟩)
  have hAcov : (⋃ i, A i) = sphere (0 : ℂ) 1 := by
    ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact hi.1
    · intro hz
      rcases le_total (conj (γ 1-γ 0)*(z-γ 0)).im 0 with h | h
      · exact ⟨0, hz, by simpa [A] using h⟩
      · exact ⟨1, hz, by simpa [A] using h⟩
  have hBcov : (⋃ i, B i) = sphere (0 : ℂ) 1 \ K := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      exact hBs i hi
    · intro hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hAcov.symm ▸ hz.1)
      refine mem_iUnion.mpr ⟨i, hi, ?_⟩
      rintro (rfl | rfl) <;> exact hz.2 (mem_range_self _)
  have hdisc : ∃ x y, x ∈ ball (0 : ℂ) 1 \ K ∧ y ∈ ball (0 : ℂ) 1 \ K ∧
      connectedComponentIn (ball (0 : ℂ) 1 \ K) x ≠
      connectedComponentIn (ball (0 : ℂ) 1 \ K) y := by
    change ∃ x y, x ∈ ball (0 : ℂ) 1 \ range γ ∧ y ∈ ball (0 : ℂ) 1 \ range γ ∧ _
    rw [← hdiff]
    exact cairns_round_disk_crosscut_opposite_side_provider g hg h0 h1 h01 hinterior
  obtain ⟨V,hV,hdis,hcov,hclass,hfront,hBcl⟩ :=
    roundDisk_components_of_two_boundary_arcs hKcompact.isClosed hKconn hout
      B hB hBs hBcov hdisc
  have hVs (i) : V i ⊆ ball (0 : ℂ) 1 \ K := by
    intro z hz
    rw [← hcov]
    exact mem_iUnion.mpr ⟨i,hz⟩
  have hcircle (i) : ∃ j : Circle → ℂ, Topology.IsEmbedding j ∧ range j = K ∪ A i := by
    apply Exists.imp (fun j hj ↦ ⟨hj.1, hj.2.trans (by rw [hAr])⟩)
      (twoArcs_circle_embedding γ (b i) hγ.continuous (hb i).continuous
        hγ.injective (hb i).injective (hend i).1.symm (hend i).2.symm ?_)
    intro s t heq
    have hγS : γ s ∈ sphere (0 : ℂ) 1 := heq ▸ hAs i (hAr i ▸ mem_range_self t)
    have hs : γ s ∈ ({γ 0,γ 1} : Set ℂ) := hcontacts ▸ ⟨mem_range_self s,hγS⟩
    rcases hs with hs | hs
    · exact Or.inl ⟨hγ.injective hs, (hb i).injective (heq.symm.trans (hs.trans (hend i).1.symm))⟩
    · exact Or.inr ⟨hγ.injective hs, (hb i).injective (heq.symm.trans (hs.trans (hend i).2.symm))⟩
  have hfrontsub (i) : frontier (V i) ⊆ K ∪ A i :=
    (hfront i).trans (union_subset_union Subset.rfl sdiff_subset)
  have havoid (i) : V i ⊆ (K ∪ A i)ᶜ := by
    intro z hz
    rintro (hzK | hzA)
    · exact (hVs i hz).2 hzK
    · exact disjoint_left.mp sphere_disjoint_ball (hAs i hzA) (hVs i hz).1
  have hcomp (i) : ∃ x, V i = connectedComponentIn (K ∪ A i)ᶜ x := by
    obtain ⟨x,hx⟩ := (hV i).1
    refine ⟨x, Subset.antisymm
      ((hV i).2.1.isPreconnected.subset_connectedComponentIn hx (havoid i)) ?_⟩
    apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      (hV i).2.2 ⟨x,mem_connectedComponentIn (havoid i hx),hx⟩
    rintro z ⟨hzcl,hzc⟩
    by_contra hz
    exact connectedComponentIn_subset _ _ hzc
      (hfrontsub i ((hV i).2.2.frontier_eq.symm ▸ ⟨hzcl,hz⟩))
  have hbdd (i) : Bornology.IsBounded (V i) :=
    (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 1)).subset ((hVs i).trans sdiff_subset)
  have hext (i) (e : ↥(K ∪ A i) ≃ₜ Circle) :
      frontier (V i) = K ∪ A i ∧ closure (V i) = V i ∪ (K ∪ A i) ∧
      ∃ F : closure (V i) ≃ₜ closedBall (0 : ℂ) 1,
        (∀ z : closure (V i), ∀ hz : (z : ℂ) ∈ K ∪ A i,
          (F z : ℂ) = (e ⟨z,hz⟩ : ℂ)) ∧
        (∀ z : closure (V i), (z : ℂ) ∈ V i ↔ (F z : ℂ) ∈ ball (0 : ℂ) 1) := by
    obtain ⟨j,hj,hjr⟩ := hcircle i
    let e' : range j ≃ₜ Circle := (Homeomorph.setCongr hjr).trans e
    have hc : ∃ x, V i = connectedComponentIn (range j)ᶜ x := by rw [hjr]; exact hcomp i
    obtain ⟨hf,hcl,F,hFb,hFi⟩ := cairns_bounded_component_disk_extension
      j hj (V i) (hV i).1 hc (hbdd i) e'
    refine ⟨hf.trans hjr, hcl.trans (by rw [hjr]), F, ?_, ?_⟩
    · intro z hz
      exact hFb z (hjr.symm ▸ hz)
    · intro z
      constructor
      · intro hz
        rw [← hFi]
        exact ⟨z,hz,rfl⟩
      · intro hz
        rw [← hFi] at hz
        obtain ⟨w,hw,heq⟩ := hz
        exact F.injective (Subtype.ext heq) ▸ hw
  have hcanonical (i) : Nonempty (↥(K ∪ A i) ≃ₜ Circle) := by
    obtain ⟨j,hj,hjr⟩ := hcircle i
    exact ⟨(Homeomorph.setCongr hjr.symm).trans hj.toHomeomorph.symm⟩
  let e (i) := Classical.choice (hcanonical i)
  have hfull (i) := hext i (e i)
  change ∃ W : Fin 2 → Set ℂ, _
  refine ⟨V,hV,hdis,?_,?_,?_,?_,?_,?_⟩
  · exact hcov.trans hdiff.symm
  · rw [hdiff]
    ext C
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨i,hi⟩ := hclass z hz
      exact ⟨i,hi.symm⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨z,hz⟩ := (hV i).1
      refine ⟨z,hVs i hz,?_⟩
      obtain ⟨k,hk⟩ := hclass z (hVs i hz)
      have heq : V i = V k := by
        by_cases hik : i=k
        · rw [hik]
        have hz' : z ∈ V k := hk ▸ mem_connectedComponentIn (hVs i hz)
        fin_cases i <;> fin_cases k
        · exact (hik rfl).elim
        · exact (disjoint_left.mp hdis hz hz').elim
        · exact (disjoint_left.mp hdis hz' hz).elim
        · exact (hik rfl).elim 
      exact hk.trans heq.symm
  · exact fun i ↦ (hfull i).1
  · ext z
    constructor
    · rintro ⟨hz0,hz1⟩
      rw [(hfull 0).2.1] at hz0
      rw [(hfull 1).2.1] at hz1
      rcases hz0 with hz0 | hz0
      · rcases hz1 with hz1 | hz1
        · exact False.elim (disjoint_left.mp hdis hz0 hz1)
        · rcases hz1 with hzK | hzA
          · exact hzK
          · exact False.elim (disjoint_left.mp sphere_disjoint_ball (hAs 1 hzA) (hVs 0 hz0).1)
      · rcases hz0 with hzK | hzA0
        · exact hzK
        · rcases hz1 with hz1 | hz1
          · exact False.elim (disjoint_left.mp sphere_disjoint_ball (hAs 0 hzA0) (hVs 1 hz1).1)
          · rcases hz1 with hzK | hzA1
            · exact hzK
            · have hdet : (conj (γ 1-γ 0)*(z-γ 0)).im = 0 :=
                le_antisymm (by simpa [A] using hzA0.2) (by simpa [A] using hzA1.2)
              rcases circle_chord_det_eq_zero h0 h1 hzA0.1 huv hdet with rfl | rfl <;>
                exact mem_range_self _
    · intro hz
      exact ⟨(hfull 0).2.1.symm ▸ Or.inr (Or.inl hz),
        (hfull 1).2.1.symm ▸ Or.inr (Or.inl hz)⟩
  · intro i
    obtain ⟨F,hFb,hFi⟩ := (hfull i).2.2
    refine ⟨F,hFi,?_⟩
    intro z
    have hzcl : (z : ℂ) ∈ V i ∪ (K ∪ A i) :=
      (congrArg (fun S : Set ℂ ↦ (z : ℂ) ∈ S) (hfull i).2.1).mp z.property
    have hnot : (z : ℂ) ∈ K ∪ A i ↔ (z : ℂ) ∉ V i := by
      constructor
      · exact fun hz hV ↦ havoid i hV hz
      · intro hn; exact hzcl.resolve_left hn
    rw [hnot, hFi]
    exact ⟨fun h ↦ le_antisymm (F z).property (not_lt.mp h),
      fun h hb ↦ (not_lt_of_ge h.ge) hb⟩
  · intro i e
    obtain ⟨_,_,F,hFb,hFi⟩ := hext i e
    refine ⟨F,hFi,?_⟩
    intro z
    have hzcl : (z : ℂ) ∈ closure (V i) :=
      (hfull i).2.1.symm ▸ Or.inr z.property
    exact ⟨hzcl,hFb ⟨z,hzcl⟩ z.property⟩

end HolomorphicAnosov

