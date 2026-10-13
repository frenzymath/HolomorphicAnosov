import HolomorphicAnosov.Dynamics.Bowen.FactOneNarrowBracketModulus
import HolomorphicAnosov.Dynamics.Bowen.PlaqueSliceInteriorDensity
import HolomorphicAnosov.Dynamics.Bowen.WitnessedTransitionRadius
import HolomorphicAnosov.Dynamics.Bowen.FiniteItineraryRefinement
import HolomorphicAnosov.Dynamics.Bowen.FactOneRefinementScales
import HolomorphicAnosov.Dynamics.Bowen.FiniteItineraryBracketClosure
import HolomorphicAnosov.Dynamics.Bowen.InteriorBracketRadius
import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData
import HolomorphicAnosov.Dynamics.Bowen.ExistsGoodOrbitInOpen
import HolomorphicAnosov.Topology.ManningBowenIterateAtomMarkov

/-!
# Bowen proper Markov partitions in compact canonical coordinates

DAG: `dynamics.bowen_compact_local_product_proper_partition`.
Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
Fact 1 pp.726–727, Lemmas 2–11 pp.727–731, Theorem 12 and Lemmas 13–25
pp.731–740. All topology is the given compact metric space topology.
Rectangles need not be connected. The output laws concern the original f,
not only the positive iterate used inside the construction. Empty X is allowed.
-/

namespace HolomorphicAnosov.Dynamics.Bowen

open Set

/-- Arbitrarily fine proper Markov partitions from compact canonical-coordinate data.

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970), Fact 1,
Lemma 23 p.738, Lemma 24 p.739 and Lemma 25 pp.739–740. The proof below expands
Lemma 24's endpoint transport using the elementary open-set/closure inclusion.
It uses the original map for the final laws and a positive iterate only for the
atom provider. Rectangles need not be connected.

Source proof and formal deduction:

1. Handle empty X by the empty finite family. For nonempty X, choose positive uniform radii for
interior bracket closure, finite-itinerary bracket closure, and witnessed-transition extension.
Choose a positive mesh below these radii and the requested epsilon. The narrow-bracket modulus
on the compact pair core and the eight-scale theorem give alpha_0=gamma, alpha_3 below that
mesh, guarded bracket scales and one-step continuity margins.

2. Apply the iterate-atom provider with these scales and the original data. It gives m>0, an open
dense good set Z, the finite image of closed atoms P(z), their properness and disjoint
interiors, and the stable/unstable laws for h=f^m at z,hz in Z. The profile formula gives z in
interior P(z) for every z in Z. Enumerate the finite atom image by Fin N; representatives
transfer all its properties. The initial cover, enlargement and quadrant construction are
entirely inside the iterate-atom provider, whose admitted proof remains a lower obligation.

3. Apply the finite-itinerary theorem to the enumerated atom cover. For each word of length m the
closure E of the intersection of the open orbit constraints is regular closed, its interior is
exactly that intersection, the E cover X and distinct words have disjoint interiors. The uniform
interior-bracket theorem and finite-itinerary bracket theorem prove bracket closure. The time-
zero containment bounds the diameter by alpha_3<epsilon. Discard empty E and enumerate the
remaining words to obtain the final finite family.

4. Each nonempty open transition has a witness w whose orbit from time zero through m lies in Z.
Disjoint atom interiors identify the two itinerary labels at their overlapping times, and
identify the endpoint atoms with P(w) and P(h w). For z in the ambient interior of the source
and stable to w, the h-stable law puts h z in P(h w). Thus f z satisfies the last target
constraint closedly and all earlier constraints openly. Their open intersection meets the
closure of the last constraint interior; IsOpen.inter_closure puts f z in the target itinerary
closure. For t in the ambient target interior and unstable to f w, induction transports its
unstable membership forward through m-1 times: time zero at each step is bounded by the common
target atom diameter, and all earlier backward times shift. The h-unstable covering then puts
f^-1 t in P(w). All other source constraints are open, so the same regular-closure argument puts
f^-1 t in the source itinerary closure. This proves the ambient-interior transport underlying
Bowen Lemma24; it does not identify closure of an arbitrary intersection with intersection of
closures.

5. At an interior basepoint, continuous bracket projection sends ambient interior points into the
corresponding interior slice and fixes the whole closed slice. Regular closure therefore makes
those interior slice points dense in the closed slice. Apply this density theorem to the source
stable and target unstable slices. Continuity of f and f^-1 and closedness of the receiving
rectangles extend the preceding ambient-interior membership laws to the entire closed slices.
Forward and backward shifting give the required plaque membership. This completes Bowen Lemma24
at the good-orbit witness.

6. The uniform witnessed-transition theorem applies because both rectangles have pair distances at
most alpha_3 below its radius and are bracket closed. It extends both witness laws to the
requested interior transition point. Together with the previously proved finite-cover,
properness, mesh and disjointness clauses, this proves the original-map partition statement.
Only the independently admitted lower providers remain unproved.

This theorem has no local admission. Its iterate-atom provider and that provider's
initial-cover/enlargement dependencies retain their own admissions, so the
transitive axiom check still includes `sorryAx`. No data definition is hollow.
-/
theorem compactLocalProductProperPartition
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData f γ lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (R : Fin N → Set X),
      (∀ i, (R i).Nonempty ∧ IsCompact (R i) ∧
        Metric.diam (R i) < ε ∧ R i = closure (interior (R i)) ∧
        ∀ x ∈ R i, ∀ y ∈ R i, H.bracket x y ∈ R i) ∧
      (⋃ i, R i) = univ ∧
      (∀ i j : Fin N, i ≠ j → Disjoint (interior (R i)) (interior (R j))) ∧
      (∀ (i j : Fin N) (x : X), x ∈ interior (R i) → f x ∈ interior (R j) →
        f '' (R i ∩ relativeClosedStablePlaque f γ x) ⊆
          R j ∩ relativeClosedStablePlaque f γ (f x) ∧
        R j ∩ relativeClosedUnstablePlaque f γ (f x) ⊆
          f '' (R i ∩ relativeClosedUnstablePlaque f γ x)) := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
    refine ⟨0, Fin.elim0, ?_⟩
    simp only [Fin.forall_fin_zero, iUnion_of_empty, true_and, and_true]
    ext x
    exact isEmptyElim x
  | inr hX =>
    obtain ⟨rInterior, hrInterior, hrInteriorCore, hInterior⟩ :=
      exists_interior_bracket_radius f γ lam H
    obtain ⟨rJoin, hrJoin, hrJoinCore, hJoin⟩ :=
      finiteItineraryBracketClosure f γ lam H
    obtain ⟨rTransition, hrTransition, hrTransitionCore, hTransition⟩ :=
      exists_witnessed_transition_radius f γ lam H
    let mesh := min ε (min rInterior (min rJoin rTransition))
    have hmesh : 0 < mesh := lt_min hε (lt_min hrInterior (lt_min hrJoin hrTransition))
    have hmodulus : ∀ δ : {δ : ℝ // 0 < δ}, ∃ η : ℝ, 0 < η ∧
        η ≤ H.closeRadius ∧ ∀ x y, dist x y ≤ η →
          H.bracket x y ∈ relativeClosedStablePlaque f δ.val x ∩
            relativeClosedUnstablePlaque f δ.val y := fun δ ↦
      HolomorphicAnosov.BowenBasicSetCoding.factOne_narrow_bracket_modulus
        f γ lam H.closeRadius H.gamma_pos H.lambda_pos.le H.lambda_lt_one.le
        H.closeRadius_pos H.bracket H.bracket_mem H.bracket_unique H.bracket_continuous
        H.stable_contraction H.unstable_contraction δ.val δ.property
    choose η hη hηcore hηmem using hmodulus
    let εmod : ℝ → ℝ := fun δ ↦ if h : 0 < δ then η ⟨δ, h⟩ else H.closeRadius
    have hmodpos : ∀ δ, 0 < δ → 0 < εmod δ := by
      intro δ hδ
      simpa only [εmod, dite_eq_left hδ] using hη ⟨δ, hδ⟩
    obtain ⟨a, ha0, hapos, hadesc, hamesh, hascale, hamap⟩ :=
      HolomorphicAnosov.BowenBasicSetCoding.exists_factOne_refinement_scales
        f γ mesh H.gamma_pos hmesh εmod hmodpos
    have hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
        ∀ x y, dist x y ≤ εmod δ →
          H.bracket x y ∈ relativeClosedStablePlaque f δ x ∩
            relativeClosedUnstablePlaque f δ y := by
      intro δ hδ _
      refine ⟨hmodpos δ hδ, ?_⟩
      intro x y hxy
      exact hηmem ⟨δ, hδ⟩ x y (by simpa only [εmod, dite_eq_left hδ] using hxy)
    obtain ⟨m, hm, hAtoms⟩ := manning_bowen_iterate_atom_markov
      f lam γ H.closeRadius H.lambda_pos H.lambda_lt_one H.gamma_pos
      H.closeRadius_pos a εmod ha0 hapos hadesc hascale hamap H.bracket
      (fun x y z n hy hz ↦ H.stable_contraction x y z hy hz n)
      (fun x y z n hy hz ↦ H.unstable_contraction x y z hy hz n)
      (fun x y hxy ↦ ⟨H.bracket_mem x y hxy,
        fun z hz ↦ H.bracket_unique x y z hxy hz⟩) H.bracket_continuous hmod
    have ha3mesh : a 3 < mesh := hamesh 2
    have ha3ε : a 3 < ε := ha3mesh.trans_le (min_le_left _ _)
    have ha3Interior : a 3 < rInterior := ha3mesh.trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
    have ha3Join : a 3 < rJoin := ha3mesh.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have ha3Transition : a 3 < rTransition := ha3mesh.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rcases hAtoms with ⟨count, hcount, center, C0, D0, select, sat, s, t,
      target, y, reverseTarget, reverseY, Cseq, Dseq, Cfinal, Dfinal, Eu, Es, hdata⟩
    extract_lets A0 A Cu Ds Q V profile Z O P at hdata
    rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hZopen, hZdense, hprofile, hPfinite, hPcover, hPproper, hPdisjoint, hPmarkov⟩
    have hZinterior (z : X) (hz : z ∈ Z) : z ∈ interior (P z) := by
      rw [hPproper z hz |>.2]
      dsimp only [O]
      apply mem_iInter.mpr
      intro i
      apply mem_iInter.mpr
      intro hi
      obtain ⟨στ, hστ, _⟩ := hprofile z hz i hi
      exact mem_iUnion.mpr ⟨στ.1, mem_iUnion.mpr ⟨στ.2,
        mem_iUnion.mpr ⟨hστ, hστ⟩⟩⟩
    let atoms : Set (Set X) := P '' Z
    have : Fintype atoms := hPfinite.fintype
    let nAtoms := Fintype.card atoms
    let atomEquiv : Fin nAtoms ≃ atoms := (Fintype.equivFin atoms).symm
    let B : Fin nAtoms → Set X := fun i ↦ (atomEquiv i).val
    have hBrep (i : Fin nAtoms) : ∃ z ∈ Z, P z = B i := (atomEquiv i).property
    have hBproper (i : Fin nAtoms) : (B i).Nonempty ∧ IsCompact (B i) ∧
        (∀ x ∈ B i, ∀ y ∈ B i, H.bracket x y ∈ B i) ∧
        Metric.diam (B i) ≤ a 3 ∧ B i = closure (interior (B i)) := by
      obtain ⟨z, hz, heq⟩ := hBrep i
      exact heq ▸ (hPproper z hz).1
    have hBcover : (⋃ i, B i) = univ := by
      apply eq_univ_iff_forall.mpr
      intro x
      have hx : x ∈ ⋃ z ∈ Z, P z := hPcover.symm ▸ mem_univ x
      obtain ⟨z, hxz⟩ := mem_iUnion.mp hx
      obtain ⟨hz, hxz⟩ := mem_iUnion.mp hxz
      let q : atoms := ⟨P z, mem_image_of_mem P hz⟩
      exact mem_iUnion.mpr ⟨atomEquiv.symm q, by simpa [B] using hxz⟩
    have hBdisjoint (i j : Fin nAtoms) (hij : i ≠ j) :
        Disjoint (interior (B i)) (interior (B j)) := by
      obtain ⟨z, hz, heq⟩ := hBrep i
      obtain ⟨w, hw, heq'⟩ := hBrep j
      rw [← heq, ← heq']
      apply hPdisjoint z hz w hw
      intro hzw
      apply hij
      apply atomEquiv.injective
      apply Subtype.ext
      exact heq.symm.trans (hzw.trans heq')
    obtain ⟨hEregular, hEdisjoint, hEcover, hEsubset⟩ :=
      finiteItineraryRefinement f nAtoms m B
        (fun i ↦ (hBproper i).2.2.2.2) hBcover hBdisjoint
    let E : (Fin m → Fin nAtoms) → Set X := fun w ↦
      closure (⋂ k : Fin m, (⇑(f ^ k.val) : X → X) ⁻¹' interior (B (w k)))
    have hBdist (i : Fin nAtoms) (x : X) (hx : x ∈ B i) (y : X) (hy : y ∈ B i) :
        dist x y ≤ a 3 :=
      (Metric.dist_le_diam_of_mem (hBproper i).2.1.isBounded hx hy).trans
        (hBproper i).2.2.2.1
    have hBinterior (i : Fin nAtoms) : ∀ x ∈ interior (B i),
        ∀ y ∈ interior (B i), H.bracket x y ∈ interior (B i) :=
      hInterior (B i) (fun x hx y hy ↦ (hBdist i x hx y hy).trans ha3Interior.le)
        (hBproper i).2.2.1
    have hEbracket (w : Fin m → Fin nAtoms) : ∀ x ∈ E w,
        ∀ y ∈ E w, H.bracket x y ∈ E w :=
      hJoin nAtoms m hm B (fun i ↦ (hBproper i).2.1.isClosed)
        (fun i x hx y hy ↦ (hBdist i x hx y hy).trans ha3Join.le) hBinterior w
    have hEdiamBound (w : Fin m → Fin nAtoms) : Metric.diam (E w) ≤ a 3 := by
      have hsub : E w ⊆ B (w ⟨0, hm⟩) := by
        exact hEsubset w ⟨0, hm⟩
      exact (Metric.diam_mono hsub (hBproper _).2.1.isBounded).trans
        (hBproper _).2.2.2.1
    have hEdiam (w : Fin m → Fin nAtoms) : Metric.diam (E w) < ε :=
      (hEdiamBound w).trans_lt ha3ε
    let retained := {w : Fin m → Fin nAtoms // (E w).Nonempty}
    let nRetained := Fintype.card retained
    let wordEquiv : Fin nRetained ≃ retained := (Fintype.equivFin retained).symm
    let R : Fin nRetained → Set X := fun i ↦ E (wordEquiv i).val
    have hRproper (i : Fin nRetained) : (R i).Nonempty ∧ IsCompact (R i) ∧
        Metric.diam (R i) < ε ∧ R i = closure (interior (R i)) ∧
        ∀ x ∈ R i, ∀ y ∈ R i, H.bracket x y ∈ R i :=
      ⟨(wordEquiv i).property, isClosed_closure.isCompact, hEdiam _,
        (hEregular _).2, hEbracket _⟩
    have hRcover : (⋃ i, R i) = univ := by
      apply eq_univ_iff_forall.mpr
      intro x
      have hx : x ∈ ⋃ w, E w := hEcover.symm ▸ mem_univ x
      obtain ⟨w, hw⟩ := mem_iUnion.mp hx
      let q : retained := ⟨w, ⟨x, hw⟩⟩
      exact mem_iUnion.mpr ⟨wordEquiv.symm q, by simpa [R] using hw⟩
    have hRdisjoint (i j : Fin nRetained) (hij : i ≠ j) :
        Disjoint (interior (R i)) (interior (R j)) := by
      apply hEdisjoint
      intro heq
      exact hij (wordEquiv.injective (Subtype.ext heq))
    refine ⟨nRetained, R, hRproper, hRcover, hRdisjoint, ?_⟩
    intro i j x hx hfx
    have hRsmall (k : Fin nRetained) (p : X) (hp : p ∈ R k)
        (q : X) (hq : q ∈ R k) : dist p q ≤ rTransition :=
      ((Metric.dist_le_diam_of_mem (hRproper k).2.1.isBounded hp hq).trans
        (hEdiamBound _)).trans ha3Transition.le
    obtain ⟨w, hw, hgood⟩ := exists_good_orbit_in_open f hZopen hZdense
      (isOpen_interior.inter (isOpen_interior.preimage f.continuous))
      (show (interior (R i) ∩ f ⁻¹' interior (R j)).Nonempty from ⟨x, hx, hfx⟩) m
    have hRinterior (k : Fin nRetained) : ∀ p ∈ interior (R k),
        ∀ q ∈ interior (R k), H.bracket p q ∈ interior (R k) :=
      hInterior (R k) (fun p hp q hq ↦
        ((Metric.dist_le_diam_of_mem (hRproper k).2.1.isBounded hp hq).trans
          (hEdiamBound _)).trans ha3Interior.le) (hRproper k).2.2.2.2
    have hdensity_i := plaque_slice_interior_density f γ lam H (R i)
      (hRproper i).2.2.2.1 (fun p hp q hq ↦ (hRsmall i p hp q hq).trans hrTransitionCore)
      (hRinterior i) w hw.1
    have hdensity_j := plaque_slice_interior_density f γ lam H (R j)
      (hRproper j).2.2.2.1 (fun p hp q hq ↦ (hRsmall j p hp q hq).trans hrTransitionCore)
      (hRinterior j) (f w) hw.2
    have hRword (l : Fin nRetained) (z : X) (hz : z ∈ interior (R l))
        (k : Fin m) : (f ^ k.val) z ∈ interior (B ((wordEquiv l).val k)) := by
      have hz' : z ∈ interior (E (wordEquiv l).val) := hz
      rw [(hEregular _).1] at hz'
      exact mem_iInter.mp hz' k
    have hBidentify (z : X) (hz : z ∈ Z) (b : Fin nAtoms)
        (hzb : z ∈ interior (B b)) : B b = P z := by
      obtain ⟨q, hq, heq⟩ := hBrep b
      by_contra hne
      have hd := hPdisjoint q hq z hz (by simpa only [heq] using hne)
      exact Set.disjoint_left.mp hd (heq.symm ▸ hzb) (hZinterior z hz)
    have hOverlap (k : Fin m) (hk : k.val + 1 < m) :
        B ((wordEquiv j).val k) = B ((wordEquiv i).val ⟨k.val + 1, hk⟩) := by
      have hleft := hRword j (f w) hw.2 k
      have hright := hRword i w hw.1 ⟨k.val + 1, hk⟩
      have hpow : (f ^ (k.val + 1)) w = (f ^ k.val) (f w) := by
        rw [pow_succ, Homeomorph.mul_apply]
      rw [hpow] at hright
      by_cases heq : (wordEquiv j).val k = (wordEquiv i).val ⟨k.val + 1, hk⟩
      · rw [heq]
      · exact False.elim (Set.disjoint_left.mp (hBdisjoint _ _ heq) hleft hright)
    have hFirst : B ((wordEquiv i).val ⟨0, hm⟩) = P w :=
      hBidentify w (by simpa using hgood 0 (Nat.zero_le _)) _ (hRword i w hw.1 ⟨0, hm⟩)
    have hLast : B ((wordEquiv j).val ⟨m - 1, by omega⟩) = P ((f ^ m) w) := by
      apply hBidentify _ (hgood m le_rfl)
      have heq : (f ^ (m - 1)) (f w) = (f ^ m) w := by
        rw [← Homeomorph.mul_apply, ← pow_succ, Nat.sub_add_cancel hm]
      rw [← heq]
      exact hRword j (f w) hw.2 ⟨m - 1, by omega⟩
    have hwInterior :
        (∀ z ∈ interior (R i), z ∈ relativeClosedStablePlaque f γ w → f z ∈ R j) ∧
        (∀ t ∈ interior (R j), t ∈ relativeClosedUnstablePlaque f γ (f w) →
          f.symm t ∈ R i) := by
      constructor
      · intro z hz hzs
        let last : Fin m := ⟨m - 1, by omega⟩
        let tail := (⇑(f ^ last.val) : X → X) ⁻¹' B ((wordEquiv j).val last)
        let U : Set X := ⋂ k : {k : Fin m // k ≠ last},
          (⇑(f ^ k.val.val) : X → X) ⁻¹' interior (B ((wordEquiv j).val k.val))
        have hUopen : IsOpen U := isOpen_iInter_of_finite fun k ↦
          isOpen_interior.preimage (f ^ k.val.val).continuous
        have hzU : f z ∈ U := by
          apply mem_iInter.mpr
          intro k
          have hk : k.val.val + 1 < m := by
            have hne : k.val.val ≠ m - 1 := fun h ↦ k.property (Fin.ext h)
            omega
          change (f ^ k.val.val) (f z) ∈ interior (B ((wordEquiv j).val k.val))
          rw [hOverlap k.val hk]
          have hzk := hRword i z hz ⟨k.val.val + 1, hk⟩
          simpa only [pow_succ, Homeomorph.mul_apply] using hzk
        have hztail : f z ∈ tail := by
          have hzP : z ∈ P w := by
            rw [← hFirst]
            exact interior_subset (hRword i z hz ⟨0, hm⟩)
          have hforward := (hPmarkov w (by simpa using hgood 0 (Nat.zero_le _))
            (hgood m le_rfl)).2 ⟨z, ⟨hzP, hzs⟩, rfl⟩
          change (f ^ last.val) (f z) ∈ B ((wordEquiv j).val last)
          rw [hLast]
          simpa only [last, ← Homeomorph.mul_apply, ← pow_succ,
            Nat.sub_add_cancel hm] using hforward.1
        have htailreg : tail = closure (interior tail) := by
          dsimp only [tail]
          rw [← (f ^ last.val).preimage_interior, ← (f ^ last.val).preimage_closure,
            ← (hBproper _).2.2.2.2]
        have hcl := hUopen.inter_closure ⟨hzU, htailreg ▸ hztail⟩
        apply closure_mono (t := ⋂ k : Fin m,
          (⇑(f ^ k.val) : X → X) ⁻¹' interior (B ((wordEquiv j).val k))) ?_ hcl
        intro p hp
        apply mem_iInter.mpr
        intro k
        by_cases hk : k = last
        · subst k
          simpa only [tail, ← Homeomorph.preimage_interior] using hp.2
        · exact mem_iInter.mp hp.1 ⟨k, hk⟩
      · intro t ht htu
        have ha3γ : a 3 ≤ γ := by
          have h32 := hadesc 2
          have h21 := hadesc 1
          have h10 := hadesc 0
          change a 3 < a 2 at h32
          change a 2 < a 1 at h21
          change a 1 < a 0 at h10
          linarith [ha0]
        have hprefix (k : ℕ) (hk : k < m) :
            (f ^ k) t ∈ relativeClosedUnstablePlaque f γ ((f ^ k) (f w)) := by
          induction k with
          | zero => exact htu
          | succ k ih =>
            have hprev := ih (by omega)
            intro n
            cases n with
            | zero =>
              exact (hBdist ((wordEquiv j).val ⟨k + 1, hk⟩) _
                (interior_subset (hRword j t ht ⟨k + 1, hk⟩)) _
                (interior_subset (hRword j (f w) hw.2 ⟨k + 1, hk⟩))).trans ha3γ
            | succ n =>
              simpa only [pow_succ', Homeomorph.mul_apply, Function.iterate_succ_apply,
                Homeomorph.symm_apply_apply] using hprev n
        let last : Fin m := ⟨m - 1, by omega⟩
        have htarget : (f ^ last.val) t ∈ P ((f ^ m) w) ∩
            relativeClosedUnstablePlaque f γ ((f ^ m) w) := by
          constructor
          · rw [← hLast]
            exact interior_subset (hRword j t ht last)
          · have heq : (f ^ last.val) (f w) = (f ^ m) w := by
              rw [← Homeomorph.mul_apply, ← pow_succ, Nat.sub_add_cancel hm]
            rw [← heq]
            exact hprefix last.val last.isLt
        obtain ⟨q, hq, hfq⟩ := (hPmarkov w
          (by simpa using hgood 0 (Nat.zero_le _)) (hgood m le_rfl)).1 htarget
        have hfqt : f q = t := by
          apply (f ^ last.val).injective
          calc
            (f ^ last.val) (f q) = (f ^ m) q := by
              rw [← Homeomorph.mul_apply, ← pow_succ, Nat.sub_add_cancel hm]
            _ = (f ^ last.val) t := hfq
        have hfirst : f.symm t ∈ B ((wordEquiv i).val ⟨0, hm⟩) := by
          rw [hFirst, ← hfqt, f.symm_apply_apply]
          exact hq.1
        let first : Fin m := ⟨0, hm⟩
        let U : Set X := ⋂ k : {k : Fin m // k ≠ first},
          (⇑(f ^ k.val.val) : X → X) ⁻¹' interior (B ((wordEquiv i).val k.val))
        have hUopen : IsOpen U := isOpen_iInter_of_finite fun k ↦
          isOpen_interior.preimage (f ^ k.val.val).continuous
        have htU : f.symm t ∈ U := by
          apply mem_iInter.mpr
          intro k
          have hkpos : 0 < k.val.val := by
            have hne : k.val.val ≠ 0 := fun h ↦ k.property (Fin.ext h)
            omega
          let prev : Fin m := ⟨k.val.val - 1, by omega⟩
          have hk : prev.val + 1 < m := by dsimp [prev]; omega
          have heq : (⟨prev.val + 1, hk⟩ : Fin m) = k.val := by
            apply Fin.ext
            exact Nat.sub_add_cancel hkpos
          have hover := hOverlap prev hk
          rw [heq] at hover
          change (f ^ k.val.val) (f.symm t) ∈ interior (B ((wordEquiv i).val k.val))
          rw [← hover]
          have hpow : (f ^ k.val.val) (f.symm t) = (f ^ prev.val) t := by
            calc
              (f ^ k.val.val) (f.symm t) = (f ^ (prev.val + 1)) (f.symm t) := by
                rw [show prev.val + 1 = k.val.val from Nat.sub_add_cancel hkpos]
              _ = (f ^ prev.val) t := by
                rw [pow_succ, Homeomorph.mul_apply, f.apply_symm_apply]
          rw [hpow]
          exact hRword j t ht prev
        have hcl := hUopen.inter_closure
          ⟨htU, (hBproper ((wordEquiv i).val first)).2.2.2.2 ▸ hfirst⟩
        apply closure_mono (t := ⋂ k : Fin m,
          (⇑(f ^ k.val) : X → X) ⁻¹' interior (B ((wordEquiv i).val k))) ?_ hcl
        intro p hp
        apply mem_iInter.mpr
        intro k
        by_cases hk : k = first
        · subst k
          exact hp.2
        · exact mem_iInter.mp hp.1 ⟨k, hk⟩
    have hwmarkov :
        (f '' (R i ∩ relativeClosedStablePlaque f γ w) ⊆
          R j ∩ relativeClosedStablePlaque f γ (f w)) ∧
        (R j ∩ relativeClosedUnstablePlaque f γ (f w) ⊆
          f '' (R i ∩ relativeClosedUnstablePlaque f γ w)) := by
      constructor
      · rintro t ⟨z, hz, rfl⟩
        have hs : MapsTo f (interior (R i) ∩ relativeClosedStablePlaque f γ w) (R j) :=
          fun p hp ↦ hwInterior.1 p hp.1 hp.2
        have hzimage := hs.closure_of_continuousOn f.continuous.continuousOn
          (hdensity_i.1 hz)
        refine ⟨(hRproper j).2.1.isClosed.closure_eq ▸ hzimage, ?_⟩
        intro n
        simpa only [Function.iterate_succ_apply] using hz.2 (n + 1)
      · intro t ht
        have hu : MapsTo f.symm
            (interior (R j) ∩ relativeClosedUnstablePlaque f γ (f w)) (R i) :=
          fun p hp ↦ hwInterior.2 p hp.1 hp.2
        have htimage := hu.closure_of_continuousOn f.symm.continuous.continuousOn
          (hdensity_j.2 ht)
        refine ⟨f.symm t, ⟨(hRproper i).2.1.isClosed.closure_eq ▸ htimage, ?_⟩,
          f.apply_symm_apply t⟩
        intro n
        simpa only [Function.iterate_succ_apply, Homeomorph.symm_apply_apply] using
          ht.2 (n + 1)
    exact hTransition (R i) (R j) (hRsmall i) (hRsmall j)
      (hRproper i).2.2.2.2 (hRproper j).2.2.2.2
      w (interior_subset hw.1) (interior_subset hw.2) hwmarkov.1 hwmarkov.2
      x (interior_subset hx) (interior_subset hfx)

end HolomorphicAnosov.Dynamics.Bowen
