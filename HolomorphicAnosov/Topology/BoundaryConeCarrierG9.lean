import HolomorphicAnosov.Topology.BoundaryCycleConeG9

/-!
# The original carrier inside an attached boundary cone

Gallier--Xu, geometric realizations in Chapter 2 and Euler comparison in
Theorems 5.1--5.2, pp.72--74. This explicit coordinate adapter is an agent
supplement for gluing the actual cone disks to the original finite surface.
-/

open Set
open scoped BigOperators Classical
namespace HolomorphicAnosov.Topology.GallierXu

/-- The zero-apex slice of an attached boundary cone is exactly the original
carrier, under the coordinate inclusion which appends zero. The cycle-edge
hypothesis ensures a new cone triangle meets this slice in an old edge. -/
theorem carrier_attachBoundaryCone_snoc_zero_iff_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (hcycle : ∀ i : Fin l.length,
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces)
    (x : Fin N → ℝ) :
    Fin.snoc (fun i => (x i : (fun _ : Fin (N+1) => ℝ) i.castSucc)) 0 ∈ carrier (attachBoundaryCone K l) ↔ x ∈ carrier K := by
  classical
  have hsimplex :
      Fin.snoc (fun i => (x i : (fun _ : Fin (N+1) => ℝ) i.castSucc)) 0 ∈
        {f : Fin (N + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} ↔
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
    simp only [Set.mem_ofPred_eq]
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, add_zero]
    constructor
    · rintro ⟨hn, hs⟩
      exact ⟨fun i => by simpa using hn i.castSucc, hs⟩
    · rintro ⟨hn, hs⟩
      refine ⟨?_, hs⟩
      intro i
      cases i using Fin.lastCases <;> simp [hn]
  constructor
  · rintro ⟨hx, s, hs, hsupport⟩
    refine ⟨hsimplex.mp hx, ?_⟩
    change ((_ ∨ _) ∨ _) at hs
    rcases hs with (hold | hcone) | hsingle
    · obtain ⟨t, ht, rfl⟩ := hold
      refine ⟨t, ht, ?_⟩
      intro v hv
      simpa using hsupport v.castSucc (by simpa using hv)
    · obtain ⟨_, i, hsub⟩ := hcone
      refine ⟨_, hcycle i, ?_⟩
      intro v hv
      have hnot : v.castSucc ∉ boundaryConeTriangle l i := by
        intro hm
        simp only [boundaryConeTriangle, Finset.mem_insert, Finset.mem_image] at hm
        rcases hm with hlast | ⟨u, hu, huv⟩
        · exact fin_last_not_mem_image_castSucc_g9 ({v} : Finset (Fin N))
            (by simpa only [Finset.image_singleton, Finset.mem_singleton] using hlast.symm)
        · have huv' := (Fin.castSucc_injective N) huv
          exact hv (huv' ▸ (Finset.mem_insert.mpr hu))
      simpa using hsupport v.castSucc (fun hm => hnot (hsub hm))
    · obtain ⟨v, rfl⟩ := hsingle
      cases v using Fin.lastCases with
      | last =>
        have hz : ∀ i, x i = 0 := by
          intro i
          have hn : i.castSucc ∉ ({Fin.last N} : Finset (Fin (N + 1))) := by
            intro hm
            have he := Finset.mem_singleton.mp hm
            exact fin_last_not_mem_image_castSucc_g9 ({i} : Finset (Fin N))
              (by simpa only [Finset.image_singleton, Finset.mem_singleton] using he.symm)
          simpa using hsupport i.castSucc hn
        have hs := (hsimplex.mp hx).2
        simp [hz] at hs
      | cast v =>
        refine ⟨{v}, K.singleton_mem v, ?_⟩
        intro u hu
        simpa using hsupport u.castSucc (by simpa using hu)
  · rintro ⟨hx, t, ht, hsupport⟩
    refine ⟨hsimplex.mpr hx, t.image Fin.castSucc, Or.inl (Or.inl ⟨t, ht, rfl⟩), ?_⟩
    intro v hv
    cases v using Fin.lastCases with
    | last => simp
    | cast v => simpa using hsupport v (by simpa using hv)


/-- The original carrier is homeomorphic to the zero-apex slice of a cone attachment.
The map appends a zero barycentric coordinate and its inverse restricts to the old
vertices. This is the unchanged original-surface piece in the cone gluing construction.
Source: Gallier--Xu Chapter 2, geometric realization; explicit coordinate verification.
-/
def boundaryConeOriginalCarrierHomeomorph_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (hcycle : ∀ i : Fin l.length,
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces) :
    ↥(carrier K) ≃ₜ
      ↥{x : ↥(carrier (attachBoundaryCone K l)) | x.val (Fin.last N) = 0} where
  toFun x := ⟨⟨Fin.snoc (α := fun _ ↦ ℝ) x.val 0,
    (carrier_attachBoundaryCone_snoc_zero_iff_g9 K l hcycle x.val).mpr x.property⟩,
    by simp only [Set.mem_ofPred_eq, Fin.snoc_last]⟩
  invFun y := ⟨fun i ↦ y.val.val i.castSucc, by
    apply (carrier_attachBoundaryCone_snoc_zero_iff_g9 K l hcycle _).mp
    have heq : Fin.snoc (α := fun _ ↦ ℝ) (fun i ↦ y.val.val i.castSucc) 0 = y.val.val := by
      have hy : y.val.val (Fin.last N) = 0 := y.property
      funext i
      cases i using Fin.lastCases <;> simp [hy]
    rw [heq]
    exact y.val.property⟩
  left_inv x := by ext i; simp
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    have hy : y.val.val (Fin.last N) = 0 := y.property
    funext i
    cases i using Fin.lastCases <;> simp [hy]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    cases i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact continuous_const
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact (continuous_apply i).comp (continuous_subtype_val (p := carrier K))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply i.castSucc).comp (continuous_subtype_val.comp continuous_subtype_val)

/-- The barycentric inclusion of the original complex into its cone attachment
is a closed embedding. Its image is the closed zero set of the apex coordinate.
This verifies the original-carrier side of the closed-set pasting used to cap a surface.
Source: Gallier--Xu Chapter 2, geometric realization; the explicit zero-apex slice above.
-/
theorem boundaryConeOriginalCarrier_isClosedEmbedding_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (hcycle : ∀ i : Fin l.length,
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces) :
    Topology.IsClosedEmbedding (fun x : ↥(carrier K) ↦
      (⟨Fin.snoc (α := fun _ ↦ ℝ) x.val 0,
        (carrier_attachBoundaryCone_snoc_zero_iff_g9 K l hcycle x.val).mpr x.property⟩ :
        ↥(carrier (attachBoundaryCone K l)))) := by
  let e := boundaryConeOriginalCarrierHomeomorph_g9 K l hcycle
  have hclosed : IsClosed {x : ↥(carrier (attachBoundaryCone K l)) |
      x.val (Fin.last N) = 0} :=
    isClosed_eq ((continuous_apply (Fin.last N)).comp continuous_subtype_val) continuous_const
  exact hclosed.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding

end HolomorphicAnosov.Topology.GallierXu


