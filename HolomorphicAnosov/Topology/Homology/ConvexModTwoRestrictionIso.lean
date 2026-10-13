import HolomorphicAnosov.Topology.Homology.ConvexComplementPunctureEquiv
import HolomorphicAnosov.Topology.Homology.RelativeHomologyMapIsoCoefficients
import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.HomotopyEquivMod2HomologyIso

/-!
Mod-two convex support restriction. (Hatcher, Lemma 3.27)
-/

open CategoryTheory Set
namespace HolomorphicAnosov.Topology.Homology
universe u

/-- A compact convex support restricts isomorphically to each of its points in ordinary mod-two relative singular homology, in every degree. (Hatcher) -/
theorem convex_compact_modTwo_support_restriction_isIso
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK : Convex ℝ K) (hcompact : IsCompact K)
    (x : E) (hx : x ∈ K) (n : ℕ) :
    IsIso (modTwoSupportRestriction E K {x} (Set.singleton_subset_iff.mpr hx) n) := by
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.subset_ball_lt 0 x
  have hequiv : ∃ e : ContinuousMap.HomotopyEquiv ↥(Kᶜ) ↥({x}ᶜ : Set E),
      ∀ z, (e z).val = z.val := by
    let A : Set E := (fun z ↦ x + z) ⁻¹' K
    have hA : Convex ℝ A := hK.translate_preimage_right x
    have h0 : (0 : E) ∈ A := by simpa [A] using hx
    have hb : A ⊆ Metric.ball 0 R := by
      intro z hz
      have hz' := hbound hz
      simpa [Metric.mem_ball, dist_eq_norm] using hz'
    obtain ⟨e, he⟩ := HolomorphicAnosov.convex_complement_puncture_equiv A hA h0 R hR hb
    let p : ↥(Kᶜ) ≃ₜ ↥(Aᶜ) := {
      toFun := fun z ↦ ⟨z.val - x, by
        intro hz
        apply z.property
        change x + (z.val - x) ∈ K at hz
        simpa using hz⟩
      invFun := fun z ↦ ⟨x + z.val, z.property⟩
      left_inv := by intro z; ext; simp
      right_inv := by intro z; ext; simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let q : {z : E // z ≠ 0} ≃ₜ ↥({x}ᶜ : Set E) := {
      toFun := fun z ↦ ⟨x + z.val, by simpa using z.property⟩
      invFun := fun z ↦ ⟨z.val - x, sub_ne_zero.mpr z.property⟩
      left_inv := by intro z; ext; simp
      right_inv := by intro z; ext; simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    refine ⟨(p.toHomotopyEquiv.trans e).trans q.toHomotopyEquiv, ?_⟩
    intro z
    change x + (e (p z)).val = z.val
    rw [he]
    change x + (z.val - x) = z.val
    simp
  obtain ⟨e, he⟩ := hequiv
  apply HolomorphicAnosov.relative_homologyMap_isIso_of_absolute_coefficients
  · intro i
    have hm : (singularSupportRestrictionPair E K {x} (Set.singleton_subset_iff.mpr hx)).hom.left =
        TopCat.toSSet.map (TopCat.ofHom e.toFun) := by
      change TopCat.toSSet.map _ = TopCat.toSSet.map _
      apply congrArg
      ext z
      exact (he z).symm
    rw [hm]
    exact (inferInstance : IsIso (HolomorphicAnosov.homotopyEquiv_mod2_homology_iso e i).hom)
  · intro i
    change IsIso (SSet.homologyMap (TopCat.toSSet.map (𝟙 _)) _ i)
    infer_instance


end HolomorphicAnosov.Topology.Homology

