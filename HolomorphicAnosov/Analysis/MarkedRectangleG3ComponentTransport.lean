import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs
open Set
namespace HolomorphicAnosov.Analysis
noncomputable section

/-- Ambient component transport for a homeomorphism between subtypes.

If a homeomorphism `h : D ≃ₜ Q` identifies the relative sets cut out by `F` and
`G`, then the ambient connected component of `G` is the image of the ambient
component of `F`. The proof uses only subtype topology, `Homeomorph.image_connectedComponentIn`,
and maximality of connected components. This is the component bridge needed by
Conway's short-cap argument after the source circular-arc component has been
identified.

Source: the component transport step in Conway, *Functions of One Complex
Variable II*, Chapter 14, Theorem 5.5, proof (d)⇒(a), p.50, formalized via
Mathlib's subtype and connected-component APIs. -/
theorem homeomorph_component_image_ambient {D Q : Set ℂ} (h : D ≃ₜ Q)
    (F G : Set ℂ) (hG : G ⊆ Q)
    (hFG : h '' {x : D | (x : ℂ) ∈ F} = {y : Q | (y : ℂ) ∈ G})
    {x : D} (hx : (x : ℂ) ∈ F) :
    connectedComponentIn G (h x : ℂ) =
      (fun z : D ↦ (h z : ℂ)) ''
        connectedComponentIn {x : D | (x : ℂ) ∈ F} x := by
  let S : Set D := {x : D | (x : ℂ) ∈ F}
  let T : Set Q := {y : Q | (y : ℂ) ∈ G}
  have hxS : x ∈ S := hx
  have hxT : h x ∈ T := by
    rw [show T = {y : Q | (y : ℂ) ∈ G} by rfl]
    rw [← hFG]
    exact ⟨x, hx, rfl⟩
  have hxG : (h x : ℂ) ∈ G := hxT
  have hcomp_sub : h '' connectedComponentIn S x =
      connectedComponentIn T (h x) := by
    change h '' connectedComponentIn ({x : D | (x : ℂ) ∈ F}) x =
      connectedComponentIn ({y : Q | (y : ℂ) ∈ G}) (h x)
    rw [← hFG]
    exact h.image_connectedComponentIn (show x ∈ {x : D | (x : ℂ) ∈ F} from hx)
  apply Set.Subset.antisymm
  · intro z hz
    have hzG : z ∈ G := connectedComponentIn_subset G (h x : ℂ) hz
    let y : Q := ⟨z, hG hzG⟩
    let C : Set Q := (Subtype.val : Q → ℂ) ⁻¹' connectedComponentIn G (h x : ℂ)
    have hCimage : (Subtype.val : Q → ℂ) '' C = connectedComponentIn G (h x : ℂ) := by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact hv
      · intro hw
        exact ⟨⟨w, hG (connectedComponentIn_subset G (h x : ℂ) hw)⟩, hw, rfl⟩
    have hCpre : IsPreconnected C := by
      apply ((Topology.IsEmbedding.subtypeVal (p := fun q : ℂ ↦ q ∈ Q)).isInducing.isPreconnected_image).mp
      rw [hCimage]
      exact isPreconnected_connectedComponentIn
    have hyC : y ∈ C := hz
    have hCx : h x ∈ C := mem_connectedComponentIn hxG
    have hCsub : C ⊆ T := by
      intro q hq
      change (q : ℂ) ∈ connectedComponentIn G (h x : ℂ) at hq
      exact connectedComponentIn_subset G (h x : ℂ) hq
    have hycompT : y ∈ connectedComponentIn T (h x) := by
      have hxy : connectedComponentIn T y = connectedComponentIn T (h x) := by
        apply connectedComponentIn_eq
        exact hCpre.subset_connectedComponentIn hyC hCsub hCx
      rw [← hxy]
      exact mem_connectedComponentIn (hCsub hyC)
    rw [← hcomp_sub] at hycompT
    obtain ⟨w, hw, hwy⟩ := hycompT
    refine ⟨w, hw, ?_⟩
    exact congrArg (fun q : Q ↦ (q : ℂ)) hwy
  · rintro z ⟨w, hw, rfl⟩
    have hwT : h w ∈ connectedComponentIn T (h x) := by
      rw [← hcomp_sub]
      exact mem_image_of_mem _ hw
    have hpre : IsPreconnected (connectedComponentIn T (h x)) := isPreconnected_connectedComponentIn
    have himgconn : IsPreconnected ((fun q : Q ↦ (q : ℂ)) '' connectedComponentIn T (h x)) :=
      hpre.image _ continuous_subtype_val.continuousOn
    have hsubset : (fun q : Q ↦ (q : ℂ)) '' connectedComponentIn T (h x) ⊆ G := by
      rintro q ⟨v, hv, rfl⟩
      change (v : ℂ) ∈ G
      have hv' : v ∈ T := connectedComponentIn_subset T (h x) hv
      exact hv'
    have hximg : (h x : ℂ) ∈ (fun q : Q ↦ (q : ℂ)) '' connectedComponentIn T (h x) :=
      ⟨h x, mem_connectedComponentIn hxT, rfl⟩
    have hcomp := himgconn.subset_connectedComponentIn hximg hsubset
    exact hcomp ⟨h w, hwT, rfl⟩
end

end HolomorphicAnosov.Analysis
