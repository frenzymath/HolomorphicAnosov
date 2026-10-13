import Mathlib.Topology.Homeomorph.Defs

/-!
# Closed-slice transport in Bowen's iterate construction

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
Lemma 22 and the last paragraph of its proof, pp.737--738.  The geometric
part of that lemma first transports the relative interiors of the unstable
and stable slices.  The displayed closed-slice inclusions then follow by
taking closures and using the fact that a homeomorphism preserves closure.

DAG node: `topo.manning_bowen_markov_closure_transport_g10`.
-/

namespace HolomorphicAnosov.Topology

open Set

/-- Bowen's final closure step for the iterate Markov laws.

The hypotheses are exactly the interface produced by the quadrant and slice
construction: each slice is regular closed, and the preceding local
coordinate argument transports its relative interior.  The conclusion is
the closed unstable inclusion and the closed stable inclusion for the same
iterate.  This separates the elementary topological closure argument from
the source-dependent construction of the quadrants and of the interior
transport.  See Bowen 1970, Lemma 22, pp.737--738.

The theorem is intentionally stated for arbitrary indexed families of slices;
no connectedness, manifold, or extra Markov assumption is hidden in it.
-/
theorem manning_bowen_markov_closure_transport
    {X : Type*} [TopologicalSpace X]
    (h : X ≃ₜ X) (Z : Set X) (U S Uo So : X → Set X)
    (hUreg : ∀ z ∈ Z, U z = closure (Uo z))
    (hSreg : ∀ z ∈ Z, S z = closure (So z))
    (hUint : ∀ z ∈ Z, h z ∈ Z →
      h ⁻¹' Uo (h z) ⊆ Uo z)
    (hSint : ∀ z ∈ Z, h z ∈ Z →
      h '' So z ⊆ So (h z)) :
    ∀ z ∈ Z, h z ∈ Z →
      U (h z) ⊆ h '' U z ∧ h '' S z ⊆ S (h z) := by
  intro z hz hhz
  constructor
  · intro x hx
    have hxpre : h.symm x ∈ closure (h ⁻¹' Uo (h z)) := by
      have hx' : x ∈ closure (Uo (h z)) := by
        rwa [← hUreg (h z) hhz]
      have hx'' : h.symm x ∈ h ⁻¹' closure (Uo (h z)) := by
        simpa using hx'
      simpa [h.preimage_closure] using hx'' 
    have hxin : h.symm x ∈ closure (Uo z) :=
      closure_mono (hUint z hz hhz) hxpre
    have hxin' : h.symm x ∈ U z := by
      rw [hUreg z hz]
      exact hxin
    exact ⟨h.symm x, hxin', by simp⟩
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hyint : y ∈ closure (So z) := by
      rw [← hSreg z hz]
      exact hy
    have hyimage : h y ∈ closure (h '' So z) := by
      rw [← h.image_closure]
      exact ⟨y, hyint, rfl⟩
    have hyin : h y ∈ closure (So (h z)) :=
      closure_mono (hSint z hz hhz) hyimage
    rw [hSreg (h z) hhz]
    exact hyin

end HolomorphicAnosov.Topology
