import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatchingImagePerm
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set
open scoped Classical
noncomputable section

/-- An ordered family of disjoint fibre blocks invariant under the return
permutation yields a periodic tuple word of its prescribed composition. At
each finite time take the coordinate images of the blocks. Injectivity preserves
sizes and disjointness, a physical orbit point gives the common intersection,
and block preservation supplies the cyclic matching at every edge. Source:
Manning (1971), pp.218–219, reverse word/fibre-family correspondence. -/
def invariantBlocksPeriodicWord {A X : Type*} [DecidableEq A] {N r m : ℕ}
    (R : Fin N → Set X) (T : Matrix (Fin N) (Fin N) ℤ)
    (c : Composition r) (hm : 0 < m) (l : Fin m → A → Fin N)
    (hl : ∀ t, Function.Injective (l t)) (x : Fin m → X)
    (hx : ∀ t a, x t ∈ R (l t a)) (g : Fin m → A ≃ A)
    (hedge : ∀ t a, T (l t a) (l (nextTime hm t) (g t a)) = 1)
    (S : Fin c.length → Finset A) (hne : ∀ k, (S k).Nonempty)
    (hcard : ∀ k, (S k).card = c.blocksFun k)
    (hdis : Pairwise fun k j ↦ Disjoint (S k) (S j))
    (hinv : ∀ t k, (S k).image (g t) = S k) : PeriodicWord R T c hm := by
  classical
  let w : Fin m → Alphabet R c := fun t ↦ ⟨fun k ↦ (S k).image (l t), by
    refine ⟨fun k ↦ (hne k).image _, ?_, ?_, ?_⟩
    · intro k
      rw [Finset.card_image_of_injective _ (hl t), hcard k]
    · intro k j hkj
      exact (Finset.disjoint_image (hl t)).mpr (hdis hkj)
    · refine ⟨x t, ?_⟩
      intro k i hi
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
      exact hx t a⟩
  refine ⟨w, ?_⟩
  intro t k
  exact blockMatching_image_perm T (l t) (l (nextTime hm t)) (hl t)
    (hl (nextTime hm t)) (g t) (S k) (hinv t k) (fun a _ ↦ hedge t a)

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
