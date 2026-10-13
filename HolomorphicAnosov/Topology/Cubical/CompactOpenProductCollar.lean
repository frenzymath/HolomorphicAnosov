import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.Compactness.Compact

open Set Metric Topology _root_.Topology
namespace HolomorphicAnosov.Cubical

/-- A product neighborhood with compact central factor can be uniformly shrunk
inside any open neighborhood of its zero section.

Proof: Pull the prescribed open set back through the open embedding. The tube
lemma gives one neighborhood of zero whose product with the entire compact
factor lies in that inverse image. Choose a positive-radius ball in it.
The open embedding restricts to a homeomorphism onto its image, and scalar
multiplication identifies that ball with the unit ball while preserving zero.
Source: Munkres, Topology, second edition, §26, tube lemma; Hatcher,
Algebraic Topology, Appendix A.3–A.4, p.522, shrinking a collar neighborhood. -/
theorem compact_open_product_collar
    {X K E : Type*} [TopologicalSpace X] [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : K × E → X) (hF : IsOpenEmbedding F)
    (O : Set X) (hO : IsOpen O) (hzero : ∀ k, F (k, 0) ∈ O) :
    ∃ V : Set X, IsOpen V ∧ V ⊆ O ∧ (∀ k, F (k, 0) ∈ V) ∧
      ∃ e : V ≃ₜ (K × ball (0 : E) 1),
        e '' {x : V | ∃ k, F (k, 0) = x.val} =
          univ ×ˢ {⟨0, mem_ball_self zero_lt_one⟩} := by
  obtain ⟨s, t, hs, ht, hKs, hzt, hst⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set K)) (isCompact_singleton (x := (0 : E)))
    (hO.preimage hF.continuous) (by
      rintro ⟨k, v⟩ ⟨_, hv⟩
      have hv' : v = 0 := hv
      change F (k, v) ∈ O
      rw [hv']
      exact hzero k)
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.mp ht 0 (hzt (mem_singleton 0))
  let P : Set (K × E) := univ ×ˢ ball 0 r
  let V : Set X := F '' P
  let scale : ball (0 : E) 1 ≃ₜ ball (0 : E) r :=
    (OpenPartialHomeomorph.unitBallBall (0 : E) r hr).toHomeomorphSourceTarget
  let prod : P ≃ₜ (K × ball (0 : E) r) :=
    (Homeomorph.Set.prod univ (ball 0 r)).trans
      ((Homeomorph.Set.univ K).prodCongr (Homeomorph.refl _))
  let e : V ≃ₜ (K × ball (0 : E) 1) :=
    (hF.isEmbedding.homeomorphImage P).symm.trans
      (prod.trans ((Homeomorph.refl K).prodCongr scale.symm))
  have hesymm (k : K) :
      (e.symm (k, ⟨0, mem_ball_self zero_lt_one⟩)).val = F (k, 0) := by
    change F (k, r • (0 : E) + 0) = F (k, 0)
    simp
  refine ⟨V, hF.isOpenMap P (isOpen_univ.prod isOpen_ball), ?_, ?_, e, ?_⟩
  · rintro x ⟨⟨k, v⟩, ⟨_, hv⟩, rfl⟩
    exact hst ⟨hKs (mem_univ k), hrt hv⟩
  · intro k
    exact ⟨(k, 0), ⟨mem_univ k, mem_ball_self hr⟩, rfl⟩
  · ext z
    constructor
    · rintro ⟨x, ⟨k, hk⟩, rfl⟩
      have hx : x = e.symm (k, ⟨0, mem_ball_self zero_lt_one⟩) :=
        Subtype.ext (hk.symm.trans (hesymm k).symm)
      rw [hx, e.apply_symm_apply]
      exact ⟨mem_univ _, rfl⟩
    · rintro ⟨_, hz⟩
      have hz' : z.2 = ⟨0, mem_ball_self zero_lt_one⟩ := hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      refine ⟨z.1, ?_⟩
      simpa only [← hz'] using (hesymm z.1).symm

end HolomorphicAnosov.Cubical
