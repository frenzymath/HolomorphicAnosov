import HolomorphicAnosov.Topology.CWComplex.AttachmentCells
import HolomorphicAnosov.Topology.CWComplex.AttachmentTower
import HolomorphicAnosov.Topology.CWComplex.DiskAdjunction
import Mathlib.Topology.Maps.Basic

/-! The characteristic-map closed-set test for finite attachment towers,
following Hatcher, Algebraic Topology, Appendix pp.519–520. The proof uses
only the given quotient topology; no Hausdorffness is assumed. -/

noncomputable section
open Set TopCat
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- The old-space map is continuous because it is a coproduct injection followed
by the quotient projection. Source: Hatcher Appendix p.519. -/
theorem continuous_oldInclusion {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    {a : Fin k → C(∂𝔻 n, X)} : Continuous (@oldInclusion n X k a) :=
  continuous_quotient_mk'.comp continuous_inl

/-- Each new characteristic map is a continuous summand inclusion followed by
the quotient projection. Source: Hatcher Appendix p.519. -/
theorem continuous_newCharacteristic {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    {a : Fin k → C(∂𝔻 n, X)} (i : Fin k) : Continuous (@newCharacteristic n X k a i) :=
  continuous_quotient_mk'.comp (continuous_inr.comp (continuous_const.prodMk continuous_id))

/-- Original characteristic maps remain continuous after all subsequent
attachments. Source: Hatcher Appendix p.519. Induct on the original cell label:
zero-cell maps are constant, retained maps compose with the continuous old-space
map, and fresh maps are continuous quotient projections. -/
theorem continuous_characteristic {d : ℕ} {X : TopCat.{u}} {T : Tower d X}
    {n : ℕ} (c : Cell T n) : Continuous (characteristic c) := by
  induction c with
  | point x => exact continuous_const
  | old c ih => exact continuous_oldInclusion.comp ih
  | fresh i => exact continuous_newCharacteristic i

/-- At one finite adjunction, closedness is tested on the old space and each
disk. Source: Hatcher Appendix p.519, quotient topology of an attachment.
Pull back by the quotient projection and use the two coproduct summands. The
disk-summand preimage is a finite union of products of singleton labels with
the closed disk preimages. This also works for an empty family. -/
theorem adjunction_isClosed_iff {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    {a : Fin k → C(∂𝔻 n, X)} (A : Set (adjunction n X k a)) :
    IsClosed A ↔ IsClosed (oldInclusion ⁻¹' A) ∧
      ∀ i : Fin k, IsClosed (newCharacteristic i ⁻¹' A) := by
  constructor
  · intro h
    exact ⟨h.preimage continuous_oldInclusion,
      fun i ↦ h.preimage (continuous_newCharacteristic i)⟩
  · rintro ⟨hX, hD⟩
    apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
    apply isClosed_sum_iff.mpr
    refine ⟨hX, ?_⟩
    change IsClosed ((fun p : Fin k × 𝔻 n ↦ newCharacteristic p.1 p.2) ⁻¹' A)
    have heq : (fun p : Fin k × 𝔻 n ↦ newCharacteristic p.1 p.2) ⁻¹' A =
        ⋃ i : Fin k, ({i} : Set (Fin k)) ×ˢ (newCharacteristic i ⁻¹' A) := by
      ext p
      simp only [mem_preimage, mem_iUnion, mem_prod, mem_singleton_iff]
      constructor
      · intro h
        exact ⟨p.1, rfl, h⟩
      · rintro ⟨i, hi, h⟩
        simpa only [hi] using h
    rw [heq]
    exact isClosed_iUnion_of_finite fun i ↦ isClosed_singleton.prod (hD i)

/-- A subset of a finite disk-attachment tower is closed exactly when its
preimage under every original characteristic map is closed.

Source: Hatcher Appendix pp.519–520, the weak topology of successive disk
attachments. The forward implication is continuity of characteristic maps.
For the converse induct on the tower. Every subset of the initial discrete
space is closed. At a successor, the retained characteristic preimages test
closedness on the old space by induction, and the fresh characteristic
preimages test each new disk. The quotient criterion at one adjunction then
proves closedness. Empty initial spaces, empty cell families and dimension
zero require no additional hypotheses. -/
theorem tower_isClosed_iff {d : ℕ} {X : TopCat.{u}} (T : Tower d X) (A : Set X) :
    IsClosed A ↔ ∀ (n : ℕ) (c : Cell T n), IsClosed (characteristic c ⁻¹' A) := by
  constructor
  · intro h n c
    exact h.preimage (continuous_characteristic c)
  · induction T with
    | points X finite discrete =>
      intro _
      let := discrete
      exact isClosed_discrete A
    | attach T k a ih =>
      intro h
      apply (adjunction_isClosed_iff A).mpr
      refine ⟨?_, ?_⟩
      · apply ih
        intro n c
        exact h n (.old c)
      · intro i
        exact h _ (.fresh i)

end HolomorphicAnosov.FiniteCellAdjunction
