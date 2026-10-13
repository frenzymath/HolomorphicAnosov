import HolomorphicAnosov.Topology.ENRRetractionRepresentation

/-!
# The section image of a Euclidean neighborhood retract

This implements the compact-image reduction used in Dold, *Fixed point index and
fixed point theorem for Euclidean neighborhood retracts* (1965), (2.3), p.3 and
Theorem (4.1), pp.5–6. The section image has the original Euclidean subspace topology.
The restricted map is the literal composition `s ∘ f ∘ r`.
-/

namespace HolomorphicAnosov.FixedPointIndexInterface

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The ambient Euclidean image of the section of an ENR representation. -/
def ENRRepresentation.sectionImage (e : ENRRepresentation X) : Set (Euclidean e.dimension) :=
  Set.range (fun x ↦ (e.sectionMap x).val)

/-- A point of the section image belongs to the original Euclidean domain. -/
theorem ENRRepresentation.sectionImage_subset_domain (e : ENRRepresentation X) :
    e.sectionImage ⊆ e.domain := by
  rintro _ ⟨x, rfl⟩
  exact (e.sectionMap x).property

/-- The section identifies X with its image, with inverse the original retraction.
The inverse identities follow from `r ∘ s = id` and the defining range witness;
both maps are continuous by the subspace topology. -/
def ENRRepresentation.sectionImageHomeomorph (e : ENRRepresentation X) :
    X ≃ₜ e.sectionImage where
  toFun x := ⟨(e.sectionMap x).val, ⟨x, rfl⟩⟩
  invFun z := e.retraction ⟨z.val, e.sectionImage_subset_domain z.property⟩
  left_inv x := e.retraction_section x
  right_inv z := by
    rcases z with ⟨z, x, rfl⟩
    apply Subtype.ext
    change (e.sectionMap (e.retraction (e.sectionMap x))).val = (e.sectionMap x).val
    exact congrArg Subtype.val (congrArg e.sectionMap (e.retraction_section x))
  continuous_toFun :=
    (continuous_subtype_val.comp e.sectionMap.continuous).subtype_mk _
  continuous_invFun := e.retraction.continuous.comp (continuous_subtype_val.subtype_mk _)

/-- The forward homeomorphism is the original section in ambient coordinates. -/
@[simp] theorem ENRRepresentation.sectionImageHomeomorph_apply_coe
    (e : ENRRepresentation X) (x : X) :
    (e.sectionImageHomeomorph x).val = (e.sectionMap x).val := rfl

/-- Compactness of X makes its section image a compact subset of Euclidean space. -/
theorem ENRRepresentation.isCompact_sectionImage (e : ENRRepresentation X) [CompactSpace X] :
    IsCompact e.sectionImage := by
  exact isCompact_range (continuous_subtype_val.comp e.sectionMap.continuous)

/-- Every retracted map takes its values in the section image, on any local domain.
For compact X this supplies the compact containing set used in Dold (4.1). -/
theorem ENRRepresentation.retractedMap_range_subset_sectionImage
    (e : ENRRepresentation X) (f : C(X, X)) (W : Set X) :
    Set.range (retractedMap e f W) ⊆ e.sectionImage := by
  rintro _ ⟨v, rfl⟩
  exact ⟨f (e.retraction (retractedDomainInclusion e W v)), rfl⟩

/-- The retracted map restricted to the section image, with its image in that same set. -/
def ENRRepresentation.sectionImageMap (e : ENRRepresentation X) (f : C(X, X)) :
    C(e.sectionImage, e.sectionImage) :=
  (⟨e.sectionImageHomeomorph, e.sectionImageHomeomorph.continuous⟩ : C(X, e.sectionImage)).comp
    (f.comp ⟨e.sectionImageHomeomorph.symm, e.sectionImageHomeomorph.symm.continuous⟩)

/-- The restricted map is literally `s ∘ f ∘ r` in Euclidean coordinates. -/
@[simp] theorem ENRRepresentation.sectionImageMap_apply_coe
    (e : ENRRepresentation X) (f : C(X, X)) (z : e.sectionImage) :
    (e.sectionImageMap f z).val =
      (e.sectionMap (f (e.retraction ⟨z.val,
        e.sectionImage_subset_domain z.property⟩))).val := rfl

/-- The section homeomorphism conjugates f to the restricted retracted map. -/
theorem ENRRepresentation.sectionImageMap_conjugacy
    (e : ENRRepresentation X) (f : C(X, X)) :
    (e.sectionImageMap f).comp
        ⟨e.sectionImageHomeomorph, e.sectionImageHomeomorph.continuous⟩ =
      (⟨e.sectionImageHomeomorph, e.sectionImageHomeomorph.continuous⟩ :
        C(X, e.sectionImage)).comp f := by
  apply ContinuousMap.ext
  intro x
  exact congrArg e.sectionImageHomeomorph
    (congrArg f (e.sectionImageHomeomorph.symm_apply_apply x))

/-- The ambient fixed set of the retracted map is exactly the section image of Fix(f).
A fixed point equals `s(f(r(v)))`; applying r makes `r(v)` fixed by f and gives
`v = s(r(v))`. Conversely a section point of a fixed point is fixed by `s ∘ f ∘ r`.
This argument also covers an empty X and Euclidean dimension zero. -/
theorem ENRRepresentation.retracted_fixed_set_eq_image
    (e : ENRRepresentation X) (f : C(X, X)) :
    {v : Euclidean e.dimension | ∃ hv : v ∈ e.domain,
      (e.sectionMap (f (e.retraction ⟨v, hv⟩))).val = v} =
      (fun x ↦ (e.sectionMap x).val) '' {x : X | f x = x} := by
  ext v
  constructor
  · rintro ⟨hv, hfix⟩
    have hs : e.sectionMap (f (e.retraction ⟨v, hv⟩)) = ⟨v, hv⟩ :=
      Subtype.ext hfix
    have hx : f (e.retraction ⟨v, hv⟩) = e.retraction ⟨v, hv⟩ := by
      exact (e.retraction_section _).symm.trans (congrArg e.retraction hs)
    exact ⟨e.retraction ⟨v, hv⟩, hx, by simpa only [hx] using hfix⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(e.sectionMap x).property, ?_⟩
    change (e.sectionMap (f (e.retraction (e.sectionMap x)))).val = (e.sectionMap x).val
    rw [e.retraction_section x, hx]

end HolomorphicAnosov.FixedPointIndexInterface

