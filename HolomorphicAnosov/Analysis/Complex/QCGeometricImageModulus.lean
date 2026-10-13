import HolomorphicAnosov.Analysis.Complex.QCMarkedModelPositive
import HolomorphicAnosov.Analysis.Complex.QCPositiveMarkedModulus
import HolomorphicAnosov.Analysis.Complex.QCGeometricOneModulusEquality

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle

/-- A positively oriented partial homeomorphism carries every compact marked
quadrilateral in its source to a marked quadrilateral. Source: Lehto–Virtanen
I.§3.1, pp.16–17. The conformal source model gives positive cyclic boundary
marks. The compact boundary transport theorem supplies their literal image
parametrization. Confine a homotopy from the source boundary to a small circle
inside its Jordan closure. Composition preserves avoidance by injectivity;
the positive image-circle hypothesis therefore gives winding one for the whole
image boundary. The marked rectangle existence theorem supplies its modulus. -/
theorem qc_geometric_image_marked_modulus
    (g : OpenPartialHomeomorph ℂ ℂ)
    (hpositive : ∀ a : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall a r ⊆ g.source →
      ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
          Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) = (g c - g a) / (‖g c - g a‖ : ℂ)) ∧
        θ 1 = θ 0 + 2 * Real.pi)
    {Q : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hcompact : IsCompact (closure Q)) (hinside : closure Q ⊆ g.source)
    (hmod : HasMarkedConformalModulus Q p m) :
    ∃ m' : ℝ, HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m' := by
  have hgeom := qc_marked_model_geometry hmod hcompact
  have hgc := g.continuousOn.mono hinside
  have hgi := g.injOn.mono hinside
  have hQsrc : Q ⊆ g.source := subset_closure.trans hinside
  have hopen : IsOpen (g '' Q) := g.isOpen_image_of_subset_source hgeom.1 hQsrc
  have hconn : IsConnected (g '' Q) :=
    hgeom.2.1.isConnected.image g (g.continuousOn.mono hQsrc)
  have hbounded : Bornology.IsBounded (g '' Q) :=
    (hcompact.image_of_continuousOn hgc).isBounded.subset (image_mono subset_closure)
  obtain ⟨β,hβ,u,hu,hp⟩ := qc_marked_model_positive hmod hcompact
  let γ : Circle → ℂ := fun z ↦ (β z : ℂ)
  have hγ : _root_.Topology.IsEmbedding γ :=
    _root_.Topology.IsEmbedding.subtypeVal.comp β.isEmbedding
  have hfront : frontier Q = range γ := by
    ext z
    constructor
    · intro hz
      obtain ⟨w,hw⟩ := β.surjective ⟨z,hz⟩
      exact ⟨w,congrArg Subtype.val hw⟩
    · rintro ⟨w,rfl⟩
      exact (β w).property
  obtain ⟨E,hE,hEcl⟩ := qc_positive_boundary_bounded_component Q hgeom.2.1.nonempty
    hgeom.1 hgeom.2.1.isConnected hgeom.2.2 γ hγ hfront β hβ
  obtain ⟨b,hb⟩ := qc_compact_boundary_transport hgeom.1 hcompact hgc hgi hopen
  let β' := β.trans b
  have hβ' : PositiveBoundaryParametrization (g '' Q) β' := by
    apply qc_positive_jordan_boundary g Q hgeom.1 hgc hgi β hβ E hE hEcl β'
      (fun z ↦ hb (β z))
    intro a r hr hball
    exact hpositive a r hr (hball.trans hQsrc)
  apply qc_positive_marked_modulus hopen hconn hbounded
  exact ⟨β',hβ',u,hu,fun i ↦ (hb (β (u i))).trans (congrArg g (hp i))⟩

/-- A one-sided unit modulus bound is exact on every compact quadrilateral.
The preceding orientation transport first guarantees that the image has a
marked modulus. Cyclic relabeling and reciprocal moduli then turn the two
one-sided inequalities into equality. Source: Lehto–Virtanen I.Theorem 5.1. -/
theorem qc_geometric_preserves_marked_modulus
    (g : OpenPartialHomeomorph ℂ ℂ)
    (hpositive : ∀ a : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall a r ⊆ g.source →
      ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
          Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) = (g c - g a) / (‖g c - g a‖ : ℂ)) ∧
        θ 1 = θ 0 + 2 * Real.pi)
    (hBound : ∀ (Q : Set ℂ) (p : Fin 4 → ℂ) (m m' : ℝ),
      IsCompact (closure Q) → closure Q ⊆ g.source →
      HasMarkedConformalModulus Q p m →
      HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m' → m' ≤ m)
    {Q : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hcompact : IsCompact (closure Q)) (hinside : closure Q ⊆ g.source)
    (hmod : HasMarkedConformalModulus Q p m) :
    HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m := by
  obtain ⟨m',hm'⟩ := qc_geometric_image_marked_modulus g hpositive hcompact hinside hmod
  have heq := qc_geometric_one_modulus_equality hBound hcompact hinside hmod hm'
  exact heq ▸ hm'

end HolomorphicAnosov
