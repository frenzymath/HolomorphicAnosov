import HolomorphicAnosov.Topology.CairnsNormalizedCircleGap
import HolomorphicAnosov.Topology.Plane.CairnsConvexStarSectorExtension

/-!
# Cairns's literal residual-star recurrence

Source: Cairns (1951), §3(D,E), pp.862–863, §4(A–C), pp.863–865, especially
(4.3) and (4.4). This module records first-contact choices and constructs the
fronts, stars, affine front maps, radial patch maps and successive glued maps.
No continuity, injectivity, openness, cell, shrinking or exhaustion property
is a field. The existence of these choices at every stage is a theorem, not
part of the input to the bounded-component extension theorem.
-/

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar

namespace CairnsRefinement

/-- Actual complementary components, rather than angular representatives of
them, index the simultaneous additions in Cairns (4.3). -/
def ResidualComponent (S : Set Circle) :=
  {G : Set Circle // ∃ x ∈ Sᶜ, connectedComponentIn Sᶜ x = G}

/-- Raw geometric choices for the first perpendicular contact of one original
Cairns sector. Its front and star are computed below, not freely specified. -/
structure StarChoice (σ : Circle → ℂ) (a : Set ℂ) (g : CairnsCircleGap) where
  sector : Set ℂ
  component : ∃ x ∈ a \ openSegment ℝ (σ g.first) (σ g.last),
    connectedComponentIn (a \ openSegment ℝ (σ g.first) (σ g.last)) x = sector
  frontier_subset : frontier sector ⊆
    segment ℝ (σ g.first) (σ g.last) ∪ σ '' g.closedArc
  sign : ℝ
  sign_eq : sign = 1 ∨ sign = -1
  radius : ℝ
  radius_pos : 0 < radius
  contactParameter : I
  contact_pos : 0 < (contactParameter : ℝ)
  contact_lt_one : (contactParameter : ℝ) < 1
  first_contact :
    (σ g.first + σ g.last) / 2 + radius • (sign • (Complex.I * (σ g.last - σ g.first))) =
      σ (g.parameter contactParameter)
  ray_inside : ∀ t ∈ Ioo (0 : ℝ) radius,
    (σ g.first + σ g.last) / 2 + t • (sign • (Complex.I * (σ g.last - σ g.first))) ∈
      sector

namespace StarChoice

variable {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}

/-- The midpoint of the old chord, the center of the literal source sweep. -/
noncomputable def center (_b : StarChoice σ a g) : ℂ := (σ g.first + σ g.last) / 2

/-- The retained first perpendicular contact on the original residual arc. -/
noncomputable def contact (b : StarChoice σ a g) : ℂ := σ (g.parameter b.contactParameter)

/-- The first closed half of the original labeled boundary arc. -/
def firstHalf (b : StarChoice σ a g) : Set ℂ :=
  (fun t : I ↦ σ (g.parameter t)) '' {t | t ≤ b.contactParameter}

/-- The second closed half of the original labeled boundary arc. -/
def lastHalf (b : StarChoice σ a g) : Set ℂ :=
  (fun t : I ↦ σ (g.parameter t)) '' {t | b.contactParameter ≤ t}

/-- The original Case I/II convex front, with both halves joined at first contact. -/
noncomputable def front (b : StarChoice σ a g) : Set ℂ :=
  halfFront b.center b.contact (σ g.first) b.firstHalf b.sector ∪
    halfFront b.center b.contact (σ g.last) b.lastHalf b.sector

/-- The original open star, including the open seam between its two halves. -/
noncomputable def sourceStar (b : StarChoice σ a g) : Set ℂ :=
  halfStar b.center b.contact (σ g.first) b.firstHalf b.sector ∪
    halfStar b.center b.contact (σ g.last) b.lastHalf b.sector ∪
    openSegment ℝ b.center b.contact

/-- Real affine coordinates on a contact-free front chord. The angular
parameters specify its endpoints; the separate scalar specifies the point. -/
def FrontCoordinate (b : StarChoice σ a g) (z : ℂ) (w : I × I × I) : Prop :=
  (σ (g.parameter w.1), σ (g.parameter w.2.1)) ∈
    gapPairs (fun t ↦ σ (g.parameter t)) (b.front ∩ range σ) ∧
  z = (1 - (w.2.2 : ℝ)) • σ (g.parameter w.1) +
    (w.2.2 : ℝ) • σ (g.parameter w.2.1)

/-- Prescribed circle values, followed by literal affine front-chord values.
Zero outside these contact/chord branches is only a totalization convention. -/
noncomputable def frontMap (b : StarChoice σ a g) (h : (range σ) ≃ₜ Circle)
    (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ range σ then (h ⟨z, hz⟩ : ℂ)
    else if hw : ∃ w, b.FrontCoordinate z w then
      let w := Classical.choose hw
      (1 - (w.2.2 : ℝ)) • (h ⟨σ (g.parameter w.1), ⟨g.parameter w.1, rfl⟩⟩ : ℂ) +
        (w.2.2 : ℝ) • (h ⟨σ (g.parameter w.2.1), ⟨g.parameter w.2.1, rfl⟩⟩ : ℂ)
    else 0

/-- The original target midpoint of the images of the old chord endpoints. -/
noncomputable def targetCenter (_b : StarChoice σ a g) (h : (range σ) ≃ₜ Circle) : ℂ :=
  ((h ⟨σ g.first, ⟨g.first, rfl⟩⟩ : ℂ) + (h ⟨σ g.last, ⟨g.last, rfl⟩⟩ : ℂ)) / 2

/-- The target front is the image of the actual source front under its affine map. -/
noncomputable def targetFront (b : StarChoice σ a g) (h : (range σ) ≃ₜ Circle) : Set ℂ :=
  b.frontMap h '' b.front

/-- The literal target sweep specified in Cairns §4, before its topological
properties are proved. The prescribed boundary homeomorphism may reverse order. -/
noncomputable def targetStar (b : StarChoice σ a g) (h : (range σ) ≃ₜ Circle) : Set ℂ :=
  openStar (h ⟨σ g.first, ⟨g.first, rfl⟩⟩ : ℂ)
    (h ⟨σ g.last, ⟨g.last, rfl⟩⟩ : ℂ)
    (h ⟨b.contact, ⟨g.parameter b.contactParameter, rfl⟩⟩ : ℂ)
    (b.targetCenter h) (b.targetFront h)

/-- Literal source-sweep coordinates; uniqueness away from the center is a
conclusion of the existing star theorem, not an additional chosen field. -/
def RadialCoordinate (b : StarChoice σ a g) (z : ℂ) (w : ℂ × I) : Prop :=
  w.1 ∈ b.front ∧ z = (1 - (w.2 : ℝ)) • b.center + (w.2 : ℝ) • w.1

/-- The radial patch: original contacts have their prescribed value, the source
center maps to the target center, and every sweep ray is mapped affinely. -/
noncomputable def patchMap (b : StarChoice σ a g) (h : (range σ) ≃ₜ Circle)
    (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ range σ then (h ⟨z, hz⟩ : ℂ)
    else if z = b.center then b.targetCenter h
    else if hw : ∃ w, b.RadialCoordinate z w then
      let w := Classical.choose hw
      (1 - (w.2 : ℝ)) • b.targetCenter h + (w.2 : ℝ) • b.frontMap h w.1
    else 0

end StarChoice

/-- One stage consists of its actual filled region and its totalized map.
The target region and contacts are derived from those same data. -/
structure Stage where
  region : Set ℂ
  map : ℂ → ℂ

/-- The target region in Cairns (4.4), the image under that stage's same map. -/
def Stage.target (s : Stage) : Set ℂ := s.map '' s.region

/-- Retained original parameter contacts at this stage. -/
def Stage.contacts (s : Stage) (σ : Circle → ℂ) : Set Circle := σ ⁻¹' closure s.region

/-- Initial choices for an arbitrary supplied chord: both opposite angular
arcs and their actual first-contact sectors. No initial homeomorphism is assumed. -/
structure InitialData (σ : Circle → ℂ) (a : Set ℂ) (p q : Circle) where
  firstGap : CairnsCircleGap
  first_eq : firstGap.first = p
  last_eq : firstGap.last = q
  secondGap : CairnsCircleGap
  second_start : secondGap.start = firstGap.stop
  second_stop : secondGap.stop = firstGap.start + 2 * Real.pi
  firstStar : StarChoice σ a firstGap
  secondStar : StarChoice σ a secondGap

/-- Cairns's first filled region, both stars plus their common open old chord. -/
noncomputable def InitialData.stage {σ a p q} (d : InitialData σ a p q)
    (h : (range σ) ≃ₜ Circle) : Stage := by
  classical
  exact {
    region := d.firstStar.sourceStar ∪ d.secondStar.sourceStar ∪ openSegment ℝ (σ p) (σ q)
    map := fun z ↦ if hz : z ∈ range σ then (h ⟨z, hz⟩ : ℂ)
      else if z ∈ closure d.firstStar.sourceStar then d.firstStar.patchMap h z
      else d.secondStar.patchMap h z }

/-- Choices for every actual old gap. Its outside sector is an actual original
chord component, and its disjointness from the old region selects the outer side.
There are no finiteness, frontier-circle, openness or shrinking requirements. -/
structure StepData (σ : Circle → ℂ) (a : Set ℂ) (s : Stage) where
  gap : ResidualComponent (s.contacts σ) → CairnsCircleGap
  gap_isGap : ∀ i, (gap i).IsGapOf (s.contacts σ)
  gap_arc : ∀ i, (gap i).openArc = i.val
  star : ∀ i, StarChoice σ a (gap i)
  outside : ∀ i, Disjoint (star i).sector s.region

/-- Successor region (4.3), adjoining every open old chord as well as every star;
the map keeps the old values and uses the selected literal radial patch elsewhere. -/
noncomputable def StepData.next {σ a s} (d : StepData σ a s)
    (h : (range σ) ≃ₜ Circle) : Stage := by
  classical
  exact {
    region := s.region ∪ ⋃ i, ((d.star i).sourceStar ∪
      openSegment ℝ (σ (d.gap i).first) (σ (d.gap i).last))
    map := fun z ↦ if z ∈ closure s.region ∪ range σ then s.map z
      else if hi : ∃ i, z ∈ closure (d.star i).sourceStar then
        (d.star (Classical.choose hi)).patchMap h z
      else 0 }

/-- The exact recurrent construction, with its initial data and successive
outside-star choices. The stage equations are construction equations only;
all topological and limiting properties must be proved separately. -/
structure Data (σ : Circle → ℂ) (a : Set ℂ) (p q : Circle)
    (h : (range σ) ≃ₜ Circle) where
  initial : InitialData σ a p q
  stages : ℕ → Stage
  start_eq : stages 0 = initial.stage h
  steps : ∀ j, StepData σ a (stages j)
  next_eq : ∀ j, stages (j + 1) = (steps j).next h

end CairnsRefinement

end HolomorphicAnosov.Topology.Plane
