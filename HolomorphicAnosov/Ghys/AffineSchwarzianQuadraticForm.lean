import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! This file defines the scalar Schwarzian, its expression as a quadratic form on a complex curve,
and Möbius scalar germs. (Ghys, §4, p.594; Lyubich, §2.9.1, pp.96–97, formula (2.17); McMullen,
Complex Analysis, p.70) -/

noncomputable section

open Set Filter Topology _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov.Ghys

universe u v

/-- The scalar complex Schwarzian `H‴ / H′ - (3 / 2) * (H″ / H′)^2`. (Lyubich, §2.9.1, formula
(2.17), p.96) -/
def schwarzian (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (deriv (deriv H)) z / deriv H z -
    (3 / 2 : ℂ) * (deriv (deriv H) z / deriv H z) ^ 2

variable {L : Type u} {L' : Type v}
  [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
  [TopologicalSpace L'] [ChartedSpace (ComplexModel 1) L']

/-- A local holomorphic diffeomorphism is an open partial homeomorphism whose forward and inverse
maps are complex smooth on their domains. (Ghys, §4, p.594) -/
def IsHolomorphicCurveLocalMap (h : OpenPartialHomeomorph L L') : Prop :=
  ContMDiffOn (complexModel 1) (complexModel 1) ∞ h h.source ∧
    ContMDiffOn (complexModel 1) (complexModel 1) ∞ h.symm h.target

/-- The scalar coordinate domain where the inverse source chart, local map, and receiving chart can
be composed. (Ghys, §4, p.594) -/
def affineLocalMapDomain (c : OpenPartialHomeomorph L ℂ)
    (h : OpenPartialHomeomorph L L') (d : OpenPartialHomeomorph L' ℂ) : Set ℂ :=
  c.target ∩ c.symm ⁻¹' h.source ∩ (fun z ↦ h (c.symm z)) ⁻¹' d.source

/-- The scalar expression `d ∘ h ∘ c.symm` of a local map in source and receiving coordinates.
(Ghys, §4, p.594) -/
def affineLocalMapExpression (c : OpenPartialHomeomorph L ℂ)
    (h : OpenPartialHomeomorph L L') (d : OpenPartialHomeomorph L' ℂ) : ℂ → ℂ :=
  fun z ↦ d (h (c.symm z))

/-- Admissible Schwarzian coordinates are charts in the specified maximal affine atlases whose
composition is defined at `x` and has nonzero scalar derivative there. (Ghys, §4, p.594;
Lyubich, §2.9.1, p.96) -/
def IsAffineSchwarzianCoordinateAt (A : ComplexAffineStructure L)
    (B : ComplexAffineStructure L') (c : OpenPartialHomeomorph L ℂ)
    (h : OpenPartialHomeomorph L L') (d : OpenPartialHomeomorph L' ℂ) (x : L) : Prop :=
  c ∈ ComplexAffineStructure.maximalAtlas L A ∧
    d ∈ ComplexAffineStructure.maximalAtlas L' B ∧
    IsHolomorphicCurveLocalMap h ∧ x ∈ c.source ∧ x ∈ h.source ∧ h x ∈ d.source ∧
    deriv (affineLocalMapExpression c h d) (c x) ≠ 0

/-- The Schwarzian quadratic form at `x` sends `v` to `S(d ∘ h ∘ c.symm)(c x) * (D c_x v)^2`. (Ghys,
§4, p.594) -/
def schwarzianQuadraticAt (c : OpenPartialHomeomorph L ℂ)
    (h : OpenPartialHomeomorph L L') (d : OpenPartialHomeomorph L' ℂ) (x : L) :
    QuadraticForm ℂ (TangentSpace (complexModel 1) x) :=
  schwarzian (affineLocalMapExpression c h d) (c x) •
    (QuadraticMap.sq (R := ℂ) (A := ℂ)).comp
      (mfderiv (complexModel 1) 𝓘(ℂ) c x).toLinearMap

/-- A scalar germ is Möbius when its finite homogeneous-coordinate expression agrees locally with a
projective transformation induced by a nonsingular matrix. (Ghys, §4, pp.593–594; Demailly, V
§15.A, p.277) -/
def IsMobiusScalarGerm (H : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ m : ComplexMobiusTransformation, ∀ᶠ w in 𝓝 z,
    complexProjectiveLineFinite (H w) = m.apply (complexProjectiveLineFinite w)

end HolomorphicAnosov.Ghys
