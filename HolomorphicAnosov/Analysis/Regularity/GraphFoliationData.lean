import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs

/-!
# Common-radius graph foliation and spatial Hölder data

Source: Hirsch–Pugh–Shub, Invariant Manifolds, §7, printed pp.115–116 (continuous
foliation boxes and intrinsic plaques); Journé (1988), printed pp.187–188
(continuous transverse foliations, leaf graph coordinates and tangent continuity);
de la Llave–Obaya (1999), Definitions2.1/2.5, printed159/162 (finite Hölder norms).
The finite regularity/common-domain hypotheses are those of
analysis.journe_transverse_leaf_polynomial_approximation. This module defines
supplied mathematical data and asserts no regularity theorem.

Each foliation has its OWN atlas. The first leaf jets, but not higher jets, are
jointly continuous; higher spatial jets have uniform bounds. Overlap changes
preserve leaf slices locally. All functions have actual pointwise data, all
inverse charts are actual homeomorphisms, and there are no admitted proofs.
-/

noncomputable section

namespace HolomorphicAnosov
namespace JourneLeafPolynomialApproximation

open Set

/-- The original real Euclidean block, with its Euclidean norm. -/
abbrev Block (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Spatial finite-order Hölder bounds, using actual unnormalized Fréchet derivatives.
Source: the current node's premises and de la Llave–Obaya (1999), Definitions 2.1/2.5.
Order zero includes the value bound; no derivative of order n+1 is required. -/
def HasFiniteHolderBounds {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (α K : ℝ) (f : D → F) (S : Set D) : Prop :=
  ContDiffOn ℝ n f S ∧
    (∀ j : ℕ, j ≤ n → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ K) ∧
    ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤ K * ‖x - y‖ ^ α

/-- One actual common-radius graph box in original ambient linear coordinates.
Source: Journé pp.187–188 and the current node's explicit graph-parametrization premise.
The fixed linear frame need not be an isometry. Its continuous linear inverse is actual data.
Only the first spatial derivative field is required to be jointly continuous. -/
structure GraphBox (d c N n : ℕ) (α : ℝ) (Ω : Set (Block N)) where
  base : Block N
  leafRadius : ℝ
  transverseRadius : ℝ
  leafRadius_pos : 0 < leafRadius
  transverseRadius_pos : 0 < transverseRadius
  frame : (Block d × Block c) ≃L[ℝ] Block N
  graph : Block c → Block d → Block c
  image : Set (Block N)
  image_open : IsOpen image
  image_subset : image ⊆ Ω
  chart : ↥(Metric.ball (0 : Block d) leafRadius ×ˢ
    Metric.ball (0 : Block c) transverseRadius) ≃ₜ ↥image
  chart_formula : ∀ z,
    (chart z).val = base + frame (z.val.1, graph z.val.2 z.val.1)
  graph_continuous : ContinuousOn (fun z : Block d × Block c ↦ graph z.2 z.1)
    (Metric.ball 0 leafRadius ×ˢ Metric.ball 0 transverseRadius)
  first_jet_continuous : ContinuousOn
    (fun z : Block d × Block c ↦ fderiv ℝ (graph z.2) z.1)
    (Metric.ball 0 leafRadius ×ˢ Metric.ball 0 transverseRadius)
  graph_bounds : ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ Metric.ball 0 transverseRadius,
    HasFiniteHolderBounds n α K (graph w) (Metric.ball 0 leafRadius)

/-- The actual ambient parametrization of one plaque; only its ball is used.
Values outside that ball play no role in any hypothesis or conclusion. -/
def GraphBox.plaque {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (w : Block c) (x : Block d) : Block N :=
  b.base + b.frame (x, b.graph w x)

/-- The actual transverse coordinate from the inverse of the same box chart. -/
def GraphBox.transverseLabel {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (a : Block N) (ha : a ∈ b.image) : Block c :=
  (b.chart.symm ⟨a, ha⟩).val.2

/-- The actual tangent range of the plaque at its original graph parameter.
This uses the derivative of the same ambient plaque map, not an independently supplied plane. -/
def GraphBox.tangent {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (a : Block N) (ha : a ∈ b.image) :
    Submodule ℝ (Block N) :=
  let z := (b.chart.symm ⟨a, ha⟩).val
  LinearMap.range (fderiv ℝ (b.plaque z.2) z.1).toLinearMap

/-- A genuine graph-foliation atlas on the open ambient domain.
Source: the continuous-foliation and common-radius graph premises of the current node.
Every overlap preserves the transverse label locally along a plaque. Thus leaf classes are
obtained by finite chains of these actual plaques; the condition excludes branching graphs.
Uniform bounds are local to each box, as required by locally uniform bounds on smaller domains.
No global bound, transverse derivative, or compatibility between the TWO atlases is required. -/
structure GraphFoliation (d c N n : ℕ) (α : ℝ) (Ω : Set (Block N)) where
  Index : Type
  box : Index → GraphBox d c N n α Ω
  cover : ∀ a ∈ Ω, ∃ i : Index, a ∈ (box i).image
  overlap : ∀ (i j : Index)
    (z : ↥(Metric.ball (0 : Block d) (box i).leafRadius ×ˢ
      Metric.ball (0 : Block c) (box i).transverseRadius))
    (hz : ((box i).chart z).val ∈ (box j).image),
    ∃ V : Set (Block d), IsOpen V ∧ z.val.1 ∈ V ∧
      V ⊆ Metric.ball 0 (box i).leafRadius ∧
      ∀ x ∈ V, ∃ hx : (box i).plaque z.val.2 x ∈ (box j).image,
        (box j).transverseLabel ((box i).plaque z.val.2 x) hx =
          (box j).transverseLabel ((box i).chart z).val hz

/-- Complementarity of the actual tangent ranges at every point, in the same ambient space.
All chart choices are quantified; no privileged chart or constant plane is substituted. -/
def AreTransverse {p q n : ℕ} {α : ℝ} {Ω : Set (Block (p + q))}
    (F₁ : GraphFoliation p q (p + q) n α Ω)
    (F₂ : GraphFoliation q p (p + q) n α Ω) : Prop :=
  ∀ (i : F₁.Index) (j : F₂.Index) (a : Block (p + q))
    (h₁ : a ∈ (F₁.box i).image) (h₂ : a ∈ (F₂.box j).image),
    IsCompl ((F₁.box i).tangent a h₁) ((F₂.box j).tangent a h₂)

/-- Uniform spatial Hölder bounds for the original scalar function on every plaque of a box.
The SAME graph parametrizations used in the foliation datum are used for these restrictions. -/
def HasLeafwiseHolderBounds {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (F : GraphFoliation d c N n α Ω) (h : Block N → ℝ) : Prop :=
  ∀ i : F.Index, ∃ K : ℝ, 0 ≤ K ∧
    ∀ w ∈ Metric.ball 0 (F.box i).transverseRadius,
      HasFiniteHolderBounds n α K (h ∘ (F.box i).plaque w)
        (Metric.ball 0 (F.box i).leafRadius)

end JourneLeafPolynomialApproximation
end HolomorphicAnosov
