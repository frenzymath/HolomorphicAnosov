import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Boundary detection of circle-valued maps on a planar surface

A circle-valued map on a closed planar subset that lifts on its entire
frontier lifts on the whole subset. Tietze extends the boundary argument,
and pasting its exponential outside gives a map on the simply connected
plane. The exponential covering then supplies the lift.
-/

open Set
namespace HolomorphicAnosov.Topology.GallierXu

/-- Boundary arguments detect the obstruction to a real lift on a closed
subset of a simply connected normal space.

Agent-written argument using Bredon I.10.4, pp.30--31, Tietze extension,
and Hatcher §1.3 Proposition 1.33, pp.61--62, the covering-space lifting theorem. Extend the frontier's real
argument to the ambient space. Paste its exponential outside the closed
subset with the given circle map inside. Boundary agreement makes this
continuous. Simply connectedness lifts the ambient map through the real
exponential covering, and restriction gives the required lift.
-/
theorem circle_lift_of_frontier_lift_g9 {X : Type*} [TopologicalSpace X]
    [NormalSpace X] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) (S : Set X) (hS : IsClosed S) (f : C(↥S,Circle))
    (a : C(↥(frontier S),ℝ))
    (ha : ∀ x : ↥(frontier S), Circle.exp (a x) =
      f ⟨x.val,(by simpa only [hS.closure_eq] using frontier_subset_closure x.property)⟩) :
    ∃ b : C(↥S,ℝ), ∀ x, Circle.exp (b x) = f x := by
  classical
  obtain ⟨A,hA⟩ := a.exists_extension isClosed_frontier.isClosedEmbedding_subtypeVal
  let f₀ : X → Circle := fun x ↦ if hx : x ∈ S then f ⟨x,hx⟩ else 1
  have hf₀ (x : ↥S) : f₀ x.val = f x := by simp [f₀,x.property]
  have hfc : ContinuousOn f₀ (closure S) := by
    rw [hS.closure_eq,continuousOn_iff_continuous_domRestrict]
    have he : S.domRestrict f₀ = f := funext hf₀
    rw [he]
    exact f.continuous
  let g : C(X,Circle) := ⟨fun x ↦ Circle.exp (A x),Circle.exp.continuous.comp A.continuous⟩
  have hmatch (x : X) (hx : x ∈ frontier S) : f₀ x = g x := by
    have he : A x = a ⟨x,hx⟩ := congrArg (fun q : C(↥(frontier S),ℝ) ↦ q ⟨x,hx⟩) hA
    have hxS : x ∈ S := by simpa only [hS.closure_eq] using frontier_subset_closure hx
    change f₀ x = Circle.exp (A x)
    rw [he,ha]
    exact hf₀ ⟨x,hxS⟩
  let F : C(X,Circle) := ⟨S.piecewise f₀ g,
    continuous_piecewise hmatch hfc g.continuous.continuousOn⟩
  obtain ⟨B,hB,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts F x₀
    (Complex.arg (F x₀)) (Circle.exp_arg (F x₀))
  refine ⟨⟨fun x ↦ B x.val,B.continuous.comp continuous_subtype_val⟩,fun x ↦ ?_⟩
  have he := congrFun hB.2 x.val
  change Circle.exp (B x.val) = f x
  simpa only [Function.comp_apply,F,ContinuousMap.coe_mk,Set.piecewise_eq_of_mem S f₀ g x.property,
    hf₀ x] using he

/-- Specialization to the complex plane, with its original topology. -/
theorem planar_circle_lift_of_frontier_lift_g9
    (S : Set ℂ) (hS : IsClosed S) (f : C(↥S,Circle))
    (a : C(↥(frontier S),ℝ))
    (ha : ∀ x : ↥(frontier S), Circle.exp (a x) =
      f ⟨x.val,(by simpa only [hS.closure_eq] using frontier_subset_closure x.property)⟩) :
    ∃ b : C(↥S,ℝ), ∀ x, Circle.exp (b x) = f x :=
  circle_lift_of_frontier_lift_g9 0 S hS f a ha

/-- A circle map on a compact embedded space that is constant one at the
ambient frontier lifts whenever the ambient space is simply connected.
Transport to the closed image and apply the frontier lifting theorem with
the constant-zero boundary argument.
-/
theorem circle_lift_of_embedding_frontier_g9
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [T2Space Y] [NormalSpace Y] [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (y₀ : Y) (h : C(X,Y)) (hinj : Function.Injective h) (f : C(X,Circle))
    (hfront : ∀ x, h x ∈ frontier (range h) → f x = 1) :
    ∃ b : C(X,ℝ), ∀ x, Circle.exp (b x) = f x := by
  let e := (h.continuous.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  let f' : C(↥(range h),Circle) := ⟨fun x ↦ f (e.symm x),f.continuous.comp e.symm.continuous⟩
  have hS : IsClosed (range h) := (isCompact_range h.continuous).isClosed
  let a : C(↥(frontier (range h)),ℝ) := ContinuousMap.const _ 0
  have ha (x : ↥(frontier (range h))) : Circle.exp (a x) =
      f' ⟨x.val,hS.frontier_subset x.property⟩ := by
    have he : h (e.symm ⟨x.val,hS.frontier_subset x.property⟩) = x.val :=
      congrArg Subtype.val (e.apply_symm_apply _)
    change Circle.exp 0 = f (e.symm ⟨x.val,hS.frontier_subset x.property⟩)
    rw [Circle.exp_zero,hfront _ (he.symm ▸ x.property)]
  obtain ⟨B,hB⟩ := circle_lift_of_frontier_lift_g9 y₀ (range h) hS f' a ha
  refine ⟨⟨fun x ↦ B (e x),B.continuous.comp e.continuous⟩,fun x ↦ ?_⟩
  simpa only [f',ContinuousMap.coe_mk,e.symm_apply_apply] using hB (e x)

end HolomorphicAnosov.Topology.GallierXu
