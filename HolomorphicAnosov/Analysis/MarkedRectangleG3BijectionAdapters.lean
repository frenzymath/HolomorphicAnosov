import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected


open Set Filter
open scoped _root_.Topology
namespace HolomorphicAnosov
/-- The inclusion of a subset is a local homeomorphism over its ambient interior. -/
theorem subtypeVal_localHomeomorph_interior {X : Type*} [TopologicalSpace X] (K : Set X) :
    IsLocalHomeomorphOn ((↑) : K → X) (Subtype.val ⁻¹' interior K) := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro x hx
  let U : Set K := Subtype.val ⁻¹' interior K
  refine ⟨U, (isOpen_interior.preimage continuous_subtype_val).mem_nhds hx, ?_⟩
  refine ⟨Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal, ?_⟩
  have hr : range (U.domRestrict ((↑) : K → X)) = interior K := by
    ext z
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hz
      exact ⟨⟨⟨z,interior_subset hz⟩,hz⟩,rfl⟩
  rw [hr]
  exact isOpen_interior

/-- A continuous map on a compact set is a covering over those target points
whose preimages lie in its interior and where the ambient map is a local
homeomorphism. This uses finite compact discrete fibres, without a chosen
uniform family of inverse branches. -/
theorem compact_restriction_covering {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] {K : Set X} (hK : IsCompact K)
    {f : X → Y} (hc : ContinuousOn f K) {V : Set Y}
    (hpre : ∀ x ∈ K, f x ∈ V → x ∈ interior K)
    (hloc : IsLocalHomeomorphOn f (interior K)) :
    IsCoveringMapOn (K.domRestrict f) V := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply IsCoveringMapOn.of_isLocalHomeomorphOn hc.domRestrict
  have hcomp := hloc.comp (subtypeVal_localHomeomorph_interior K)
    (show MapsTo ((↑) : K → X) (Subtype.val ⁻¹' interior K) (interior K) from fun _ h ↦ h)
  intro x hx
  exact hcomp x (hpre x x.property hx)
end HolomorphicAnosov

open Function
namespace HolomorphicAnosov
/-- A covering with connected Hausdorff source and nonempty source over a simply
connected locally path connected target is bijective. Lift the identity at one
source point. Uniqueness of local lifts makes its composition with the covering
the identity on the connected source. -/
theorem covering_bijective_of_simplyConnected
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) : Bijective p := by
  classical
  let e : E := Classical.choice inferInstance
  obtain ⟨F,⟨hF0,hF⟩,huniq⟩ := hp.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) (p e) e rfl
  have hleft : F ∘ p = id := by
    apply (T2Space.isSeparatedMap p).eq_of_comp_eq hp.isLocalHomeomorph.isLocallyInjective
      (F.continuous.comp hp.continuous) continuous_id
    · funext x
      exact congrFun hF (p x)
    · exact hF0
  have hl : Function.LeftInverse F p := fun x ↦ congrFun hleft x
  exact ⟨hl.injective,
    fun x ↦ ⟨F x,congrFun hF x⟩⟩
end HolomorphicAnosov

namespace HolomorphicAnosov
/-- An interior local homeomorphism on a compact closure is globally bijective
onto a simply connected target when precisely the interior points map into that
target. The proof identifies the target preimage with the connected interior
and applies the covering criterion and uniqueness of lifts. -/
theorem compact_localHomeomorph_bijOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] {K : Set X} (hK : IsCompact K)
    {f : X → Y} (hc : ContinuousOn f K) {V : Set Y}
    [PreconnectedSpace (interior K)] [Nonempty (interior K)]
    [SimplyConnectedSpace V] [LocallyPathConnectedSpace V]
    (hpre : ∀ x ∈ K, f x ∈ V ↔ x ∈ interior K)
    (hloc : IsLocalHomeomorphOn f (interior K)) : BijOn f (interior K) V := by
  let g : K → Y := K.domRestrict f
  have hcov : IsCoveringMapOn g V :=
    compact_restriction_covering hK hc (fun x hx h ↦ (hpre x hx).mp h) hloc
  let e : (interior K) ≃ₜ (g ⁻¹' V) :=
    { toFun := fun x ↦ ⟨⟨x,interior_subset x.property⟩,(hpre x (interior_subset x.property)).mpr x.property⟩
      invFun := fun x ↦ ⟨x.val.val,(hpre x.val x.val.property).mp x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hbij := covering_bijective_of_simplyConnected
    (hcov.isCoveringMap_restrictPreimage.comp_homeomorph e)
  refine ⟨fun x hx ↦ (hpre x (interior_subset hx)).mpr hx, ?_, ?_⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val (hbij.1 (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) (Subtype.ext hxy))
  · intro y hy
    obtain ⟨x,hx⟩ := hbij.2 ⟨y,hy⟩
    exact ⟨x,x.property,congrArg Subtype.val hx⟩
end HolomorphicAnosov

open Set Metric
namespace HolomorphicAnosov.Analysis.MarkedRectangle
/-- The real part of a holomorphic function continuous on a bounded closure is
bounded above by its boundary bound. Apply maximum modulus to its exponential. -/
theorem re_le_of_boundary {f : ℂ → ℂ} {U : Set ℂ} (hU : Bornology.IsBounded U)
    (hf : DiffContOnCl ℂ f U) {C : ℝ}
    (hC : ∀ z ∈ frontier U, (f z).re ≤ C) {z : ℂ} (hz : z ∈ closure U) :
    (f z).re ≤ C := by
  have he : DiffContOnCl ℂ (fun w ↦ Complex.exp (f w)) U :=
    ⟨fun w hw ↦ (hf.differentiableOn w hw).cexp,
      Complex.continuous_exp.comp_continuousOn hf.continuousOn⟩
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le hU he
    (C := Real.exp C) (fun w hw ↦ by rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (hC w hw)) hz
  rwa [Complex.norm_exp, Real.exp_le_exp] at hbound
end HolomorphicAnosov.Analysis.MarkedRectangle

namespace HolomorphicAnosov.Analysis.MarkedRectangle
/-- Coordinatewise maximum principles confine the image to the closed rectangle;
local openness upgrades this to the open rectangle at every interior point. -/
theorem rectangle_image_of_boundary {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hf : DiffContOnCl ℂ f U) (hlocal : IsLocalHomeomorphOn f U)
    {a b c d : ℝ}
    (hboundary : MapsTo f (frontier U) (Complex.reProdIm (Icc a b) (Icc c d))) :
    MapsTo f (closure U) (Complex.reProdIm (Icc a b) (Icc c d)) ∧
      MapsTo f U (Complex.reProdIm (Ioo a b) (Ioo c d)) := by
  have hclosed : MapsTo f (closure U) (Complex.reProdIm (Icc a b) (Icc c d)) := by
    intro z hz
    have hupper := re_le_of_boundary hbounded hf (fun w hw ↦ (hboundary hw).1.2) hz
    have hlower := re_le_of_boundary hbounded hf.neg
      (C := -a) (fun w hw ↦ by simpa using neg_le_neg (hboundary hw).1.1) hz
    have hmul : DiffContOnCl ℂ (fun w ↦ Complex.I * f w) U := by
      exact hf.const_smul Complex.I
    have hiupper := re_le_of_boundary hbounded hmul.neg
      (C := d) (fun w hw ↦ by simpa using (hboundary hw).2.2) hz
    have hilower := re_le_of_boundary hbounded hmul
      (C := -c) (fun w hw ↦ by simpa using neg_le_neg (hboundary hw).2.1) hz
    exact ⟨⟨neg_le_neg_iff.mp hlower,hupper⟩,
      ⟨by simpa using hilower,by simpa using hiupper⟩⟩
  refine ⟨hclosed,?_⟩
  intro z hz
  have hn : Complex.reProdIm (Icc a b) (Icc c d) ∈ nhds (f z) := by
    rw [← hlocal.map_nhds_eq hz]
    apply Filter.mem_of_superset (hU.mem_nhds hz)
    exact fun w hw ↦ hclosed (subset_closure hw)
  have hi := mem_interior_iff_mem_nhds.mpr hn
  simpa only [Complex.interior_reProdIm,interior_Icc] using hi
end HolomorphicAnosov.Analysis.MarkedRectangle

open Set
namespace HolomorphicAnosov
/-- A holomorphic scalar function with nonvanishing derivative is locally a
homeomorphism on its open domain, by the analytic inverse-function theorem. -/
theorem holomorphic_localHomeomorphOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hder : ∀ z ∈ U, deriv f z ≠ 0) : IsLocalHomeomorphOn f U := by
  apply IsLocalHomeomorphOn.mk
  intro z hz
  have ha := (hf.analyticOnNhd hU) z hz
  have hd := ha.hasStrictDerivAt.hasStrictFDerivAt_equiv (hder z hz)
  exact ⟨hd.toOpenPartialHomeomorph f, hd.mem_toOpenPartialHomeomorph_source, fun _ _ ↦ rfl⟩
end HolomorphicAnosov
namespace HolomorphicAnosov.Analysis.MarkedRectangle
/-- A holomorphic disk map with nonzero derivative and continuous extension,
whose boundary lies precisely outside the interior of a rectangle and inside
its closure, maps the disk bijectively onto that rectangle. Coordinate maximum
principles and the compact covering argument prove the assertion. -/
theorem disk_rectangle_bijOn_of_boundary {f : ℂ → ℂ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hc : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hd : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0)
    (hb : ∀ z ∈ sphere (0 : ℂ) 1,
      f z ∈ Complex.reProdIm (Icc a b) (Icc c d) ∧
      f z ∉ Complex.reProdIm (Ioo a b) (Ioo c d)) :
    BijOn f (ball (0 : ℂ) 1) (Complex.reProdIm (Ioo a b) (Ioo c d)) := by
  let Q := Complex.reProdIm (Ioo a b) (Ioo c d)
  have hopen : IsOpen Q := isOpen_Ioo.reProdIm isOpen_Ioo
  have hconv : Convex ℝ Q := by
    exact ((convex_Ioo a b).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioo c d).linear_preimage Complex.imCLM.toLinearMap)
  have hne : Q.Nonempty := by
    refine ⟨⟨(a+b)/2,(c+d)/2⟩,?_,?_⟩ <;> change _ < _ ∧ _ < _ <;> constructor <;> linarith
  have hloc := holomorphic_localHomeomorphOn isOpen_ball hf hd
  have hmaps := (rectangle_image_of_boundary isOpen_ball isBounded_ball
    (DiffContOnCl.mk_ball hf hc) hloc (by
      intro z hz
      have hz' : z ∈ sphere (0 : ℂ) 1 := by
        simpa [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz
      exact (hb z hz').1)).2
  have hpre : ∀ z ∈ closedBall (0 : ℂ) 1, f z ∈ Q ↔ z ∈ interior (closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    constructor
    · intro hq
      by_contra hnot
      have hs : z ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere]
        exact le_antisymm (mem_closedBall.mp hz) (not_lt.mp hnot)
      exact (hb z hs).2 hq
    · intro hball; exact hmaps hball
  let : ContractibleSpace Q := hconv.contractibleSpace hne
  let : LocallyPathConnectedSpace Q := hopen.locallyPathConnectedSpace
  let : PreconnectedSpace (interior (closedBall (0 : ℂ) 1)) := by
    rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact (isPreconnected_iff_preconnectedSpace).mp (convex_ball (0 : ℂ) 1).isPreconnected
  let : Nonempty (interior (closedBall (0 : ℂ) 1)) := by
    rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact ⟨⟨0,by simp⟩⟩
  have hres := compact_localHomeomorph_bijOn
    (isCompact_closedBall (0 : ℂ) 1) hc hpre (by simpa only [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hloc)
  simpa only [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hres
end HolomorphicAnosov.Analysis.MarkedRectangle
