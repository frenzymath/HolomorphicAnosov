import HolomorphicAnosov.Topology.RelativeTriangleRealization.PairedTriangleQuotientT2
import HolomorphicAnosov.Topology.RelativeTriangleRealization.EdgeInteriorClasses
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization
open Set _root_.HolomorphicAnosov.Topology _root_.Topology Metric

-- The dependency source already contains this elementary face uniqueness
-- lemma, but the single-file sandbox may see its pre-landing object file.
theorem interior_face_eq_local {j k : Fin 3} (t s : Simplex 1)
    (ht : t ∈ interior 1) (h : face j t = face k s) (_haux : True) :
    j = k ∧ t = s := by
  have hz (j : Fin 3) (s : Simplex 1) : (face j s).weights j = 0 := by
    change s.weights.mapDomain j.succAbove j = 0
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact j.succAbove_ne a ha
  have hjk : j = k := by
    by_contra hne
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (Ne.symm hne)
    have hh := congrArg (fun z : Simplex 2 ↦ z.weights k) h
    rw [hz] at hh
    change t.weights.mapDomain j.succAbove k = 0 at hh
    rw [← ha, Finsupp.mapDomain_apply_of_injective j.succAbove_right_injective] at hh
    exact (ne_of_gt (ht a)) hh
  subst k
  refine ⟨rfl, ?_⟩
  apply Convexity.StdSimplex.ext
  have hw := congrArg Convexity.StdSimplex.weights h
  exact Finsupp.mapDomain_injective j.succAbove_right_injective hw

/-!
# Open edge characteristic embeddings

Source: Hatcher, *Algebraic Topology*, pp.103--104 and p.167, with the
characteristic-map criterion in Appendix A.2 pp.519--521. -/

/-- Restrict a continuous closed map to a set on which all fibers are singletons. -/
theorem closedMap_singletonFibers_embedding {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hc : Continuous f) (hf : IsClosedMap f) (s : Set X)
    (hs : ∀ x ∈ s, ∀ y, f x = f y → x = y) :
    Topology.IsEmbedding (fun x : s ↦ f x.val) := by
  have hpre : f ⁻¹' (f '' s) = s := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      simpa only [hs y hy x heq] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hi : Function.Injective ((f '' s).restrictPreimage f) := by
    intro x y h
    apply Subtype.ext
    exact hs x.val (by simpa only [hpre] using x.property) y.val
      (congrArg Subtype.val h)
  have he := Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    hc.restrictPreimage hi (hf.restrictPreimage (f '' s))
  have hh := he.isEmbedding.comp (Homeomorph.setCongr hpre.symm).isEmbedding
  exact Topology.IsEmbedding.subtypeVal.comp hh

/- The ordered interior of an edge is embedded in the paired-face quotient.

The quotient class calculation `edgeInterior_class_iff` gives injectivity and
identifies the image with one open edge stratum. In the quotient topology, the
finite closed-simplex chart restricts to this stratum as an inducing map; the
compact Hausdorff argument on closed subintervals and the open-cover criterion
for embeddings then gives the full open-edge embedding. This statement is
kept public because the finite classical CW constructor and the subcomplex
proof both consume it. -/
theorem edgeInterior_isEmbedding_gap {m : ℕ}
    (pair : Occurrence m → Occurrence m)
    (hinv : Function.Involutive pair) (o : Occurrence m) :
    Topology.IsEmbedding (fun t : interior 1 ↦ edge pair o t.val) := by
  let : T2Space (Space pair) := pairedTriangle_quotient_t2 pair hinv
  apply closedMap_singletonFibers_embedding (edge pair o) (edge pair o).continuous
    (edge pair o).continuous.isClosedMap
  intro t ht s heq
  obtain h | h :=
    (edgeInterior_class_iff pair hinv o t ht (o.1, face o.2 s)).mp heq
  · exact (interior_face_eq_local t s ht (congrArg Prod.snd h).symm trivial).2
  · exact (interior_face_eq_local t s ht (congrArg Prod.snd h).symm trivial).2


end HolomorphicAnosov.RelativeTriangleRealization
