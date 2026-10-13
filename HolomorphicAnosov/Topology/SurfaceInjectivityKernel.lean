import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.PathConnected

/-!
# Injectivity from overlapping inverse branches and from increasing exhaustions

Source: É. Ghys, *Holomorphic Anosov systems*, Lemma 5.2, printed pp. 599–600.
The two-open-set theorem isolates the common-origin path-lift argument on p. 599;
the exhaustion theorem isolates its final increasing-union passage on p. 600.
DAG node: `ghys.surface_injectivity_kernel`.
-/

namespace HolomorphicAnosov

open unitInterval

/-- Injectivity of a local homeomorphism on the union of two overlapping inverse domains.

Source: Ghys, *Holomorphic Anosov systems*, Lemma 5.2, printed p. 599.

Choose z in the actual source intersection U ∩ V. A local homeomorphism is continuous and open.
Since each restriction is injective and its domain is open, it gives a homeomorphism from that
source domain onto its actual open image: the inverse takes the unique preimage, and the inverse
preimage of an open source subset W is the open image D(W). No covering or global inverse is used.
For x ∈ U and y ∈ V with D(x) = D(y), choose a path in the path-connected common image from D(z)
to that common value. Composing with the two inverse branches gives continuous lifts starting at
z and ending at x and y. They remain in their respective inverse domains throughout.

Hausdorffness of X makes D a separated map, and a local homeomorphism is locally injective.
The uniqueness theorem for continuous lifts over the preconnected path interval therefore makes
the two lifts equal, so their endpoints are equal. The cases where both points lie in the same
source domain follow from its original injectivity. This proves every union membership case.

The source Hausdorff and actual nonempty source overlap assumptions are essential. The doubled
origin line projecting onto ℝ violates the conclusion without Hausdorffness. Two disjoint copies
of ℝ projecting onto ℝ violate it without the source overlap. Neither condition is replaced by
mere image overlap. No Hausdorff condition on Y or nonempty ambient-space instance is assumed. -/
theorem surface_injOn_union_of_pathConnected_image_inter
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {D : X → Y} (hD : IsLocalHomeomorph D) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hDU : Set.InjOn D U) (hDV : Set.InjOn D V)
    (hUV : (U ∩ V).Nonempty) (himage : IsPathConnected (D '' U ∩ D '' V)) :
    Set.InjOn D (U ∪ V) := by
  let : Nonempty X := ⟨hUV.choose⟩
  let eU : OpenPartialHomeomorph X Y :=
    OpenPartialHomeomorph.ofContinuousOpen
      (hDU.toPartialEquiv D U)
      hD.continuous.continuousOn hD.isOpenMap hU
  let eV : OpenPartialHomeomorph X Y :=
    OpenPartialHomeomorph.ofContinuousOpen
      (hDV.toPartialEquiv D V)
      hD.continuous.continuousOn hD.isOpenMap hV
  have cross : ∀ ⦃x y : X⦄, x ∈ U → y ∈ V → D x = D y → x = y := by
    intro x y hx hy hxy
    obtain ⟨z, hzU, hzV⟩ := hUV
    have hzI : D z ∈ D '' U ∩ D '' V :=
      ⟨⟨z, hzU, rfl⟩, ⟨z, hzV, rfl⟩⟩
    have hxyI : D x ∈ D '' U ∩ D '' V :=
      ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy.symm⟩⟩
    have hjoin : JoinedIn (D '' U ∩ D '' V) (D z) (D x) :=
      himage.joinedIn (D z) hzI (D x) hxyI
    obtain ⟨p, hp⟩ := hjoin
    let gU : I → X := fun t => eU.symm (p t)
    let gV : I → X := fun t => eV.symm (p t)
    have hgU_cont : Continuous gU := by
      apply eU.continuousOn_symm.comp_continuous p.continuous
      intro t
      exact (hp t).1
    have hgV_cont : Continuous gV := by
      apply eV.continuousOn_symm.comp_continuous p.continuous
      intro t
      exact (hp t).2
    have hcomp : D ∘ gU = D ∘ gV := by
      funext t
      change eU (eU.symm (p t)) = eV (eV.symm (p t))
      have hptU : p t ∈ eU.target := by
        change p t ∈ D '' U
        exact (hp t).1
      have hptV : p t ∈ eV.target := by
        change p t ∈ D '' V
        exact (hp t).2
      rw [eU.right_inv hptU, eV.right_inv hptV]
    have hstart : gU 0 = gV 0 := by
      change eU.symm (p 0) = eV.symm (p 0)
      have hp0 : p 0 = D z := p.source
      rw [hp0]
      change eU.symm (eU z) = eV.symm (eV z)
      rw [eU.left_inv hzU, eV.left_inv hzV]
    have hpaths : gU = gV :=
      (T2Space.isSeparatedMap D).eq_of_comp_eq hD.isLocallyInjective
        hgU_cont hgV_cont hcomp 0 hstart
    have hend := congr_fun hpaths 1
    change eU.symm (p 1) = eV.symm (p 1) at hend
    have hp1 : p 1 = D x := p.target
    rw [hp1] at hend
    have hu : eU.symm (D x) = x := by
      change eU.symm (eU x) = x
      rw [eU.left_inv hx]
    have hv : eV.symm (D x) = y := by
      rw [hxy]
      change eV.symm (eV y) = y
      rw [eV.left_inv hy]
    exact hu.symm.trans (hend.trans hv)
  intro x hx y hy hxy
  rcases hx with hxU | hxV
  · rcases hy with hyU | hyV
    · exact hDU hxU hyU hxy
    · exact cross hxU hyV hxy
  · rcases hy with hyU | hyV
    · exact (cross hyU hxV hxy.symm).symm
    · exact hDV hxV hyV hxy

/-- A map injective on every stage of a monotone exhaustive sequence is globally injective.

Source: Ghys, *Holomorphic Anosov systems*, increasing-exhaustion conclusion, printed p. 600.

Given arbitrary x and y with D(x) = D(y), the exhaustive union supplies indices m and n containing
x and y, respectively. Monotonicity puts both in Ω(max m n). Injectivity on that stage then gives
x = y. This works for an arbitrary map between arbitrary types; no topology or local inverse is
needed. Empty ambient spaces and empty initial stages need no extra hypotheses, and no uniform
stage is chosen for all points. -/
theorem surface_injective_of_monotone_exhaustion
    {X Y : Type*} {D : X → Y} {Ω : ℕ → Set X}
    (hΩ : Monotone Ω) (hcover : (⋃ n, Ω n) = Set.univ)
    (hinj : ∀ n, Set.InjOn D (Ω n)) : Function.Injective D := by
  intro x y hxy
  have hx : x ∈ ⋃ n, Ω n := by rw [hcover]; trivial
  have hy : y ∈ ⋃ n, Ω n := by rw [hcover]; trivial
  rcases Set.mem_iUnion.mp hx with ⟨m, hxm⟩
  rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
  let k := max m n
  apply hinj k
  · exact hΩ (Nat.le_max_left _ _) hxm
  · exact hΩ (Nat.le_max_right _ _) hyn
  · exact hxy

end HolomorphicAnosov
