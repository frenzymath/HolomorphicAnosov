import HolomorphicAnosov.Topology.BasedHomotopyUniqueness
import HolomorphicAnosov.Topology.BasedMapsEqOfHomotopicAbelian
import HolomorphicAnosov.Topology.CWAsphericalCompositeHomotopy
import HolomorphicAnosov.Topology.Franks.PointedMapComposition
import HolomorphicAnosov.Topology.CWPointVertexRefinement
import HolomorphicAnosov.Topology.CWVertexBasedHomomorphismRealization
import HolomorphicAnosov.Topology.RealTorusCoordinateCWStructure
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Topology.TorusCoordinateCover
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Recognition of the homotopy type of a real torus

Source: Allen Hatcher, *Algebraic Topology*, K(G,1) definition p. 87,
Example 1B.5 p. 88, Proposition 1B.9 and Theorem 1B.8 pp. 90–91;
fundamental-group transport: Proposition 1.18 and Lemma 1.19 pp. 37–38.
The DAG node is `topo.aspherical_torus_recognition`.
-/

universe u v w

namespace HolomorphicAnosov.Topology

open CategoryTheory

/-- A connected, locally path-connected, semilocally simply connected space of CW
homotopy type, with contractible universal cover and fundamental group `ℤ^r`,
is genuinely homotopy equivalent to the real torus of dimension `r`.

The witnesses `K` and `hmodel` unpack CW homotopy type using Mathlib's actual CW
structure on all of `K` and a homotopy equivalence with the original space `X`.
The local loop condition `hsemi` says every loop in a sufficiently small open
neighborhood is endpoint-fixed nullhomotopic in `X`, not necessarily in that neighborhood.
The supplied covering `p` is surjective, and its total space `E` is contractible;
it is therefore a universal cover, rather than an arbitrary possibly empty covering.
The chosen point `x₀` specifies the fundamental group. `Multiplicative` only converts
the additive group `Fin r → ℤ` to Mathlib's multiplicative group convention.
The conclusion is the existence of continuous inverse maps up to jointly continuous
homotopies, not a condition on their induced group maps. No CW structure on `X`,
finite CW model, compactness, dimension bound, or Hausdorffness of `X` is assumed.
The zero-dimensional torus is included.

Source: Hatcher, *Algebraic Topology*, pp. 87–91 and pp. 37–38 as above;
local source `literature/hatcher-at.pdf` and its extracted text.

Natural-language proof (the complete current DAG proof, relative to its named source
and Mathlib prerequisites; the Stage2 proof is deliberately postponed):

Step 1: Choose a connected Hausdorff CW homotopy model K with continuous maps e:K→X and a:X→K and
jointly continuous homotopies ae~id_K and ea~id_X. This is the stated CW homotopy type, with
genuine inverse maps. X is path connected because it is connected and locally path connected. K is
path connected: join e(k) to e(k′) in X, apply a, and join the two endpoints to k,k′ by the traces
of ae~id_K. In particular K is nonempty and has a zero cell; a nonempty CW complex cannot have a
least positive cell dimension since that cell has a nonempty attaching sphere mapping into lower
cells. Choose a zero-cell point k0 and put x0=e(k0). Express the given group isomorphism as
α:π1(X,x0)≃Z^r; if it was initially at another basepoint, conjugate along a path to x0.
Concatenation with that path and its reverse gives mutually inverse basepoint-change maps. The
genuine homotopy equivalence e induces eπ:π1(K,k0)≃π1(X,x0), by the fundamental-groupoid
equivalence and its fully faithful endomorphism equivalence. Thus no assumption that a(x0)=k0 is
made.

Step 2: Let T=UnitAddTorus(Fin r) and E_r=Fin r→R. The coordinate-cell theorem gives T its
Hausdorff finite CW structure with zero cell 0. Define q:E_r→T by q(v)_i=[v_i]. Here is its
covering verification, rather than an unstated extra output of the winding theorem. Each
coordinate quotient is an additive quotient covering by the discreteness of integer multiples of
1, hence continuous, surjective and open. Their product is an open quotient map. The translation
subgroup D=Fin r→zmultiples(1:R) acts coordinatewise continuously, and q(v)=q(w) holds exactly
when v−w∈D, by the coordinate quotient-cover orbit condition. For each v choose coordinate
neighborhoods U_i on which the coordinate-cover disjointness condition says (g_i+U_i)∩U_i≠∅
implies g_i=0. The finite product U is a neighborhood of v, and (g+U)∩U≠∅ implies all g_i=0. Thus
the quotient-cover constructor gives the additive product quotient covering, hence the covering
map q. E_r is a real vector space, so it is contractible and simply connected; q is therefore a
surjective universal covering. In the empty product r=0 all orbit/disjointness claims are
empty-coordinate equalities and q is the singleton identity. The winding theorem gives
ω:π1(T,0)≃Z^r. Also T is path connected: for z choose v with q(v)=z and project the path t↦tv from
0 to z.

Step 3: Set θ=ω⁻¹∘α∘eπ:π1(K,k0)≃π1(T,0). Apply the generic vertex-based realization theorem with
source K and target T, its covering q and θ, obtaining a continuous f:K→T with f(k0)=0 and f_*=θ.
Apply it a second time with source T, its zero cell 0, target the original X, its stated
contractible universal cover and the homomorphism eπ∘θ⁻¹, obtaining a continuous g:T→X with
g(0)=x0 and g_*=eπ∘θ⁻¹. Both source basepoints are zero cells; no vertex refinement of a(x0) or
universal-cover transfer to K is used. Both covers are surjective and contractible, and both
target spaces are path connected as required.

Step 4: The based maps gf,e:(K,k0)→(X,x0) induce the same homomorphism, since
(gf)_*=g_*f_*=eπθ⁻¹θ=eπ=e_*. Apply based uniqueness to CW source K and the original universal
cover of X, giving a jointly continuous homotopy gf~e. Put u=fa:X→T. Postcompose/precompose this
homotopy with a to get gu=gfa~ea, and concatenate with ea~id_X. Hence gu~id_X. These are genuine
homotopies of continuous maps, constructed by the homotopy-composition and concatenation
primitives.

Step 5: Correct u to a based map u0(x)=u(x)−u(x0). Choose w∈E_r with q(w)=u(x0). The path
c(t)=q(−tw) goes from 0 to −u(x0), and J(t,x)=u(x)+c(t) is a jointly continuous homotopy from u to
u0. Coordinate real multiplication, quotient projection and product continuity give continuity of
c; continuous addition gives continuity of J, and continuous subtraction gives continuity of u0.
It satisfies u0(x0)=0. Thus gu0~gu~id_X, by reversing J and composing with g, then concatenating
with the preceding homotopy. This construction still works when r=0, with its constant paths.

Step 6: Both gu0 and id_X are based at x0, although their displayed homotopy need not fix x0.
Naturality of homotopicMapsNatIso says their induced endomorphisms differ by conjugation with the
basepoint trace loop. The group π1(X,x0) is abelian through α, so this conjugation is the
identity: for every class β the naturality equation is (gu0)_*(β)h=hβ, whence (gu0)_*(β)=β by
commutativity and cancellation. By induced-map composition, g_*∘(u0)_*=id. Since g_*=eπθ⁻¹ is an
isomorphism, (u0)_*=g_*⁻¹, and therefore (u0g)_*=id on π1(T,0). Apply based uniqueness with CW
source T and the covering q of T to the based maps u0g,id_T. It gives a jointly continuous
homotopy u0g~id_T. Together with gu0~id_X the continuous maps u0:X→T and g:T→X are genuine
homotopy inverses, which proves X≃ₕT. The conclusion is not merely an isomorphism of groups and
uses no extra premise on X.
-/
theorem aspherical_torus_recognition
    (X : Type u) [TopologicalSpace X] [ConnectedSpace X] [LocallyPathConnectedSpace X]
    (_hsemi : ∀ x : X, ∃ U : Set X, x ∈ U ∧ IsOpen U ∧
      ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x))
    (K : Type v) [TopologicalSpace K] [T2Space K]
    [_root_.Topology.CWComplex (Set.univ : Set K)]
    (hmodel : Nonempty (ContinuousMap.HomotopyEquiv X K))
    (E : Type w) [TopologicalSpace E] [ContractibleSpace E]
    (p : E → X) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (x₀ : X) (r : ℕ)
    (hpi : Nonempty (FundamentalGroup X x₀ ≃* Multiplicative (Fin r → ℤ))) :
    Nonempty (ContinuousMap.HomotopyEquiv X (UnitAddTorus (Fin r))) := by
  classical
  have : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  let q := coordinateProjection r
  have hq : IsCoveringMap q := (coordinateProjection_cover r).isCoveringMap
  have hq_surjective : Function.Surjective q := (coordinateProjection_cover r).surjective
  have hq_zero : q 0 = 0 := map_zero q
  obtain ⟨α⟩ := hpi
  obtain ⟨ω, _⟩ := torus_pi1_standard_winding r
  obtain ⟨h⟩ := hmodel
  let k₀ : K := h.toFun x₀
  let : PathConnectedSpace K := {
    nonempty := ⟨k₀⟩
    joined := by
      intro k₁ k₂
      let p₁ : Path (h.invFun k₁) (h.invFun k₂) := PathConnectedSpace.somePath _ _
      let q₁ := p₁.map h.toFun.continuous
      exact ⟨(h.right_inv.some.evalAt k₁).symm.trans
        (q₁.trans (h.right_inv.some.evalAt k₂))⟩ }
  let : ConnectedSpace K := PathConnectedSpace.connectedSpace
  obtain ⟨new, _, _, _, ⟨r₀, hrvertex⟩, _, _, _, _⟩ :=
    cw_point_vertex_refinement K inferInstance k₀
  let : _root_.Topology.CWComplex (Set.univ : Set K) := new
  let : _root_.Topology.RelCWComplex (Set.univ : Set K) ∅ :=
    @_root_.Topology.CWComplex.instRelCWComplex K _ Set.univ new
  have hkzero : k₀ ∈
      (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set K) 0 : Set K) := by
    let χr := @_root_.Topology.CWComplex.map K _ Set.univ new 0 r₀
    have hs : (0 : Fin 0 → ℝ) ∈ χr.source := by
      simp [χr, @_root_.Topology.CWComplex.source_eq K _ Set.univ new 0 r₀]
    have hmem : χr 0 ∈ χr.target := χr.map_source hs
    have hrvertex' : χr.target = {k₀} := by simpa [χr] using hrvertex
    rw [hrvertex'] at hmem
    have hrpt : χr 0 = k₀ := Set.mem_singleton_iff.mp hmem
    apply _root_.Topology.RelCWComplex.openCell_subset_skeleton 0 r₀
    rw [_root_.Topology.RelCWComplex.openCell_zero_eq_singleton]
    apply Set.mem_singleton_iff.mpr
    convert hrpt.symm using 1
    exact congrArg χr (Subsingleton.elim _ _)
  obtain ⟨_, cw, hcw⟩ := real_torus_coordinate_cw_structure r
  let : _root_.Topology.CWComplex (Set.univ : Set (UnitAddTorus (Fin r))) := cw
  obtain ⟨_, index, _, hvertex, _⟩ := hcw
  have hzero : (0 : UnitAddTorus (Fin r)) ∈
      (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set (UnitAddTorus (Fin r))) 0 :
        Set (UnitAddTorus (Fin r))) := by
    apply _root_.Topology.RelCWComplex.openCell_subset_skeleton 0 (index 0 ⟨∅, rfl⟩)
    rw [hvertex]
    exact Set.mem_singleton 0
  let x₁ : X := h.invFun k₀
  let F := FundamentalGroupoidFunctor.equivOfHomotopyEquiv h.symm
  let eπ : FundamentalGroup K k₀ ≃* FundamentalGroup X x₁ :=
    F.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk k₀)
  let pX : Path x₁ x₀ := PathConnectedSpace.somePath _ _
  let α₁ : FundamentalGroup X x₁ ≃* Multiplicative (Fin r → ℤ) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath pX).trans α
  let θ : FundamentalGroup K k₀ ≃* FundamentalGroup (UnitAddTorus (Fin r)) 0 :=
    eπ.trans (α₁.trans ω.symm)
  obtain ⟨f, hf, hfπ⟩ := cw_vertex_based_homomorphism_realization
    k₀ hkzero (0 : UnitAddTorus (Fin r)) q hq hq_surjective θ.toMonoidHom
  obtain ⟨g, hg, hgπ⟩ := cw_vertex_based_homomorphism_realization
    (0 : UnitAddTorus (Fin r)) hzero x₁ p hp hsurj (θ.symm.trans eπ).toMonoidHom
  have hcompπ : FundamentalGroup.mapOfEq (g.comp f) ((congrArg g hf).trans hg) =
      FundamentalGroup.mapOfEq h.invFun rfl := by
    rw [← HolomorphicAnosov.FranksPointedTransport.mapOfEq_comp f g hf hg, hfπ, hgπ]
    ext γ
    change eπ (θ.symm (θ γ)) = _
    rw [θ.symm_apply_apply]
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  obtain ⟨Hgf⟩ := cw_map_based_homotopy_uniqueness
    k₀ x₁ p hp hsurj (g.comp f) h.invFun ((congrArg g hf).trans hg) rfl hcompπ
  let u : C(X, UnitAddTorus (Fin r)) := f.comp h.toFun
  let Hu : (g.comp u).Homotopic (ContinuousMap.id X) := by
    exact ⟨(Hgf.toHomotopy.comp (ContinuousMap.Homotopy.refl h.toFun)).trans h.left_inv.some⟩
  let c := PathConnectedSpace.somePath (0 : UnitAddTorus (Fin r)) (-u x₁)
  let u₀ : C(X, UnitAddTorus (Fin r)) :=
    ⟨fun x ↦ u x - u x₁, u.continuous.sub continuous_const⟩
  have hu₀ : u₀ x₁ = 0 := sub_self _
  have Hcorr : u.Homotopy u₀ := by
    exact {
      toFun := fun tx ↦ u tx.2 + c tx.1
      continuous_toFun := (u.continuous.comp continuous_snd).add
        (c.continuous.comp continuous_fst)
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp [u₀, sub_eq_add_neg] }
  have Hleft : (g.comp u₀).Homotopic (ContinuousMap.id X) := by
    exact ⟨((ContinuousMap.Homotopy.refl g).comp Hcorr.symm).trans Hu.some⟩
  have huπ : FundamentalGroup.mapOfEq u₀ hu₀ = (α₁.trans ω.symm).toMonoidHom := by
    obtain ⟨H⟩ := Hleft
    have heq := based_maps_eq_of_homotopic_abelian x₁ x₁
      (g.comp u₀) (ContinuousMap.id X) ((congrArg g hu₀).trans hg) rfl H
      (fun a b ↦ α₁.injective (by
        change α₁ (a * b) = α₁ (b * a)
        rw [map_mul, map_mul, mul_comm]))
    rw [← HolomorphicAnosov.FranksPointedTransport.mapOfEq_comp u₀ g hu₀ hg,
      hgπ] at heq
    ext γ
    apply (ω.trans α₁.symm).injective
    have hγ := DFunLike.congr_fun heq γ
    have hid : FundamentalGroup.mapOfEq (ContinuousMap.id X) rfl γ = γ := by
      rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
      induction γ using Quotient.inductionOn with
      | h γ => rfl
    have hγ' : (ω.trans α₁.symm) ((FundamentalGroup.mapOfEq u₀ hu₀) γ) = γ := by
      simpa [θ] using hγ.trans hid
    calc
      (ω.trans α₁.symm) ((FundamentalGroup.mapOfEq u₀ hu₀) γ) = γ := hγ'
      _ = (ω.trans α₁.symm) ((α₁.trans ω.symm).toMonoidHom γ) := by
        simp only [MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  have hinverse : (FundamentalGroup.mapOfEq u₀ hu₀).comp
      (FundamentalGroup.mapOfEq g hg) =
        MonoidHom.id (FundamentalGroup (UnitAddTorus (Fin r)) 0) := by
    rw [huπ, hgπ]
    ext γ
    simp [θ]
  obtain ⟨Hright⟩ := cw_aspherical_composite_homotopy
    (0 : UnitAddTorus (Fin r)) x₁ q hq hq_surjective g u₀ hg hu₀ hinverse
  exact ⟨{toFun := u₀
          invFun := g
          left_inv := Hleft
          right_inv := ⟨Hright.toHomotopy⟩}⟩


end HolomorphicAnosov.Topology
