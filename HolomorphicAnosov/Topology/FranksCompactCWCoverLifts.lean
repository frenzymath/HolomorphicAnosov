import HolomorphicAnosov.Topology.ContractibleOpenNeighborhoods
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover
import HolomorphicAnosov.Topology.TorusStandardWinding
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Covering.Quotient
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# Pointed compact-CW covering lifts used by Franks

Source: John Franks, *Anosov Diffeomorphisms* (1970), Proposition (2.1), printed pp.69–70,
`literature/Global analysis, part I.pdf`; covering prerequisites are Hatcher,
*Algebraic Topology*, Proposition A.4 p.522, pp.63–65 and Propositions 1.33–1.34,
1.39, pp.61–62,70–71. This is DAG node `topo.franks_compact_cw_cover_lifts`.

The torus is exactly `UnitAddTorus (Fin n)`, the real coordinate projection is the
coordinatewise quotient `ℝ → ℝ/ℤ`, and no auxiliary universal-cover type is postulated.
The theorem existentially supplies its carrier, topology, continuous projection and covering
proof, simple connectedness and based deck identification. All types retain their native
topologies. The left deck group is the opposite of Mathlib's fundamental group: chronological
prefix concatenation does not invert loops. The monodromy equations fix this convention and the
positive winding sign on the actual cover; an arbitrary abstract group isomorphism would not.
-/

noncomputable section

open Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Topology.FranksCompactCWCoverLifts

universe u



private def coordinateProjection (n : ℕ) : (Fin n → ℝ) →+ UnitAddTorus (Fin n) where
  toFun v i := (v i : UnitAddCircle)
  map_zero' := by ext; simp
  map_add' v w := by ext; simp

private theorem coordinateProjection_kernel (n : ℕ) :
    (coordinateProjection n).ker =
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup := by
  ext v
  change coordinateProjection n v = 0 ↔ v ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
  rw [(Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ v]
  rw [funext_iff]
  change (∀ i, (v i : UnitAddCircle) = 0) ↔
    ∀ i, ((Pi.basisFun ℝ (Fin n)).repr v) i ∈ Set.range (algebraMap ℤ ℝ)
  simp [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]

private theorem coordinate_cover_data (n : ℕ) :
    ∃ (_cov : IsCoveringMap (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)))
      (zero : (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)) ⁻¹'
        {(0 : UnitAddTorus (Fin n))}), (zero : Fin n → ℝ) = 0 := by
  let p := coordinateProjection n
  have hopen : IsOpenQuotientMap p := IsOpenQuotientMap.piMap (fun _ : Fin n ↦
    (QuotientAddGroup.isOpenQuotientMap_mk :
      IsOpenQuotientMap (fun x : ℝ ↦ (x : UnitAddCircle))))
  have hd : DiscreteTopology p.ker := by
    rw [coordinateProjection_kernel]
    exact ZSpan.discreteTopology_pi_basisFun
  have hcov : IsAddQuotientCoveringMap p p.ker :=
    hopen.isQuotientMap.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hd.isDiscrete
  refine ⟨hcov.isCoveringMap, ?_, ?_⟩
  · exact ⟨0, by ext; simp⟩
  · ext; simp



private def straightPath (n : ℕ) (z : Fin n → ℤ) :
    Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)) where
  toFun t i := (t : ℝ) * (z i : ℝ)
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by ext; simp

private def integralPath (n : ℕ) (z : Fin n → ℤ) :
    Path (0 : UnitAddTorus (Fin n)) 0 :=
  ((straightPath n z).map
      (show Continuous (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)) by fun_prop)).cast
    (by ext; simp) (by
      ext i
      exact ((AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨z i, by simp⟩).symm)

private theorem integralPath_formula (n : ℕ) (z : Fin n → ℤ) (t : unitInterval)
    (i : Fin n) : integralPath n z t i =
      (((t : ℝ) * (z i : ℝ) : ℝ) : UnitAddCircle) := by
  change (coordinateProjection n (straightPath n z t)) i = _
  rfl

private theorem integralPath_monodromy (n : ℕ) (z : Fin n → ℤ)
    (cov : IsCoveringMap (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)))
    (zero : (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)) ⁻¹'
      {(0 : UnitAddTorus (Fin n))}) (hzero : zero.val = 0) :
    (cov.monodromy ⟦integralPath n z⟧ zero : Fin n → ℝ) =
      fun i ↦ (z i : ℝ) := by
  let ey : (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)) ⁻¹' {0} :=
    ⟨fun i ↦ (z i : ℝ), by
      ext i
      exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨z i, by simp⟩⟩
  let Γ : Path.Homotopic.Quotient zero.val ey.val :=
    Path.Homotopic.Quotient.cast (⟦straightPath n z⟧ :
      Path.Homotopic.Quotient (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ))) hzero rfl
  let pcont : ContinuousMap (Fin n → ℝ) (UnitAddTorus (Fin n)) :=
    ⟨fun x j ↦ (x j : UnitAddCircle), by fun_prop⟩
  have hm := cov.monodromy_eq_of_map_eq (ex := zero) (ey := ey)
    (γ := (⟦integralPath n z⟧ : Path.Homotopic.Quotient (0 : UnitAddTorus (Fin n)) 0))
    Γ
    (by
      dsimp [Γ, pcont, integralPath]
      rfl)
  exact congrArg Subtype.val hm


/-- Hatcher, Proposition 1.34 p.62: a deck map of a connected cover is determined
by one value. Apply covering-lift uniqueness to the two actual homeomorphisms. -/
private theorem deck_ext {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] {P : E → X} (cov : IsCoveringMap P)
    (d d' : deck P) (e : E) (h : d • e = d' • e) : d = d' := by
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun (cov.eq_of_comp_eq (d : E ≃ₜ E).continuous
    (d' : E ≃ₜ E).continuous (d.property.trans d'.property.symm) e h)

/-- Hatcher, pp.70–71: on a connected cover, the full deck action is free;
with fibre transitivity this is the quotient-cover structure used by monodromy. -/
private theorem deck_quotient_cover {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace E]
    {P : E → X} (cov : IsCoveringMap P) (hsurj : Function.Surjective P)
    (horbit : ∀ x y : E, P x = P y → ∃ d : deck P, d • x = y) :
    IsQuotientCoveringMap P (deck P) := by
  have hcancel : IsCancelSMul (deck P) E :=
    ⟨fun d d' e h ↦ deck_ext cov d d' e h⟩
  apply (_root_.isQuotientCoveringMap_iff_isCoveringMap_and P (deck P)).mpr
  refine ⟨cov, hsurj, inferInstance, hcancel, ?_⟩
  intro x y
  constructor
  · intro h
    obtain ⟨d, hd⟩ := horbit y x h.symm
    exact ⟨d, hd⟩
  · rintro ⟨d, rfl⟩
    exact deck.proj_smul d y

/-- Hatcher, Proposition 1.33 p.61 and Proposition 1.34 p.62: lift the
homeomorphism and its inverse at the original basepoint. Their composites are
lifts of the identity with the same base value, so uniqueness makes them inverse. -/
private theorem pointed_homeomorph_lift {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {P : C(E, X)} (cov : IsCoveringMap P) (e : E)
    (g : X ≃ₜ X) (hg : g (P e) = P e) :
    ∃ G : E ≃ₜ E, G e = e ∧ ∀ x, P (G x) = g (P x) := by
  obtain ⟨F, ⟨hF0, hF⟩, _⟩ := cov.existsUnique_continuousMap_lifts
    ((⟨g, g.continuous⟩ : C(X, X)).comp P) e e hg.symm
  have hgi : g.symm (P e) = P e := by
    simpa using (congrArg g.symm hg).symm
  obtain ⟨B, ⟨hB0, hB⟩, _⟩ := cov.existsUnique_continuousMap_lifts
    ((⟨g.symm, g.symm.continuous⟩ : C(X, X)).comp P) e e hgi.symm
  have hFp : ∀ x, P (F x) = g (P x) := fun x ↦ congrFun hF x
  have hBp : ∀ x, P (B x) = g.symm (P x) := fun x ↦ congrFun hB x
  have hBF : ∀ x, B (F x) = x := by
    apply congrFun (cov.eq_of_comp_eq (B.continuous.comp F.continuous)
      continuous_id ?_ e ?_)
    · ext x
      change P (B (F x)) = P x
      rw [hBp, hFp]
      exact g.symm_apply_apply _
    · change B (F e) = e
      rw [hF0, hB0]
  have hFB : ∀ x, F (B x) = x := by
    apply congrFun (cov.eq_of_comp_eq (F.continuous.comp B.continuous)
      continuous_id ?_ e ?_)
    · ext x
      change P (F (B x)) = P x
      rw [hFp, hBp]
      exact g.apply_symm_apply _
    · change F (B e) = e
      rw [hB0, hF0]
  refine ⟨⟨⟨F, B, hBF, hFB⟩, F.continuous, B.continuous⟩, hF0, ?_⟩
  intro x
  exact congrFun hF x


/-- Hatcher, path-lift uniqueness pp.61–62: a continuous commuting square
carries the lift of a path to the lift of its image, with the same initial point.
Apply monodromy to the mapped lifted path and keep the endpoint casts explicit. -/
private theorem monodromy_natural {E X V Y : Type*}
    [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace V] [TopologicalSpace Y]
    {P : C(E, X)} {Q : C(V, Y)}
    (pcov : IsCoveringMap P) (qcov : IsCoveringMap Q)
    (H : C(E, V)) (f : C(X, Y)) (hsq : ∀ e, Q (H e) = f (P e))
    {x y : X} (γ : Path.Homotopic.Quotient x y) (e : P ⁻¹' {x}) :
    (qcov.monodromy (γ.map f)
      ⟨H e, (hsq e).trans (congrArg f e.property)⟩ : V) =
      H (pcov.monodromy γ e) := by
  obtain ⟨γ⟩ := γ
  have hp0 : γ 0 = P e := γ.source.trans e.property.symm
  have hq0 : (γ.map f.continuous) 0 = Q (H e) := by
    change f (γ 0) = Q (H e)
    rw [hp0, hsq]
  change qcov.liftPath (γ.map f.continuous) (H e) hq0 1 =
    H (pcov.liftPath γ e _ 1)
  have heq : H.comp (pcov.liftPath γ e (γ.source.trans e.property.symm)) =
      qcov.liftPath (γ.map f.continuous) (H e) hq0 := by
    apply (qcov.eq_liftPath_iff' _).mpr
    constructor
    · ext t
      change Q (H (pcov.liftPath γ e _ t)) = f (γ t)
      rw [hsq]
      exact congrArg f (congrFun (pcov.liftPath_lifts γ e _) t)
    · change H (pcov.liftPath γ e _ 0) = H e
      rw [pcov.liftPath_zero]
  exact (DFunLike.congr_fun heq 1).symm


/-- The based-loop form of the preceding path-lift naturality identity, with
exactly Mathlib's induced based homomorphism and its original endpoint casts. -/
private theorem based_monodromy_natural {E X V Y : Type*}
    [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace V] [TopologicalSpace Y]
    {P : C(E, X)} {Q : C(V, Y)}
    (pcov : IsCoveringMap P) (qcov : IsCoveringMap Q)
    (H : C(E, V)) (f : C(X, Y)) (hsq : ∀ e, Q (H e) = f (P e))
    {x : X} {y : Y} (hf : f x = y)
    (e : E) (he : P e = x) (v : V) (hv : Q v = y) (hH : H e = v)
    (γ : FundamentalGroup X x) :
    H (pcov.monodromy γ ⟨e, he⟩) =
      (qcov.monodromy (FundamentalGroup.mapOfEq f hf γ) ⟨v, hv⟩ : V) := by
  subst y
  subst v
  simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    using (monodromy_natural pcov qcov H f hsq γ ⟨e, he⟩).symm

/-- Franks, Proposition (2.1) p.70: invariant functions descend through the
covering quotient. The compact base then bounds their range in the original norm. -/
private theorem invariant_descent {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [CompactSpace X]
    {P : C(E, X)} (cov : IsCoveringMap P) (hsurj : Function.Surjective P)
    (Γ : Type*) [Group Γ] (δ : Γ →* deck P)
    (horbit : ∀ x y : E, P x = P y ↔ ∃ γ, δ γ • x = y)
    (n : ℕ) (v : C(E, Fin n → ℝ))
    (hv : ∀ γ x, v (δ γ • x) = v x) :
    (∃! vbar : C(X, Fin n → ℝ), ∀ x, vbar (P x) = v x) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖v x‖ ≤ C := by
  have hfactor : Function.FactorsThrough v P := by
    intro x y h
    obtain ⟨γ, rfl⟩ := (horbit x y).mp h
    exact (hv γ x).symm
  let vbar := (cov.isQuotientMap hsurj).lift v hfactor
  have hbar : ∀ x, vbar (P x) = v x := by
    intro x
    exact DFunLike.congr_fun ((cov.isQuotientMap hsurj).lift_comp v hfactor) x
  constructor
  · refine ⟨vbar, hbar, ?_⟩
    intro w hw
    apply ContinuousMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact (hw x).trans (hbar x).symm
  · obtain ⟨C, hC⟩ := (isCompact_range vbar.continuous).isBounded.exists_norm_le
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro x
    rw [← hbar x]
    exact (hC _ (mem_range_self (P x))).trans (le_max_left _ _)


/-- Hatcher pp.61–65,70–71 and Franks (2.1) p.70: apply the actual path-class
universal cover, normalize the full deck action by monodromy, and lift the original
maps. Path-lift naturality supplies the based covariance, and covering uniqueness
extends it to every point. Invariant functions descend through the quotient and
are bounded on the compact base, as detailed in the public theorem's proof. -/
private theorem cover_lifts_from_normalized_torus
    (K : Type u) [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [PathConnectedSpace K] [LocallyPathConnectedSpace K]
    (b : K) (g : K ≃ₜ K) (hg : g b = b)
    (hsemi : ∀ x : K, ∃ U : Set K, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x))
    (n : ℕ) (h0 : C(K, UnitAddTorus (Fin n))) (hh0 : h0 b = 0)
    (covT : IsCoveringMap (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)))
    (zeroT : (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)) ⁻¹'
      {(0 : UnitAddTorus (Fin n))}) (hzT : (zeroT : Fin n → ℝ) = 0)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ q : FundamentalGroup (UnitAddTorus (Fin n)) 0,
      (covT.monodromy (FundamentalGroup.toPath q) zeroT : Fin n → ℝ) =
        fun j ↦ ((w q).toAdd j : ℝ)) :
    let pT : (Fin n → ℝ) → UnitAddTorus (Fin n) := fun x j ↦ (x j : UnitAddCircle)
    ∃ (E : Type u) (tE : TopologicalSpace E),
          let _ : TopologicalSpace E := tE
          ∃ (P : C(E, K)) (btilde : E) (hb : P btilde = b) (cov : IsCoveringMap P),
            SimplyConnectedSpace E ∧ LocallyPathConnectedSpace E ∧ Function.Surjective P ∧
            ∃ (δ : (FundamentalGroup K b)ᵐᵒᵖ ≃* deck P)
              (φ : (FundamentalGroup K b)ᵐᵒᵖ →* Multiplicative (Fin n → ℤ))
              (G : E ≃ₜ E) (H0 : C(E, Fin n → ℝ)),
              (∀ γ : (FundamentalGroup K b)ᵐᵒᵖ,
                δ γ • btilde =
                  (cov.monodromy (FundamentalGroup.toPath γ.unop) ⟨btilde, hb⟩ : E)) ∧
              (∀ x y : E, P x = P y ↔ ∃ γ : (FundamentalGroup K b)ᵐᵒᵖ, δ γ • x = y) ∧
              (∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E), δ γ • x = x → γ = 1) ∧
              (∀ γ : (FundamentalGroup K b)ᵐᵒᵖ,
                φ γ = w (FundamentalGroup.mapOfEq h0 hh0 γ.unop)) ∧
              G btilde = btilde ∧
              (∀ x : E, P (G x) = g (P x)) ∧
              (∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E),
                G (δ γ • x) =
                  δ (MulOpposite.op (FundamentalGroup.mapOfEq ⟨g, g.continuous⟩ hg γ.unop)) •
                    G x) ∧
              H0 btilde = 0 ∧
              (∀ x : E, pT (H0 x) = h0 (P x)) ∧
              (∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E),
                H0 (δ γ • x) = H0 x + fun j ↦ ((φ γ).toAdd j : ℝ)) ∧
              (∀ v : C(E, Fin n → ℝ),
                (∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E), v (δ γ • x) = v x) →
                (∃! vbar : C(K, Fin n → ℝ), ∀ x : E, vbar (P x) = v x) ∧
                  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖v x‖ ≤ C) := by
  classical
  let E := Σ x : K, Path.Homotopic.Quotient b x
  let good : Set K → Prop := fun U ↦ IsOpen U ∧ IsPathConnected U ∧
    ∀ x : K, x ∈ U → ∀ p : Path x x,
      (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)
  let sheet : Set K → E → Set E := fun U a ↦
    {e | ∃ η : Path a.1 e.1, (∀ t, η t ∈ U) ∧
      a.2.trans (Path.Homotopic.Quotient.mk η) = e.2}
  let tE : TopologicalSpace E := TopologicalSpace.generateFrom
    {S | ∃ (U : Set K) (a : E), good U ∧ a.1 ∈ U ∧ S = sheet U a}
  let : TopologicalSpace E := tE
  obtain ⟨hsurj, cov, hlocal, hsimp, hb, action, haction, hfree, hfib⟩ :=
    pointed_path_class_universal_cover b hsemi
  let : SimplyConnectedSpace E := hsimp
  let : LocallyPathConnectedSpace E := hlocal
  let P : C(E, K) := ⟨fun e ↦ e.1, cov.continuous⟩
  let e0 : E := ⟨b, Path.Homotopic.Quotient.refl b⟩
  have horbit : ∀ x y : E, P x = P y → ∃ d : deck P, d • x = y := by
    intro x y h
    obtain ⟨γ, hγ⟩ := (hfib x y).mp h
    exact ⟨action γ, (haction γ x).trans hγ.symm⟩
  let qcov := deck_quotient_cover (P := (P : E → K)) cov hsurj horbit
  let δ : (FundamentalGroup K b)ᵐᵒᵖ ≃* deck P :=
    ((qcov.fundamentalGroupEquiv ⟨e0, hb⟩).op).trans (MulEquiv.opOp (deck P)).symm
  have hδpoint : ∀ γ : (FundamentalGroup K b)ᵐᵒᵖ,
      δ γ • e0 = (cov.monodromy γ.unop ⟨e0, hb⟩ : E) := by
    intro γ
    exact qcov.unop_fundamentalGroupToMulOpposite_smul
  have hδfib : ∀ x y : E, P x = P y ↔ ∃ γ, δ γ • x = y := by
    intro x y
    constructor
    · intro h
      obtain ⟨d, hd⟩ := horbit x y h
      exact ⟨δ.symm d, by simpa using hd⟩
    · rintro ⟨γ, rfl⟩
      exact (deck.proj_smul (δ γ) x).symm
  have hδfree : ∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E), δ γ • x = x → γ = 1 := by
    intro γ x h
    apply δ.injective
    rw [δ.map_one]
    exact deck_ext cov (δ γ) 1 x (by simpa using h)
  let j := FundamentalGroup.mapOfEq h0 hh0
  let φ : (FundamentalGroup K b)ᵐᵒᵖ →* Multiplicative (Fin n → ℤ) :=
    { toFun := fun γ ↦ w (j γ.unop)
      map_one' := by
        change w (j 1) = 1
        rw [j.map_one, w.map_one]
      map_mul' := fun γ γ' ↦ by
        change w (j (γ'.unop * γ.unop)) = _
        rw [j.map_mul, w.map_mul, mul_comm] }
  obtain ⟨G, hG0, hPG⟩ := pointed_homeomorph_lift (P := P) cov e0 g (by simpa [P, e0] using hg)
  have hGδ : ∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E),
      G (δ γ • x) = δ (MulOpposite.op
        (FundamentalGroup.mapOfEq ⟨g, g.continuous⟩ hg γ.unop)) • G x := by
    intro γ
    let γg := MulOpposite.op (FundamentalGroup.mapOfEq ⟨g, g.continuous⟩ hg γ.unop)
    have hbase : G (δ γ • e0) = δ γg • e0 := by
      rw [hδpoint, hδpoint]
      exact based_monodromy_natural cov cov ⟨G, G.continuous⟩ ⟨g, g.continuous⟩
        hPG hg e0 hb e0 hb hG0 γ.unop
    apply congrFun (cov.eq_of_comp_eq
      (G.continuous.comp (δ γ : E ≃ₜ E).continuous)
      ((δ γg : E ≃ₜ E).continuous.comp G.continuous) ?_ e0 ?_)
    · ext x
      change P (G (δ γ • x)) = P (δ γg • G x)
      rw [hPG, deck.proj_smul (δ γ) x, deck.proj_smul (δ γg) (G x)]
      exact (hPG x).symm
    · change G (δ γ • e0) = δ γg • G e0
      rw [hG0]
      exact hbase
  let Q : C(Fin n → ℝ, UnitAddTorus (Fin n)) := ⟨_, covT.continuous⟩
  have hQ0 : Q 0 = 0 := by ext; simp [Q]
  obtain ⟨H0, ⟨hH00, hH0⟩, _⟩ := covT.existsUnique_continuousMap_lifts
    (h0.comp P) e0 0 (by
      change Q 0 = h0 (P e0)
      rw [hQ0]
      change 0 = h0 b
      exact hh0.symm)
  have hH0p : ∀ x, Q (H0 x) = h0 (P x) := fun x ↦ congrFun hH0 x
  have hHz : ∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ), H0 (δ γ • e0) = fun i ↦ ((φ γ).toAdd i : ℝ) := by
    intro γ
    rw [hδpoint]
    have hn := based_monodromy_natural cov (P := P) (Q := Q) covT H0 h0
      hH0p hh0 e0 hb 0 hQ0 hH00 γ.unop
    have hz : (⟨0, hQ0⟩ : Q ⁻¹' {0}) = zeroT := Subtype.ext hzT.symm
    rw [hz] at hn
    exact hn.trans (hw (j γ.unop))
  have hHδ : ∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E),
      H0 (δ γ • x) = H0 x + fun i ↦ ((φ γ).toAdd i : ℝ) := by
    intro γ
    have hz : ∀ i : Fin n, (((φ γ).toAdd i : ℝ) : UnitAddCircle) = 0 := by
      intro i
      exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
        ⟨(φ γ).toAdd i, by simp⟩
    apply congrFun (covT.eq_of_comp_eq
      (H0.continuous.comp (δ γ : E ≃ₜ E).continuous)
      (H0.continuous.add continuous_const) ?_ e0 ?_)
    · ext x i
      change (H0 (δ γ • x) i : UnitAddCircle) =
        ((H0 x i + ((φ γ).toAdd i : ℝ) : ℝ) : UnitAddCircle)
      rw [AddCircle.coe_add, hz, add_zero]
      exact congrFun ((hH0p (δ γ • x)).trans
        ((congrArg h0 (deck.proj_smul (δ γ) x)).trans (hH0p x).symm)) i
    · change H0 (δ γ • e0) = H0 e0 + _
      rw [hH00, zero_add]
      exact hHz γ
  refine ⟨E, tE, P, e0, hb, cov, hsimp, hlocal, hsurj,
    δ, φ, G, H0, hδpoint, hδfib, hδfree, ?_, hG0, hPG, hGδ,
    hH00, hH0p, hHδ, ?_⟩
  · intro γ
    rfl
  · intro v hv
    exact invariant_descent cov hsurj _ δ.toMonoidHom hδfib n v hv

/-- A pointed homeomorphism of a compact connected Hausdorff CW complex lifts to a pointed
homeomorphism of its universal cover. A pointed torus map has a continuous lift with the
original positive-winding deck covariance, and every invariant continuous real-vector-valued
function descends uniquely and is bounded. The cover, deck action and winding map are outputs.
The coordinate norm in the final boundedness assertion is Mathlib's finite-product norm;
boundedness is unchanged by replacing this with any equivalent Euclidean norm.

Source: Franks (1970), Proposition (2.1), pp.69–70; Hatcher, Proposition A.4 p.522,
universal-cover construction pp.63–65, Propositions 1.33–1.34 pp.61–62 and 1.39 pp.70–71.
For the positive winding normalization use Hatcher Theorem 1.7 pp.29–31 and its finite-product
application, Proposition 1.12 p.34; the actual projected loop lift ends at its integer vector.

Natural-language proof:

1. The CW contractible-open-neighborhood theorem gives local path-connectedness and semilocal
simple connectedness for K. Since K has basepoint b it is nonempty, and its connectedness makes it
path-connected. Apply the pointed path-class universal-cover theorem to obtain E=K̃, the endpoint
projection P, e₀=b̃, and the chronological left deck action. Its surjectivity, local
path-connectedness, simple connectedness and full fibre-orbit equation are conclusions of that
theorem, not hypotheses assumed from compactness.

Every deck homeomorphism d sends b̃ into the same P-fibre. Full fibre transitivity of the prefix
action supplies γ whose prefix deck map sends b̃ to d(b̃), uniquely by freeness. These two maps
are continuous lifts of P and agree at b̃. Since E is connected, covering-lift uniqueness
(Hatcher Proposition 1.34 p.62; the deck argument preceding Proposition 1.39 pp.70–71) makes
them equal everywhere. Thus the prefix homomorphism is onto the entire deck group, while
freeness makes it injective. Its inverse sends each deck map to this unique γ, so it gives the
returned deck-group equivalence δ without a surjectivity assumption.

2. Use chronological Γ explicitly. The exact bank definition gives Mathlib FundamentalGroup
multiplication p*q=q.trans p, so Γ is its opposite for implementation. Write
j=(h0)_*:FundamentalGroup K b→FundamentalGroup T^n 0 and w for the positive winding equivalence.
For γ=op(q) put φ(γ)=toAdd(w(j(q))). Because unop(γδ)=unop(δ)*unop(γ), this evaluates to
φ(δ)+φ(γ)=φ(γ)+φ(δ); thus φ is the asserted homomorphism into Z^n. Define the induced automorphism
g_*(op(q))=op((g)_*(q)). No loop inversion or winding sign change occurs.

3. Define G([α])=[g∘α] and its inverse [α]↦[g⁻¹∘α]. Composition of an endpoint-fixed homotopy with
g or g⁻¹ proves well-definedness. A good open U maps under g to another good open, since g and g⁻¹
induce inverse maps on loops; G carries U_[α] homeomorphically to (gU)_[gα] by the sheet endpoint
charts. Thus both maps are continuous and inverse. They fix e₀ since g fixes b and satisfy
P∘G=g∘P. For γ represented by ℓ, G(γ·[α])=[gℓ followed by gα]=g_*(γ)·G([α]). The same formula for
g⁻¹ proves pointed inverse lift covariance.

4. The torus winding theorem supplies the coordinate projection p:R^n→T^n as a pointed simply
connected translation covering, with winding number equal to the endpoint of a loop lift starting
at zero. Apply the simply-connected lift leaf to h0∘P:E→T^n with value zero at e₀. Its hypotheses
hold because E is simply connected and locally path-connected and h0(P(e₀))=0. This gives a
continuous H0 with p∘H0=h0∘P. For γ=[ℓ], the stopped-path lift of ℓ in E ends at γ·e₀; composing
with H0 is the unique lift of h0∘ℓ starting at zero. Hence H0(γ·e₀)=φ(γ). The maps H0∘δγ and
e↦H0(e)+φ(γ) are continuous lifts of h0∘P through p, and they agree at e₀ by that endpoint
calculation. Pointed lift uniqueness makes them equal everywhere. Consequently H0(γe)=H0(e)+φ(γ),
in the positive chronological convention.

5. For a continuous Γ-invariant v:E→R^n, the fibre-orbit equality gives v(e)=v(e') whenever
P(e)=P(e'). P is a continuous surjective covering and hence an open surjection. It is a quotient
map: if P⁻¹(A) is open, then A=P(P⁻¹(A)) is open by surjectivity and openness; the converse
follows by continuity. Apply the continuous fibre-descent leaf to obtain vbar:K→R^n with vbar∘P=v,
unique since P is onto. The compact-range leaf makes range(vbar) compact; compact sets in the
canonical metric bornology are bounded, and the norm-bound leaf gives a real C with ||vbar(k)||≤C
for all k. Then ||v(e)||≤C for every e. Replacing C by max(C,0) if desired gives a nonnegative
bound. No compact fundamental domain upstairs is required.

6. If n=0 then R^n, T^n and Z^n are singletons, so H0 and φ are their unique maps and the same
equations hold. If Γ is trivial, the prefix action and its covariance reduce to identity. K may be
a point; none of the proof uses smoothness, differentiability, torus hyperbolicity or an
induced-map commutation with a hyperbolic automorphism. Those are additional hypotheses of
Franks's later correction argument, not of this covering lemma.

In the formal statement, the canonical coordinate projection pT is a literal lambda. Its covering
proof covT and its zero fibre point are returned, and w is characterized by the endpoint of
covT.monodromy for every actual torus loop. Thus w has the positive winding convention, including
negative loops and the empty product n=0. The deck isomorphism δ is characterized at b̃ by the
endpoint of P-monodromy for every original loop, and hence is the chronological prefix action.
This characterization rules out replacing it by a sign-inverted or arbitrary automorphism.
The homomorphism φ is returned with its exact induced-map formula, rather than assumed as input.
All covering, simple-connectedness, deck-orbit and lift conclusions belong to the existential
output; compact CW locality and winding are proof prerequisites only.
-/
theorem compact_cw_cover_lifts
    (K : Type u) [TopologicalSpace K] [T2Space K] [CompactSpace K] [ConnectedSpace K]
    [Topology.CWComplex (univ : Set K)]
    (b : K) (g : K ≃ₜ K) (hg : g b = b)
    (n : ℕ) (h0 : C(K, UnitAddTorus (Fin n))) (hh0 : h0 b = 0) :
    let pT : (Fin n → ℝ) → UnitAddTorus (Fin n) := fun x j ↦ (x j : UnitAddCircle)
    ∃ (covT : IsCoveringMap pT) (zeroT : pT ⁻¹' {(0 : UnitAddTorus (Fin n))}),
      (zeroT : Fin n → ℝ) = 0 ∧
      ∃ (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ)),
        (∀ q : FundamentalGroup (UnitAddTorus (Fin n)) 0,
          (covT.monodromy (FundamentalGroup.toPath q) zeroT : Fin n → ℝ) =
            fun j ↦ ((w q).toAdd j : ℝ)) ∧
        ∃ (E : Type u) (tE : TopologicalSpace E),
          let _ : TopologicalSpace E := tE
          ∃ (P : C(E, K)) (btilde : E) (hb : P btilde = b) (cov : IsCoveringMap P),
            SimplyConnectedSpace E ∧ LocallyPathConnectedSpace E ∧ Function.Surjective P ∧
            ∃ (δ : (FundamentalGroup K b)ᵐᵒᵖ ≃* deck P)
              (φ : (FundamentalGroup K b)ᵐᵒᵖ →* Multiplicative (Fin n → ℤ))
              (G : E ≃ₜ E) (H0 : C(E, Fin n → ℝ)),
              (∀ γ : (FundamentalGroup K b)ᵐᵒᵖ,
                δ γ • btilde =
                  (cov.monodromy (FundamentalGroup.toPath γ.unop) ⟨btilde, hb⟩ : E)) ∧
              (∀ x y : E, P x = P y ↔ ∃ γ : (FundamentalGroup K b)ᵐᵒᵖ, δ γ • x = y) ∧
              (∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E), δ γ • x = x → γ = 1) ∧
              (∀ γ : (FundamentalGroup K b)ᵐᵒᵖ,
                φ γ = w (FundamentalGroup.mapOfEq h0 hh0 γ.unop)) ∧
              G btilde = btilde ∧
              (∀ x : E, P (G x) = g (P x)) ∧
              (∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E),
                G (δ γ • x) =
                  δ (MulOpposite.op (FundamentalGroup.mapOfEq ⟨g, g.continuous⟩ hg γ.unop)) •
                    G x) ∧
              H0 btilde = 0 ∧
              (∀ x : E, pT (H0 x) = h0 (P x)) ∧
              (∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E),
                H0 (δ γ • x) = H0 x + fun j ↦ ((φ γ).toAdd j : ℝ)) ∧
              (∀ v : C(E, Fin n → ℝ),
                (∀ (γ : (FundamentalGroup K b)ᵐᵒᵖ) (x : E), v (δ γ • x) = v x) →
                (∃! vbar : C(K, Fin n → ℝ), ∀ x : E, vbar (P x) = v x) ∧
                  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖v x‖ ≤ C) := by
  dsimp
  obtain ⟨covT, zeroT, hzero⟩ := coordinate_cover_data n
  obtain ⟨w, hw, _hwstd, _hwmap⟩ := torus_pi1_standard_winding n
  obtain ⟨_, hlocal, hsemi, hpath⟩ := cw_contractible_open_neighborhoods (X := K)
  let : LocallyPathConnectedSpace K := hlocal
  let : PathConnectedSpace K := hpath inferInstance
  have hsemi' : ∀ x : K, ∃ U : Set K, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x) := by
    intro x
    obtain ⟨U, hU, hx, hp⟩ := hsemi x
    exact ⟨U, hU, hx, fun p hmem ↦ hp p (Set.range_subset_iff.mpr hmem)⟩
  have hwinding : ∀ q : FundamentalGroup (UnitAddTorus (Fin n)) 0,
      (covT.monodromy (FundamentalGroup.toPath q) zeroT : Fin n → ℝ) =
        fun i ↦ ((w q).toAdd i : ℝ) := by
    intro q
    let z : Fin n → ℤ := (w q).toAdd
    obtain ⟨p, hp, hwp⟩ := hw z
    have hq : q = FundamentalGroup.fromPath ⟦p⟧ := by
      apply w.injective
      rw [hwp]
      rfl
    rw [hq]
    have hp' : p = integralPath n z := by
      ext t i
      exact (hp t i).trans (integralPath_formula n z t i).symm
    rw [hp']
    rw [integralPath_monodromy _ _ covT zeroT hzero]
    have hwp' : w (FundamentalGroup.fromPath ⟦integralPath n z⟧) =
        Multiplicative.ofAdd z := by
      rw [← hp']
      exact hwp
    rw [hwp']
    funext i
    rfl
  refine ⟨covT, zeroT, hzero, w, hwinding, ?_⟩
  exact cover_lifts_from_normalized_torus K b g hg hsemi' n h0 hh0 covT zeroT hzero w hwinding



end HolomorphicAnosov.Topology.FranksCompactCWCoverLifts
