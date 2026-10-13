import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition

noncomputable section
open TopologicalSpace
namespace HolomorphicAnosov

/-- The coordinate product of two admissible Euclidean maps has compact fixed set.
Source: Dold (1965), §1.6, printed p.2.
Proof: the fixed set is the image of the product of the two factor fixed sets
under the inverse coordinate equivalence, with its induced subtype map. This map
is continuous, and products and continuous images of compact sets are compact. -/
theorem euclidean_product_fixedSet_compact :
    let euclideanProductDomain :
      ∀ {n m : ℕ}, Opens (EuclideanSpace ℝ (Fin n)) →
        Opens (EuclideanSpace ℝ (Fin m)) → Opens (EuclideanSpace ℝ (Fin (n + m))) :=
      fun {n} {m} U V ↦
        ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ)) ⁻¹' (U ×ˢ V),
          (U.isOpen.prod V.isOpen).preimage EuclideanSpace.finAddEquivProd.continuous⟩
    let euclideanProductMap :
      ∀ {n m : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
        {V : Opens (EuclideanSpace ℝ (Fin m))},
        C(U, EuclideanSpace ℝ (Fin n)) → C(V, EuclideanSpace ℝ (Fin m)) →
          C(euclideanProductDomain U V, EuclideanSpace ℝ (Fin (n + m))) :=
      fun {n} {m} {U} {V} f g ↦ by
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
        let a : C(euclideanProductDomain U V, U) :=
          ⟨fun x ↦ ⟨(e x.1).1, x.2.1⟩,
            (e.continuous.comp continuous_subtype_val).fst.subtype_mk _⟩
        let b : C(euclideanProductDomain U V, V) :=
          ⟨fun x ↦ ⟨(e x.1).2, x.2.2⟩,
            (e.continuous.comp continuous_subtype_val).snd.subtype_mk _⟩
        exact ⟨fun x ↦ e.symm (f (a x), g (b x)),
          e.symm.continuous.comp ((f.continuous.comp a.continuous).prodMk
            (g.continuous.comp b.continuous))⟩
    ∀ (n m : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
      (V : Opens (EuclideanSpace ℝ (Fin m)))
      (f : C(U, EuclideanSpace ℝ (Fin n))) (g : C(V, EuclideanSpace ℝ (Fin m)))
      (_hF : IsCompact (euclideanFixedSet f)) (_hG : IsCompact (euclideanFixedSet g)),
      IsCompact (euclideanFixedSet (euclideanProductMap f g)) := by
  dsimp only
  intro n m U V f g hF hG
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let W : Opens (EuclideanSpace ℝ (Fin (n + m))) :=
    ⟨e ⁻¹' (U ×ˢ V), (U.isOpen.prod V.isOpen).preimage e.continuous⟩
  let k : U × V → W := fun z ↦ ⟨e.symm (z.1.1, z.2.1), by
    change e (e.symm (z.1.1, z.2.1)) ∈ ((U : Set _) ×ˢ (V : Set _))
    rw [e.apply_symm_apply]
    exact ⟨z.1.2, z.2.2⟩⟩
  have hk : Continuous k :=
    (e.symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hc := (hF.prod hG).image hk
  convert hc using 1
  ext x
  constructor
  · intro hx
    let u : U := ⟨(e x.1).1, x.2.1⟩
    let v : V := ⟨(e x.1).2, x.2.2⟩
    have heq : (f u, g v) = e x.1 := by
      change e.symm (f u, g v) = x.1 at hx
      have h := congrArg e hx
      simpa only [e.apply_symm_apply] using h
    refine ⟨(u, v), ⟨?_, ?_⟩, ?_⟩
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq
    · apply Subtype.ext
      exact e.symm_apply_apply x.1
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    change e.symm (f _, g _) = e.symm (u.1, v.1)
    congr 1
    apply Prod.ext
    · convert hu using 1; simp [k, e, euclideanFixedSet]
    · convert hv using 1; simp [k, e, euclideanFixedSet]

end HolomorphicAnosov
