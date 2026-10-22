/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.DisjointUnion

/-!
# Compactification of a disjoint union of opens

The native colimit of a disjoint open cover identifies the actual union
with the binary coproduct. Image closure then supplies schematic density
without changing the original structural map to the base.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The actual union of disjoint opens is their coproduct, over the original
scheme. The isomorphism comes from the native disjoint-open colimit. -/
theorem exists_coprodIso_sup_of_disjoint {X : Scheme.{u}}
    (U V : X.Opens) (hUV : Disjoint U V) :
    ∃ e : U.toScheme ⨿ V.toScheme ≅ (U ⊔ V).toScheme,
      e.hom ≫ (U ⊔ V).ι = coprod.desc U.ι V.ι := by
  let q : (b : WalkingPair) → (b.casesOn U.toScheme V.toScheme) ⟶ (U ⊔ V).toScheme
    | .left => X.homOfLE le_sup_left
    | .right => X.homOfLE le_sup_right
  let (b : WalkingPair) : IsOpenImmersion (q b) := by
    cases b <;> dsimp only [q] <;> infer_instance
  have hleft : (q .left).opensRange = (U ⊔ V).ι ⁻¹ᵁ U :=
    Scheme.opensRange_homOfLE le_sup_left
  have hright : (q .right).opensRange = (U ⊔ V).ι ⁻¹ᵁ V :=
    Scheme.opensRange_homOfLE le_sup_right
  have hcov : (⨆ b, (q b).opensRange) = ⊤ := by
    apply top_unique
    intro x _
    rcases x.property with hx | hx
    · apply (le_iSup (fun b => (q b).opensRange) WalkingPair.left)
      rw [hleft]
      exact hx
    · apply (le_iSup (fun b => (q b).opensRange) WalkingPair.right)
      rw [hright]
      exact hx
  have hdisj : Pairwise (fun a b => Disjoint (q a).opensRange (q b).opensRange) := by
    intro a b hab
    cases a <;> cases b
    · exact (hab rfl).elim
    · rw [hleft, hright, ← TopologicalSpace.Opens.coe_disjoint]
      exact (TopologicalSpace.Opens.coe_disjoint.mpr hUV).preimage (U ⊔ V).ι
    · rw [hright, hleft, ← TopologicalSpace.Opens.coe_disjoint]
      exact (TopologicalSpace.Opens.coe_disjoint.mpr hUV.symm).preimage (U ⊔ V).ι
    · exact (hab rfl).elim
  obtain ⟨H⟩ := nonempty_isColimit_cofanMk_of q hcov hdisj
  change IsColimit (BinaryCofan.mk (X.homOfLE (show U ≤ U ⊔ V from le_sup_left))
    (X.homOfLE (show V ≤ U ⊔ V from le_sup_right))) at H
  let e := (coprodIsCoprod U.toScheme V.toScheme).coconePointUniqueUpToIso H
  have heleft : (coprod.inl : U.toScheme ⟶ U.toScheme ⨿ V.toScheme) ≫ e.hom =
      X.homOfLE (show U ≤ U ⊔ V from le_sup_left) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod U.toScheme V.toScheme) H (Discrete.mk WalkingPair.left)
  have heright : (coprod.inr : V.toScheme ⟶ U.toScheme ⨿ V.toScheme) ≫ e.hom =
      X.homOfLE (show V ≤ U ⊔ V from le_sup_right) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod U.toScheme V.toScheme) H (Discrete.mk WalkingPair.right)
  refine ⟨e, ?_⟩
  apply coprod.hom_ext
  · rw [← Category.assoc, heleft, homOfLE_ι, coprod.inl_desc]
  · rw [← Category.assoc, heright, homOfLE_ι, coprod.inr_desc]

namespace Hom

/-- Compactifications of disjoint opens combine into a schematically dense
compactification of their actual union and its original map to the base. -/
theorem exists_schematicallyDense_compactification_sup_of_disjoint
    {X S : Scheme.{u}} (p : X ⟶ S) (U V : X.Opens) (hUV : Disjoint U V)
    (C : Compactification (U.ι ≫ p)) (D : Compactification (V.ι ≫ p))
    [QuasiCompact ((U ⊔ V).ι ≫ p)] :
    ∃ E : Compactification ((U ⊔ V).ι ≫ p), IsSchemeTheoreticallyDominant E.j := by
  obtain ⟨e, he⟩ := exists_coprodIso_sup_of_disjoint U V hUV
  let E := C.coprod D
  let j := e.inv ≫ E.j
  have hj : j ≫ E.p = (U ⊔ V).ι ≫ p := by
    dsimp only [j]
    rw [Category.assoc, E.fac]
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, he]
    apply coprod.hom_ext <;> simp
  let : QuasiCompact (j ≫ E.p) := by rw [hj]; infer_instance
  have : QuasiCompact j := QuasiCompact.of_comp j E.p
  exact ⟨Compactification.ofImmersion _ j E.p hj, inferInstance⟩

end Hom
end AlgebraicGeometry.Scheme
