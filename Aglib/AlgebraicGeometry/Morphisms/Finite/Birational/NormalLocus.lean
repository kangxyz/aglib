/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.Birational
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange

/-!
# Finite birational maps with normality only outside the isomorphism open

A finite dominant morphism between integral schemes which is an isomorphism
over a nonempty open needs normal target stalks only outside that open.
The proof uses actual stalk-spectrum base changes. It does not assume that
the normal locus is open, or impose excellence or a finiteness condition on
normalization.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

private theorem isIntegral_pullback_fromSpecStalk
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsDominant p] (x : X) :
    IsIntegral (pullback p (X.fromSpecStalk x)) := by
  let s := X.fromSpecStalk x
  let a := pullback.fst p s
  let : Flat s := Scheme.fromSpecStalk_flat X x
  let (z : (pullback p s : Scheme.{u})) :
      IsDomain ((pullback p s).presheaf.stalk z) := by
    let : IsIso (a.stalkMap z) :=
      Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks a z
    exact (asIso (a.stalkMap z)).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _
  let : IsReduced (pullback p s) := isReduced_of_isReduced_stalk _
  have hg : genericPoint X ∈ Set.range s := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  obtain ⟨t, ht⟩ := hg
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (genericPoint Y) t
    ((Scheme.map_genericPoint_of_isDominant Y p).trans ht.symm)
  have hgeneric : IsGenericPoint z (Set.univ : Set (pullback p s : Scheme.{u})) := by
    apply isGenericPoint_iff_specializes.mpr
    intro w
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    apply a.isEmbedding.isInducing.specializes_iff.mp
    change pullback.fst p s z ⤳ pullback.fst p s w
    rw [hz]
    exact (genericPoint_spec Y).specializes trivial
  let : IrreducibleSpace (pullback p s : Scheme.{u}) :=
    (irreducibleSpace_def _).mpr hgeneric.isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _

private theorem isIso_restrict_pullback_snd
    {Y X T : Scheme.{u}} (p : Y ⟶ X) (s : T ⟶ X) (U : X.Opens)
    [IsIso (p ∣_ U)] : IsIso (pullback.snd p s ∣_ s ⁻¹ᵁ U) := by
  let a := pullback.fst p s
  let b := pullback.snd p s
  have he : a ⁻¹ᵁ p ⁻¹ᵁ U = b ⁻¹ᵁ s ⁻¹ᵁ U := by
    rw [← Hom.comp_preimage, ← Hom.comp_preimage, pullback.condition]
  have h := Hom.isPullback_resLE (IsPullback.of_hasPullback p s)
    (US := U) (UT := s ⁻¹ᵁ U) (UX := p ⁻¹ᵁ U) (UY := b ⁻¹ᵁ s ⁻¹ᵁ U)
    le_rfl le_rfl (by rw [he]; exact (inf_idem _).symm)
  have hp : IsIso (p.resLE U (p ⁻¹ᵁ U) le_rfl) := by
    rw [Hom.resLE_eq_morphismRestrict]
    infer_instance
  have hb : IsIso (b.resLE (s ⁻¹ᵁ U) (b ⁻¹ᵁ s ⁻¹ᵁ U) le_rfl) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) h hp
  simpa only [Hom.resLE_eq_morphismRestrict] using hb

private theorem isIso_pullback_fromSpecStalk_of_normal
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsFinite p] [IsDominant p]
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)] (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] :
    IsIso (pullback.snd p (X.fromSpecStalk x)) := by
  let s := X.fromSpecStalk x
  let q := pullback.snd p s
  let V := s ⁻¹ᵁ U
  let : IsIntegral (pullback p s) := isIntegral_pullback_fromSpecStalk p x
  let : IsIso (q ∣_ V) := isIso_restrict_pullback_snd p s U
  let : Nonempty V := by
    have hg : genericPoint X ∈ Set.range s := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨z, hz⟩ := hg
    refine ⟨⟨z, ?_⟩⟩
    change s z ∈ U
    rw [hz]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  have hN : NormalStalks (Spec (X.presheaf.stalk x)) := by
    intro z
    have h := isIntegrallyClosed_and_isDomain_stalk_Spec (X.presheaf.stalk x) z
    exact ⟨h.2, h.1⟩
  exact isIso_of_isFinite_of_isIso_restrict q hN V

/-- A finite birational morphism only needs normal target stalks outside
the supplied isomorphism open. The normal locus need not be open. -/
theorem isIso_of_isFinite_of_isIso_restrict_of_normal_complement
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsFinite p] [IsDominant p]
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)]
    (hN : ∀ x : X, x ∉ U → IsIntegrallyClosed (X.presheaf.stalk x)) : IsIso p := by
  have hlocal (x : X) (hx : x ∉ U) :
      IsIso (pullback.snd p (X.fromSpecStalk x)) := by
    let : IsIntegrallyClosed (X.presheaf.stalk x) := hN x hx
    exact isIso_pullback_fromSpecStalk_of_normal p U x
  have hinjective : Function.Injective p := by
    intro y z hyz
    by_cases hy : p y ∈ U
    · have hz : p z ∈ U := hyz ▸ hy
      have he : (p ∣_ U) ⟨y, hy⟩ = (p ∣_ U) ⟨z, hz⟩ := by
        apply Subtype.ext
        exact (morphismRestrict_base_coe p U ⟨y, hy⟩).trans
          (hyz.trans (morphismRestrict_base_coe p U ⟨z, hz⟩).symm)
      exact congrArg Subtype.val ((p ∣_ U).isOpenEmbedding.injective he)
    · let s := X.fromSpecStalk (p y)
      let q := pullback.snd p s
      let : IsIso q := hlocal (p y) hy
      obtain ⟨y', hy', hqy⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := s) y
        (IsLocalRing.closedPoint (X.presheaf.stalk (p y)))
        (Scheme.fromSpecStalk_closedPoint (X := X) (x := p y)).symm
      obtain ⟨z', hz', hqz⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := s) z
        (IsLocalRing.closedPoint (X.presheaf.stalk (p y)))
        (hyz.symm.trans (Scheme.fromSpecStalk_closedPoint (X := X) (x := p y)).symm)
      have he : y' = z' := q.isOpenEmbedding.injective (hqy.trans hqz.symm)
      exact hy'.symm.trans ((congrArg (pullback.fst p s) he).trans hz')
  apply (isIso_iff_isIso_stalkMap p).mpr
  refine ⟨?_, fun y => ?_⟩
  · apply (TopCat.isIso_iff_isHomeomorph p.base).mpr
    exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨p.continuous, p.isClosedMap, hinjective, p.surjective⟩
  · by_cases hy : p y ∈ U
    · exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
        (morphismRestrictStalkMap p U ⟨y, hy⟩)).mp inferInstance
    · let s := X.fromSpecStalk (p y)
      let : Flat s := Scheme.fromSpecStalk_flat X (p y)
      let : IsIso (pullback.snd p s) := hlocal (p y) hy
      obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := s) y
        (IsLocalRing.closedPoint (X.presheaf.stalk (p y)))
        (Scheme.fromSpecStalk_closedPoint (X := X) (x := p y)).symm
      exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
        (Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion
          (IsPullback.of_hasPullback p s) z y hz)).mpr inferInstance

end AlgebraicGeometry.Scheme
