/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Normalized
public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified

/-!
# Rigidification and the laws of family pullback

The actual normalized tensor line bundle has a chosen rigidification. The
identity and composition comparisons are isomorphisms of the existing
`RigidifiedPair`s, with the required equation on their rigidifications. The
construction corrects the ordinary pullback comparison by its scalar defect,
as in `RigidifiedPair.isoOfBundleIso`. Universal O-connectedness makes these
isomorphisms unique and gives the coherence laws, on all test schemes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

set_option backward.isDefEq.respectTransparency false in
/-- The actual normalized family bundle is trivial along the origin section. -/
theorem nonempty_normalizedFamilyRigidification (T : Over S)
    (L : LineBundle (pullback p T.hom)) :
    Nonempty ((Scheme.Modules.pullback (originSection p o ho T)).obj
      (normalizedFamilyLineBundle p o ho T L).val ≅
        (SheafOfModules.unit T.left.ringCatSheaf : T.left.Modules)) := by
  have h : classOf _ (pullbackLineBundle (originSection p o ho T)
      (normalizedFamilyLineBundle p o ho T L)) =
      classOf _ (trivialLineBundle T.left) := by
    rw [← pullbackClass_classOf, classOf_normalizedFamilyLineBundle, classOf_trivial]
    exact (normalizedFamilyClass p o ho T (classOf _ L)).property
  obtain ⟨e⟩ := (class_eq_iff _ _ _).mp h
  exact ⟨e ≪≫ coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit T.left.ringCatSheaf)⟩

/-- The normalized tensor line bundle with one selected rigidification. -/
def normalizedFamilyRigidifiedPair (T : Over S) (L : LineBundle (pullback p T.hom)) :
    RigidifiedPair p o ho T where
  bundle := normalizedFamilyLineBundle p o ho T L
  rigidification := Classical.choice (nonempty_normalizedFamilyRigidification p o ho T L)

@[simp]
theorem normalizedFamilyRigidifiedPair_bundle (T : Over S)
    (L : LineBundle (pullback p T.hom)) :
    (normalizedFamilyRigidifiedPair p o ho T L).bundle =
      normalizedFamilyLineBundle p o ho T L := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual normalized tensor line bundle commutes with arbitrary family
pullback, up to an isomorphism of the original module sheaves. -/
theorem nonempty_normalizedFamilyLineBundle_pullbackIso {T T' : Over S}
    (f : T' ⟶ T) (L : LineBundle (pullback p T.hom)) :
    Nonempty ((pullbackLineBundle ((familyScheme p).map f)
      (normalizedFamilyLineBundle p o ho T L)).val ≅
        (normalizedFamilyLineBundle p o ho T'
          (pullbackLineBundle ((familyScheme p).map f) L)).val) := by
  let q : pullback p T'.hom ⟶ pullback p T.hom := (familyScheme p).map f
  change Nonempty ((pullbackLineBundle q (normalizedFamilyLineBundle p o ho T L)).val ≅
    (normalizedFamilyLineBundle p o ho T' (pullbackLineBundle q L)).val)
  apply (class_eq_iff _ _ _).mp
  change classOf _ (pullbackLineBundle q (normalizedFamilyLineBundle p o ho T L)) =
    classOf _ (normalizedFamilyLineBundle p o ho T' (pullbackLineBundle q L))
  rw [← pullbackClass_classOf, classOf_normalizedFamilyLineBundle,
    classOf_normalizedFamilyLineBundle, ← pullbackClass_classOf]
  exact (congrArg Subtype.val (normalizedFamilyClass_pullback p o ho f (classOf _ L))).symm

/-- Pullback of the chosen normalized pair agrees with the normalized
pullback pair by an actual rigidification-preserving isomorphism. -/
def normalizedFamilyRigidifiedPairMapIso {T T' : Over S} (f : T' ⟶ T)
    (L : LineBundle (pullback p T.hom)) :
    RigidifiedPair.Iso (RigidifiedPair.map f (normalizedFamilyRigidifiedPair p o ho T L))
      (normalizedFamilyRigidifiedPair p o ho T'
        (pullbackLineBundle ((familyScheme p).map f) L)) :=
  RigidifiedPair.isoOfBundleIso _ _
    (Classical.choice (nonempty_normalizedFamilyLineBundle_pullbackIso p o ho f L))

namespace RigidifiedPair

variable {p o ho}

/-- Equality of the original test-scheme map gives an isomorphism of its
pullbacks, preserving the existing rigidifications. -/
def mapCongrIso {T T' : Over S} {f g : T' ⟶ T} (h : f = g)
    (P : RigidifiedPair p o ho T) : Iso (map f P) (map g P) :=
  h ▸ Iso.refl (map f P)

set_option backward.isDefEq.respectTransparency false in
/-- The identity comparison for actual pullback of rigidified families. -/
def mapIdIso {T : Over S} (P : RigidifiedPair p o ho T) : Iso (map (𝟙 T) P) P :=
  isoOfBundleIso _ _
    ((Scheme.Modules.pullbackCongr ((familyScheme p).map_id T)).app P.bundle.val ≪≫
      (Scheme.Modules.pullbackId _).app P.bundle.val)

set_option backward.isDefEq.respectTransparency false in
/-- The composition comparison for the original pullback of rigidified
families, including compatibility with their rigidifications. -/
def mapCompIso {T₀ T₁ T₂ : Over S} (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂)
    (P : RigidifiedPair p o ho T₂) : Iso (map (f ≫ g) P) (map f (map g P)) :=
  isoOfBundleIso _ _
    ((Scheme.Modules.pullbackCongr ((familyScheme p).map_comp f g)).app P.bundle.val ≪≫
      ((Scheme.Modules.pullbackComp ((familyScheme p).map f)
        ((familyScheme p).map g)).app P.bundle.val).symm)

/-- The left unit law for rigidified family pullback. -/
theorem mapCompIso_id_left {T₀ T₁ : Over S} (f : T₀ ⟶ T₁)
    (P : RigidifiedPair p o ho T₁) [IsIso (pullback.snd p T₀.hom).c] :
    (mapCompIso (𝟙 T₀) f P).trans (mapIdIso (map f P)) =
      mapCongrIso (Category.id_comp f) P :=
  Iso.eq_of_isIso_c p o ho _ _

/-- The right unit law for rigidified family pullback. -/
theorem mapCompIso_id_right {T₀ T₁ : Over S} (f : T₀ ⟶ T₁)
    (P : RigidifiedPair p o ho T₁) [IsIso (pullback.snd p T₀.hom).c] :
    (mapCompIso f (𝟙 T₁) P).trans (Iso.map f (mapIdIso P)) =
      mapCongrIso (Category.comp_id f) P :=
  Iso.eq_of_isIso_c p o ho _ _

/-- The associativity law for the same actual rigidified pullback
comparisons. It needs only universal O-connectedness at the final test scheme. -/
theorem mapCompIso_assoc {T₀ T₁ T₂ T₃ : Over S}
    (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂) (h : T₂ ⟶ T₃)
    (P : RigidifiedPair p o ho T₃) [IsIso (pullback.snd p T₀.hom).c] :
    ((mapCompIso (f ≫ g) h P).trans (mapCompIso f g (map h P))) =
      ((mapCongrIso (Category.assoc f g h) P).trans
        ((mapCompIso f (g ≫ h) P).trans (Iso.map f (mapCompIso g h P)))) :=
  Iso.eq_of_isIso_c p o ho _ _

end RigidifiedPair

end AlgebraicGeometry.Scheme.RelativePicard
