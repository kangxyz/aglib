/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Translation
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Fppf
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Classifying
public import Aglib.AlgebraicGeometry.Picard.IdentityComponent
public import Aglib.AlgebraicGeometry.Group.LineBundleCube.Rigidity

/-!
# The morphism associated to a line bundle on a proper group

The morphism `φ_L` classifies the original family `t_a^* L ⊗ L⁻¹`, normalized
along the original unit. It uses the supplied fppf Picard representative `P`
and its normalized representation; the underlying scheme and group law of
`P` are unchanged. Its equations are first proved for every locally Noetherian
test scheme, including nonreduced ones. No smoothness, dimension or properness
of `Pic⁰` is assumed.

Source: Edixhoven--van der Geer--Moonen, preliminary *Abelian Varieties*,
Chapter VI, §3, text preceding (6.18), printed p. 95; Chapter II (2.10), p. 20.
The homomorphism property follows from the general pointed-morphism rigidity
theorem with separated locally finite-type target.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local
open Scheme.Group

universe u

attribute [local instance] Over.cartesianMonoidalCategory


variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The normalized representation of the same supplied Picard scheme,
using its original group unit as the normalizing section. -/
abbrev lineBundleNormalizedRepresentation :=
  normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral
    G.hom η[G].left (Over.w η[G]) R

/-- The original morphism associated to a Picard class on a proper
geometrically integral group scheme, through the supplied representative. -/
def lineBundleClassMorphism (a : PicardGroup G.left) : G ⟶ P.obj :=
  (normalizedFamilyClassifyingMap G.hom η[G].left (Over.w η[G])
    (lineBundleNormalizedRepresentation G P R)
    ⟨G, LocallyOfFiniteType.isLocallyNoetherian G.hom⟩
    (translationFamilyClass G (𝟙 G) a)).hom

/-- The line-bundle constructor uses exactly its original Picard class. -/
def lineBundleMorphism (L : LineBundle G.left) : G ⟶ P.obj :=
  lineBundleClassMorphism G P R (classOf G.left L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The classifying equation on every locally Noetherian test scheme.
This retains the original translated family and its actual normalization. -/
theorem homEquiv_comp_lineBundleClassMorphism
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ G)
    (a : PicardGroup G.left) :
    (lineBundleNormalizedRepresentation G P R).homEquiv
      (ObjectProperty.homMk (t ≫ lineBundleClassMorphism G P R a)) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T.obj
        (translationFamilyClass G t a) := by
  let Q : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨G, LocallyOfFiniteType.isLocallyNoetherian G.hom⟩
  change (lineBundleNormalizedRepresentation G P R).homEquiv
    ((ObjectProperty.homMk t : T ⟶ Q) ≫
    normalizedFamilyClassifyingMap G.hom η[G].left (Over.w η[G])
      (lineBundleNormalizedRepresentation G P R) Q
      (translationFamilyClass G (𝟙 G) a)) = _
  rw [← normalizedFamilyClassifyingMap_pullback, homEquiv_normalizedFamilyClassifyingMap,
    translationFamilyClass_pullback, Category.comp_id]
  rfl

/-- The universal classifying equation is precisely the normalized Mumford
family, including its correction along the parameter scheme. -/
theorem homEquiv_comp_lineBundleClassMorphism_val
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ G)
    (a : PicardGroup G.left) :
    ((lineBundleNormalizedRepresentation G P R).homEquiv
      (ObjectProperty.homMk (t ≫ lineBundleClassMorphism G P R a))).val =
      translationFamilyClass G t a -
        pullbackClass (pullback.snd G.hom T.obj.hom) (pullbackClass t.left a) := by
  rw [homEquiv_comp_lineBundleClassMorphism, normalized_translationFamilyClass_val]

/-- Isomorphic original line bundles determine the same scheme morphism. -/
theorem lineBundleMorphism_eq_of_iso {L M : LineBundle G.left}
    (e : L.val ≅ M.val) : lineBundleMorphism G P R L = lineBundleMorphism G P R M := by
  apply congrArg (lineBundleClassMorphism G P R)
  exact (class_eq_iff G.left L M).mpr ⟨e⟩

section GroupLaw

variable [LocallyOfFiniteType P.obj.hom]

/-- The actual identity is preserved, without any smoothness or properness
assumption on the Picard representative. -/
theorem lineBundleClassMorphism_pointed (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    η[G] ≫ lineBundleClassMorphism G P R a = η[P.obj] := by
  let := picardCommGrpObj G.hom P R
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨𝟙_ _, inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))⟩
  have h : (ObjectProperty.homMk (η[G] ≫ lineBundleClassMorphism G P R a) : T ⟶ P) =
      ObjectProperty.homMk η[P.obj] := by
    apply (lineBundleNormalizedRepresentation G P R).homEquiv.injective
    rw [homEquiv_comp_lineBundleClassMorphism]
    have hz : translationFamilyClass G η[G] a = 0 := by
      simpa only [MonObj.one_eq_one] using translationFamilyClass_one G T.obj a
    rw [hz, normalizedFamilyClass_zero]
    symm
    simpa only [MonObj.one_eq_one] using
      normalizedRepresentableBy_homEquiv_one G.hom η[G].left (Over.w η[G]) P R T
  exact congrArg (fun f : T ⟶ P => f.hom) h

/-- The zero Picard class gives the original constant identity morphism. -/
theorem lineBundleClassMorphism_zero :
    letI := picardCommGrpObj G.hom P R
    lineBundleClassMorphism G P R 0 = 1 := by
  let := picardCommGrpObj G.hom P R
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨G, LocallyOfFiniteType.isLocallyNoetherian G.hom⟩
  have h : (ObjectProperty.homMk (lineBundleClassMorphism G P R 0) : T ⟶ P) =
      ObjectProperty.homMk (1 : G ⟶ P.obj) := by
    apply (lineBundleNormalizedRepresentation G P R).homEquiv.injective
    have he := homEquiv_comp_lineBundleClassMorphism G P R (T := T) (𝟙 G) 0
    rw [Category.id_comp, translationFamilyClass_zero, normalizedFamilyClass_zero] at he
    rw [he]
    exact (normalizedRepresentableBy_homEquiv_one G.hom η[G].left (Over.w η[G]) P R T).symm
  exact congrArg (fun f : T ⟶ P => f.hom) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor product of line bundles becomes the original product of morphisms
to the supplied Picard group scheme. -/
theorem lineBundleClassMorphism_add (a b : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    lineBundleClassMorphism G P R (a + b) =
      lineBundleClassMorphism G P R a * lineBundleClassMorphism G P R b := by
  let := picardCommGrpObj G.hom P R
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨G, LocallyOfFiniteType.isLocallyNoetherian G.hom⟩
  have h : (ObjectProperty.homMk (lineBundleClassMorphism G P R (a + b)) : T ⟶ P) =
      ObjectProperty.homMk (lineBundleClassMorphism G P R a *
        lineBundleClassMorphism G P R b) := by
    apply (lineBundleNormalizedRepresentation G P R).homEquiv.injective
    rw [normalizedRepresentableBy_homEquiv_mul]
    have he (c : PicardGroup G.left) :
        (lineBundleNormalizedRepresentation G P R).homEquiv'
          (F := (locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
            normalizedPicardFunctor G.hom η[G].left (Over.w η[G]))
          (ObjectProperty.homMk (lineBundleClassMorphism G P R c) : T ⟶ P) =
        normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T.obj
          (translationFamilyClass G (𝟙 G) c) := by
      exact homEquiv_normalizedFamilyClassifyingMap G.hom η[G].left (Over.w η[G])
        (lineBundleNormalizedRepresentation G P R) T (translationFamilyClass G (𝟙 G) c)
    rw [he a, he b]
    change (lineBundleNormalizedRepresentation G P R).homEquiv
        (normalizedFamilyClassifyingMap G.hom η[G].left (Over.w η[G])
          (lineBundleNormalizedRepresentation G P R) T
          (translationFamilyClass G (𝟙 G) (a + b))) = _
    rw [homEquiv_normalizedFamilyClassifyingMap]
    change normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T.obj
        (translationFamilyClass G (𝟙 G) (a + b)) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T.obj
          (translationFamilyClass G (𝟙 G) a) +
        normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T.obj
          (translationFamilyClass G (𝟙 G) b)
    rw [translationFamilyClass_add, map_add]
  exact congrArg (fun f : T ⟶ P => f.hom) h

variable [IsSeparated P.obj.hom]

/-- The original line-bundle morphism is a group homomorphism. Properness
and geometric integrality are used only on the source. -/
theorem isMonHom_lineBundleClassMorphism (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    IsMonHom (lineBundleClassMorphism G P R a) := by
  let := picardCommGrpObj G.hom P R
  exact Group.PointedMorphism.isMonHom_of_geometricallyIntegral_of_isSeparated
    G P.obj _ (lineBundleClassMorphism_pointed G P R a)

omit [IsSeparated P.obj.hom] in
/-- The image lies in the actual identity component of the same Picard scheme. -/
theorem range_lineBundleClassMorphism_subset_identityComponent (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    Set.range (lineBundleClassMorphism G P R a).left ⊆ identityComponent P.obj := by
  let := picardCommGrpObj G.hom P R
  let : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  exact range_subset_identityComponent_of_section P.obj _ η[G]
    (lineBundleClassMorphism_pointed G P R a)

/-- The original line-bundle morphism with codomain restricted to `Pic⁰`.
This definition constructs no second Picard representative. -/
def lineBundleClassMorphismIdentityComponent (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    G ⟶ identityComponentOver P.obj :=
  letI := picardCommGrpObj G.hom P R
  liftIdentityComponent P.obj (lineBundleClassMorphism G P R a)
    (range_lineBundleClassMorphism_subset_identityComponent G P R a)

omit [IsSeparated P.obj.hom] in
@[reassoc (attr := simp)]
theorem lineBundleClassMorphismIdentityComponent_ι (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    lineBundleClassMorphismIdentityComponent G P R a ≫ identityComponentι P.obj =
      lineBundleClassMorphism G P R a := by
  let := picardCommGrpObj G.hom P R
  exact liftIdentityComponent_ι ..

omit [IsSeparated P.obj.hom] in
/-- Identity preservation after the actual open-component factorization. -/
theorem lineBundleClassMorphismIdentityComponent_pointed (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    η[G] ≫ lineBundleClassMorphismIdentityComponent G P R a =
      η[identityComponentOver P.obj] := by
  let := picardCommGrpObj G.hom P R
  rw [← cancel_mono (identityComponentι P.obj), Category.assoc,
    lineBundleClassMorphismIdentityComponent_ι, lineBundleClassMorphism_pointed,
    IsMonHom.one_hom]

/-- The same factored morphism is a group homomorphism, on the original
identity-component group law. -/
theorem isMonHom_lineBundleClassMorphismIdentityComponent (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    IsMonHom (lineBundleClassMorphismIdentityComponent G P R a) := by
  let := picardCommGrpObj G.hom P R
  have : IsSeparated (identityComponentOver P.obj).hom := by
    change IsSeparated ((identityComponent P.obj).ι ≫ P.obj.hom)
    infer_instance
  exact Group.PointedMorphism.isMonHom_of_geometricallyIntegral_of_isSeparated
    G (identityComponentOver P.obj) _
      (lineBundleClassMorphismIdentityComponent_pointed G P R a)

end GroupLaw

end AlgebraicGeometry.Scheme.RelativePicard
