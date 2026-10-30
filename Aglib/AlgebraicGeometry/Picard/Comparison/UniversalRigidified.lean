/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Rigidified
public import Aglib.AlgebraicGeometry.Picard.Comparison.RepresentableBy
public import Aglib.AlgebraicGeometry.Picard.GroupLaw
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Mathlib.CategoryTheory.Yoneda

/-!
# One universal rigidified pair for the supplied Picard representative

The universal pair is one representative of `Rr.homEquiv (𝟙 P)`. Its actual
bundle and rigidification are selected once. Every later pullback uses that
same pair and the existing `RigidifiedPair.map`.

Pullback objects and their identity/composition laws are defined on every
test scheme. Classification uses only locally Noetherian test schemes, which
is the stated domain of `Rr`. The classifying isomorphisms are actual
rigidification-preserving isomorphisms; universal O-connectedness makes them
unique and proves their naturality. No additional universal-bundle structure
or assumed coherence field is introduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

set_option backward.isDefEq.respectTransparency false in
/-- The original trivial line bundle with its canonical origin rigidification. -/
def trivialRigidifiedPair (T : Over S) : RigidifiedPair p o ho T where
  bundle := trivialLineBundle (pullback p T.hom)
  rigidification :=
    (Scheme.Modules.pullback (originSection p o ho T)).mapIso
      (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
        SheafOfModules.unit (pullback p T.hom).ringCatSheaf)) ≪≫
      Scheme.Modules.pullbackUnitIso (originSection p o ho T)

/-- The trivial rigidified pair corresponds to the zero normalized class. -/
theorem rigidifiedNormalizedIso_hom_trivial (T : Over S) :
    (rigidifiedNormalizedIso p o ho).hom.app (op T)
      (Quotient.mk _ (trivialRigidifiedPair p o ho T)) = 0 := by
  apply Subtype.ext
  exact classOf_trivial _

set_option backward.isDefEq.respectTransparency false in
/-- The original trivial rigidified pair commutes with arbitrary pullback. -/
def trivialRigidifiedPairMapIso {T T' : Over S} (f : T' ⟶ T) :
    RigidifiedPair.Iso (RigidifiedPair.map f (trivialRigidifiedPair p o ho T))
      (trivialRigidifiedPair p o ho T') :=
  RigidifiedPair.isoOfBundleIso _ _
    ((Scheme.Modules.pullback ((familyScheme p).map f)).mapIso
        (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
          SheafOfModules.unit (pullback p T.hom).ringCatSheaf)) ≪≫
      Scheme.Modules.pullbackUnitIso ((familyScheme p).map f) ≪≫
      (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
        SheafOfModules.unit (pullback p T'.hom).ringCatSheaf)).symm)

variable {P : LocallyNoetherianOver S}
  (Rr : ((locallyNoetherianOverInclusion S).op ⋙
    rigidifiedPicardFunctor p o ho).RepresentableBy P)

/-- One selected representative of the universal rigidified class. Every
construction below uses this same pair. -/
def universalRigidifiedPair : RigidifiedPair p o ho P.obj :=
  Quotient.out (Rr.homEquiv (𝟙 P))

/-- The selected pair represents the original universal element. -/
theorem universalRigidifiedPair_class :
    Quotient.mk _ (universalRigidifiedPair p o ho Rr) = Rr.homEquiv (𝟙 P) :=
  Quotient.out_eq _

/-- Pullback of the one universal pair, defined on arbitrary test schemes. -/
def universalRigidifiedPullback {T : Over S} (f : T ⟶ P.obj) :
    RigidifiedPair p o ho T :=
  RigidifiedPair.map f (universalRigidifiedPair p o ho Rr)

/-- On the represented locally Noetherian tests, the actual pulled-back pair
has the original represented class. -/
theorem universalRigidifiedPullback_class {T : LocallyNoetherianOver S} (f : T ⟶ P) :
    Quotient.mk _ (universalRigidifiedPullback p o ho Rr f.hom) = Rr.homEquiv f := by
  have h := congrArg (fun a : (rigidifiedPicardFunctor p o ho).obj (op P.obj) =>
    (rigidifiedPicardFunctor p o ho).map f.hom.op a)
      (universalRigidifiedPair_class p o ho Rr)
  exact h.trans ((Rr.homEquiv_comp f (𝟙 P)).symm.trans
    (congrArg Rr.homEquiv (Category.comp_id f)))

/-- The classifying morphism of a pair on a represented test scheme. -/
def rigidifiedPairClassifyingMap {T : LocallyNoetherianOver S}
    (Q : RigidifiedPair p o ho T.obj) : T ⟶ P :=
  Rr.homEquiv.symm (Quotient.mk _ Q)

/-- The classifying morphism commutes with original test-scheme pullback. -/
theorem rigidifiedPairClassifyingMap_pullback {T T' : LocallyNoetherianOver S}
    (f : T' ⟶ T) (Q : RigidifiedPair p o ho T.obj) :
    rigidifiedPairClassifyingMap p o ho Rr (RigidifiedPair.map f.hom Q) =
      f ≫ rigidifiedPairClassifyingMap p o ho Rr Q :=
  (Rr.comp_homEquiv_symm (Quotient.mk _ Q) f).symm

/-- The original universal pair has the identity classifying morphism. -/
theorem rigidifiedPairClassifyingMap_universal :
    rigidifiedPairClassifyingMap p o ho Rr (universalRigidifiedPair p o ho Rr) = 𝟙 P :=
  (congrArg Rr.homEquiv.symm (universalRigidifiedPair_class p o ho Rr)).trans
    (Rr.homEquiv.symm_apply_apply _)

/-- Pulling the universal pair back by a given morphism recovers that same
classifying morphism, on the represented tests. -/
theorem rigidifiedPairClassifyingMap_universalPullback {T : LocallyNoetherianOver S}
    (f : T ⟶ P) :
    rigidifiedPairClassifyingMap p o ho Rr
        (universalRigidifiedPullback p o ho Rr f.hom) = f :=
  (congrArg Rr.homEquiv.symm (universalRigidifiedPullback_class p o ho Rr f)).trans
    (Rr.homEquiv.symm_apply_apply _)

/-- The represented class equation is exactly existence of an actual
rigidified isomorphism with the original universal pullback. -/
theorem nonempty_universalRigidifiedPullbackIso_iff {T : LocallyNoetherianOver S}
    (f : T ⟶ P) (Q : RigidifiedPair p o ho T.obj) :
    Nonempty (RigidifiedPair.Iso (universalRigidifiedPullback p o ho Rr f.hom) Q) ↔
      Rr.homEquiv f = Quotient.mk _ Q := by
  constructor
  · rintro ⟨e⟩
    exact (universalRigidifiedPullback_class p o ho Rr f).symm.trans
      (Quotient.sound ⟨e⟩)
  · intro h
    exact Quotient.exact ((universalRigidifiedPullback_class p o ho Rr f).trans h)

/-- The classifying isomorphism is an isomorphism of the actual rigidified
pairs, selected from the original represented class equation. -/
def rigidifiedPairClassifyingIso {T : LocallyNoetherianOver S}
    (Q : RigidifiedPair p o ho T.obj) :
    RigidifiedPair.Iso
      (universalRigidifiedPullback p o ho Rr (rigidifiedPairClassifyingMap p o ho Rr Q).hom)
      Q :=
  Classical.choice ((nonempty_universalRigidifiedPullbackIso_iff p o ho Rr _ Q).mpr
    (Rr.homEquiv.apply_symm_apply _))

/-- The original classifying morphism is the unique morphism whose actual
universal pullback is rigidified-isomorphic to the given pair. -/
theorem existsUnique_rigidifiedPairClassifyingMap {T : LocallyNoetherianOver S}
    (Q : RigidifiedPair p o ho T.obj) :
    ∃! f : T ⟶ P,
      Nonempty (RigidifiedPair.Iso (universalRigidifiedPullback p o ho Rr f.hom) Q) := by
  refine ⟨rigidifiedPairClassifyingMap p o ho Rr Q,
    ⟨rigidifiedPairClassifyingIso p o ho Rr Q⟩, ?_⟩
  intro f hf
  apply Rr.homEquiv.injective
  exact ((nonempty_universalRigidifiedPullbackIso_iff p o ho Rr f Q).mp hf).trans
    (Rr.homEquiv.apply_symm_apply _).symm

/-- The classifying rigidified isomorphism is unique under the original
structure-sheaf isomorphism at that test scheme. -/
theorem rigidifiedPairClassifyingIso_unique {T : LocallyNoetherianOver S}
    [IsIso (pullback.snd p T.obj.hom).c] (Q : RigidifiedPair p o ho T.obj)
    (e : RigidifiedPair.Iso
      (universalRigidifiedPullback p o ho Rr (rigidifiedPairClassifyingMap p o ho Rr Q).hom)
      Q) : e = rigidifiedPairClassifyingIso p o ho Rr Q :=
  RigidifiedPair.Iso.eq_of_isIso_c p o ho _ _

/-- Identity pullback of the same universal pair. -/
def universalRigidifiedIdentityIso :
    RigidifiedPair.Iso (universalRigidifiedPullback p o ho Rr (𝟙 P.obj))
      (universalRigidifiedPair p o ho Rr) :=
  RigidifiedPair.mapIdIso _

/-- The classifying isomorphism of the universal pair is the original
identity-pullback comparison, after its proved classifying-map identity. -/
theorem rigidifiedPairClassifyingIso_universal [IsIso (pullback.snd p P.obj.hom).c] :
    rigidifiedPairClassifyingIso p o ho Rr (universalRigidifiedPair p o ho Rr) =
      (RigidifiedPair.mapCongrIso
        (congrArg (fun f : P ⟶ P => f.hom) (rigidifiedPairClassifyingMap_universal p o ho Rr))
        (universalRigidifiedPair p o ho Rr)).trans
          (universalRigidifiedIdentityIso p o ho Rr) :=
  RigidifiedPair.Iso.eq_of_isIso_c p o ho _ _

/-- On an original universal pullback, the classifying isomorphism is the
comparison induced by the proved equality with its original classifying map. -/
theorem rigidifiedPairClassifyingIso_universalPullback {T : LocallyNoetherianOver S}
    (f : T ⟶ P) [IsIso (pullback.snd p T.obj.hom).c] :
    rigidifiedPairClassifyingIso p o ho Rr (universalRigidifiedPullback p o ho Rr f.hom) =
      RigidifiedPair.mapCongrIso
        (congrArg (fun g : T ⟶ P => g.hom)
          (rigidifiedPairClassifyingMap_universalPullback p o ho Rr f))
        (universalRigidifiedPair p o ho Rr) :=
  RigidifiedPair.Iso.eq_of_isIso_c p o ho _ _

/-- Composition pullback of the same universal pair, on all test schemes. -/
def universalRigidifiedCompIso {T T' : Over S} (f : T' ⟶ T) (g : T ⟶ P.obj) :
    RigidifiedPair.Iso (universalRigidifiedPullback p o ho Rr (f ≫ g))
      (RigidifiedPair.map f (universalRigidifiedPullback p o ho Rr g)) :=
  RigidifiedPair.mapCompIso f g _

/-- The whole left-unit equation for universal rigidified pullback. -/
theorem universalRigidifiedCompIso_id_left {T : Over S} (f : T ⟶ P.obj)
    [IsIso (pullback.snd p T.hom).c] :
    (universalRigidifiedCompIso p o ho Rr (𝟙 T) f).trans
        (RigidifiedPair.mapIdIso (universalRigidifiedPullback p o ho Rr f)) =
      RigidifiedPair.mapCongrIso (Category.id_comp f) (universalRigidifiedPair p o ho Rr) :=
  RigidifiedPair.mapCompIso_id_left f _

/-- The whole right-unit equation for universal rigidified pullback. -/
theorem universalRigidifiedCompIso_id_right {T : Over S} (f : T ⟶ P.obj)
    [IsIso (pullback.snd p T.hom).c] :
    (universalRigidifiedCompIso p o ho Rr f (𝟙 P.obj)).trans
        (RigidifiedPair.Iso.map f (universalRigidifiedIdentityIso p o ho Rr)) =
      RigidifiedPair.mapCongrIso (Category.comp_id f) (universalRigidifiedPair p o ho Rr) :=
  RigidifiedPair.mapCompIso_id_right f _

/-- The whole associativity equation for the original universal pullback
comparisons, before evaluation at any bundle coefficient. -/
theorem universalRigidifiedCompIso_assoc {T₀ T₁ T₂ : Over S}
    (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂) (h : T₂ ⟶ P.obj)
    [IsIso (pullback.snd p T₀.hom).c] :
    (universalRigidifiedCompIso p o ho Rr (f ≫ g) h).trans
        (RigidifiedPair.mapCompIso f g (universalRigidifiedPullback p o ho Rr h)) =
      (RigidifiedPair.mapCongrIso (Category.assoc f g h) (universalRigidifiedPair p o ho Rr)).trans
        ((universalRigidifiedCompIso p o ho Rr f (g ≫ h)).trans
          (RigidifiedPair.Iso.map f (universalRigidifiedCompIso p o ho Rr g h))) :=
  RigidifiedPair.mapCompIso_assoc f g h _

/-- The original naturality path for classifying rigidified isomorphisms. -/
def rigidifiedPairClassifyingPullbackIso {T T' : LocallyNoetherianOver S}
    (f : T' ⟶ T) (Q : RigidifiedPair p o ho T.obj) :
    RigidifiedPair.Iso
      (universalRigidifiedPullback p o ho Rr
        (rigidifiedPairClassifyingMap p o ho Rr (RigidifiedPair.map f.hom Q)).hom)
      (RigidifiedPair.map f.hom Q) :=
  (RigidifiedPair.mapCongrIso
      (congrArg (fun g : T' ⟶ P => g.hom)
        (rigidifiedPairClassifyingMap_pullback p o ho Rr f Q))
      (universalRigidifiedPair p o ho Rr)).trans
    ((universalRigidifiedCompIso p o ho Rr f.hom
        (rigidifiedPairClassifyingMap p o ho Rr Q).hom).trans
      (RigidifiedPair.Iso.map f.hom (rigidifiedPairClassifyingIso p o ho Rr Q)))

/-- Naturality is proved by the existing uniqueness theorem, for the two
actual rigidification-preserving paths with the same original endpoints. -/
theorem rigidifiedPairClassifyingIso_naturality {T T' : LocallyNoetherianOver S}
    (f : T' ⟶ T) (Q : RigidifiedPair p o ho T.obj)
    [IsIso (pullback.snd p T'.obj.hom).c] :
    rigidifiedPairClassifyingIso p o ho Rr (RigidifiedPair.map f.hom Q) =
      rigidifiedPairClassifyingPullbackIso p o ho Rr f Q :=
  RigidifiedPair.Iso.eq_of_isIso_c p o ho _ _

section FppfRepresentation

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The same fppf representative's one universal rigidified pair, using the
proved rigidified comparison and no second bundle choice. -/
def fppfUniversalRigidifiedPair : RigidifiedPair p o ho P.obj :=
  universalRigidifiedPair p o ho
    (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R)

/-- The proved whole rigidified/fppf comparison evaluates to the original
quotient and sheafification maps on the original line bundle. -/
theorem rigidifiedPair_fppfClass {T : Over S} (Q : RigidifiedPair p o ho T) :
    (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).hom.app (op T)
        (Quotient.mk _ Q) =
      ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T)).hom (classOf _ Q.bundle) := by
  rw [rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral_hom]
  change ((toFppfPicardSheaf p).app (op T)).hom
      ((rigidifiedRelativeIso p o ho).hom.app (op T) (Quotient.mk _ Q)) =
    ((toFppfPicardSheaf p).app (op T)).hom (QuotientAddGroup.mk (classOf _ Q.bundle))
  exact congrArg ((toFppfPicardSheaf p).app (op T)).hom
    (rigidifiedRelativeIso_hom_app_mk p o ho Q)

/-- The selected universal bundle has the original universal fppf class for
the same representative, with no new bundle choice. -/
theorem fppfUniversalRigidifiedPair_fppfClass :
    ((quotientProjection p ≫ toFppfPicardSheaf p).app (op P.obj)).hom
      (classOf _ (fppfUniversalRigidifiedPair p o ho R).bundle) = R.homEquiv (𝟙 P) := by
  let E := rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho
  have h := congrArg (E.hom.app (op P.obj))
    (universalRigidifiedPair_class p o ho
      (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R))
  exact (rigidifiedPair_fppfClass p o ho (fppfUniversalRigidifiedPair p o ho R)).symm.trans
    (h.trans ((E.app (op P.obj)).toEquiv.apply_symm_apply (R.homEquiv (𝟙 P))))

/-- Original pullback classification in the original fppf representation,
evaluated on the actual bundle, only on the represented test category. -/
theorem fppfUniversalRigidifiedPullback_fppfClass {T : LocallyNoetherianOver S}
    (f : T ⟶ P) :
    ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T.obj)).hom
        (classOf _ (RigidifiedPair.map f.hom (fppfUniversalRigidifiedPair p o ho R)).bundle) =
      R.homEquiv f := by
  let E := rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho
  have h := congrArg (E.hom.app (op T.obj))
    (universalRigidifiedPullback_class p o ho
      (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R) f)
  exact (rigidifiedPair_fppfClass p o ho
    (RigidifiedPair.map f.hom (fppfUniversalRigidifiedPair p o ho R))).symm.trans
      (h.trans ((E.app (op T.obj)).toEquiv.apply_symm_apply (R.homEquiv f)))

/-- The actual trivial rigidified pair has zero original fppf Picard class. -/
theorem rigidifiedFppfIso_hom_trivial (T : Over S) :
    (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).hom.app (op T)
      (Quotient.mk _ (trivialRigidifiedPair p o ho T)) =
        (0 : (fppfPicardSheaf p).obj.obj (op T)) := by
  rw [rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral_hom]
  change ((toFppfPicardSheaf p).app (op T)).hom
    (QuotientAddGroup.mk (classOf _ (trivialLineBundle (pullback p T.hom)))) = 0
  exact map_zero _

variable [LocallyOfFiniteType P.obj.hom]

/-- The same rigidified representation sends the original Picard group unit
to the actual trivial rigidified pair, on represented tests only. -/
theorem rigidifiedRepresentableBy_homEquiv_one (T : LocallyNoetherianOver S) :
    letI := picardCommGrpObj p P R
    (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R).homEquiv
      (ObjectProperty.homMk (1 : T.obj ⟶ P.obj)) =
        Quotient.mk _ (trivialRigidifiedPair p o ho T.obj) := by
  let := picardCommGrpObj p P R
  let E := rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho
  apply (E.app (op T.obj)).toEquiv.injective
  have h := (E.app (op T.obj)).toEquiv.apply_symm_apply
    (R.homEquiv (ObjectProperty.homMk (1 : T.obj ⟶ P.obj)))
  exact (h.trans (picard_homEquiv_one p P R T)).trans
    (rigidifiedFppfIso_hom_trivial p o ho T.obj).symm

/-- Unit normalization on a represented locally Noetherian test scheme,
through the original universal pullback and original Picard group unit. -/
def fppfUniversalRigidifiedUnitIsoLN (T : LocallyNoetherianOver S) :
    letI := picardCommGrpObj p P R
    RigidifiedPair.Iso (RigidifiedPair.map (1 : T.obj ⟶ P.obj)
      (fppfUniversalRigidifiedPair p o ho R)) (trivialRigidifiedPair p o ho T.obj) := by
  letI := picardCommGrpObj p P R
  exact Classical.choice
    ((nonempty_universalRigidifiedPullbackIso_iff p o ho
      (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R)
      (ObjectProperty.homMk (1 : T.obj ⟶ P.obj))
      (trivialRigidifiedPair p o ho T.obj)).mpr
        (rigidifiedRepresentableBy_homEquiv_one p o ho R T))

/-- Unit normalization on every test scheme. It is the pullback of the
proved base-unit isomorphism, not an extension of the representability claim. -/
def fppfUniversalRigidifiedUnitIso (T : Over S) :
    letI := picardCommGrpObj p P R
    RigidifiedPair.Iso (RigidifiedPair.map (1 : T ⟶ P.obj)
      (fppfUniversalRigidifiedPair p o ho R)) (trivialRigidifiedPair p o ho T) := by
  letI := picardCommGrpObj p P R
  let T₀ : LocallyNoetherianOver S :=
    ⟨𝟙_ (Over S), by change IsLocallyNoetherian S; infer_instance⟩
  exact (RigidifiedPair.mapCongrIso (MonObj.comp_one (toUnit T)).symm
      (fppfUniversalRigidifiedPair p o ho R)).trans
    ((RigidifiedPair.mapCompIso (toUnit T) (1 : (𝟙_ (Over S)) ⟶ P.obj)
      (fppfUniversalRigidifiedPair p o ho R)).trans
      ((RigidifiedPair.Iso.map (toUnit T) (fppfUniversalRigidifiedUnitIsoLN p o ho R T₀)).trans
        (trivialRigidifiedPairMapIso p o ho (toUnit T))))

/-- The actual unit rigidified isomorphism is unique under the supplied
proper flat geometrically integral geometry, for arbitrary test schemes. -/
theorem fppfUniversalRigidifiedUnitIso_unique (T : Over S) :
    letI := picardCommGrpObj p P R
    ∀ e : RigidifiedPair.Iso (RigidifiedPair.map (1 : T ⟶ P.obj)
      (fppfUniversalRigidifiedPair p o ho R)) (trivialRigidifiedPair p o ho T),
      e = fppfUniversalRigidifiedUnitIso p o ho R T := by
  let := picardCommGrpObj p P R
  intro e
  exact RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral p o ho _ _

/-- The original unit normalization is natural on arbitrary test schemes;
the two actual paths preserve the original source rigidification. -/
theorem fppfUniversalRigidifiedUnitIso_naturality {T T' : Over S} (f : T' ⟶ T) :
    letI := picardCommGrpObj p P R
    fppfUniversalRigidifiedUnitIso p o ho R T' =
      (RigidifiedPair.mapCongrIso
        (show (1 : T' ⟶ P.obj) = f ≫ (1 : T ⟶ P.obj) from (MonObj.comp_one f).symm)
        (fppfUniversalRigidifiedPair p o ho R)).trans
        ((RigidifiedPair.mapCompIso f (1 : T ⟶ P.obj)
          (fppfUniversalRigidifiedPair p o ho R)).trans
          ((RigidifiedPair.Iso.map f (fppfUniversalRigidifiedUnitIso p o ho R T)).trans
            (trivialRigidifiedPairMapIso p o ho f))) := by
  let := picardCommGrpObj p P R
  exact RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral p o ho _ _

end FppfRepresentation

end AlgebraicGeometry.Scheme.RelativePicard
