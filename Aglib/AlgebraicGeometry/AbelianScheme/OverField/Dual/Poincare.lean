/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.UniversalRigidified
public import Aglib.AlgebraicGeometry.Picard.IdentityComponent

/-!
# The original Poincare bundle on the actual Picard identity component

For a proper geometrically integral group `G` over a field and the supplied
fppf Picard representative `P,R`, select the one universal rigidified pair
through the existing rigidified comparison. The Poincare pair is its actual
pullback along `picardIdentityComponentι`, hence along the inclusion of the
same `identityComponentOver P.obj`. No second bundle is chosen on Pic0.

The bundle and all its pullbacks exist for arbitrary tests. Classification
uses only the locally Noetherian test schemes represented by `R`. Parameter
unit normalization is pulled back from the base-unit isomorphism, and the
source-origin rigidification is preserved. Properness, smoothness or a
dimension statement for Pic0 is not assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible Scheme.Group

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsProper G.hom] [GeometricallyIntegral G.hom]
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The same representative's one universal pair, with source origin the
original group unit. This specializes the general constructor. -/
abbrev picardUniversalRigidifiedPair :
    RigidifiedPair G.hom η[G].left (by simp) P.obj :=
  fppfUniversalRigidifiedPair G.hom η[G].left (by simp) R

/-- The original universal line bundle on `G × P`. -/
def picardUniversalLineBundle : LineBundle (pullback G.hom P.obj.hom) :=
  (picardUniversalRigidifiedPair G P R).bundle

/-- The selected original universal bundle's source-origin rigidification. -/
def picardUniversalOriginIso :
    (Scheme.Modules.pullback (originSection G.hom η[G].left (by simp) P.obj)).obj
      (picardUniversalLineBundle G P R).val ≅
        (SheafOfModules.unit P.obj.left.ringCatSheaf : P.obj.left.Modules) :=
  (picardUniversalRigidifiedPair G P R).rigidification

variable [LocallyOfFiniteType P.obj.hom]

/-- The Poincare pair is the actual pullback of the one universal pair along
the original identity-component inclusion. -/
def poincareRigidifiedPair :
    RigidifiedPair G.hom η[G].left (by simp) (picardIdentityComponent G.hom P R) :=
  RigidifiedPair.map (picardIdentityComponentι G.hom P R)
    (picardUniversalRigidifiedPair G P R)

/-- The actual Poincare line bundle on `G × Pic0`. -/
def poincareLineBundle :
    LineBundle (pullback G.hom (picardIdentityComponent G.hom P R).hom) :=
  (poincareRigidifiedPair G P R).bundle

/-- The Poincare bundle is the original bundle's literal line-bundle pullback. -/
theorem poincareLineBundle_eq_pullback :
    poincareLineBundle G P R =
      pullbackLineBundle ((familyScheme G.hom).map (picardIdentityComponentι G.hom P R))
        (picardUniversalLineBundle G P R) := rfl

/-- The source-origin rigidification of that same restricted bundle. -/
def poincareOriginIso :
    (Scheme.Modules.pullback (originSection G.hom η[G].left (by simp)
      (picardIdentityComponent G.hom P R))).obj (poincareLineBundle G P R).val ≅
        (SheafOfModules.unit (picardIdentityComponent G.hom P R).left.ringCatSheaf :
          (picardIdentityComponent G.hom P R).left.Modules) :=
  (poincareRigidifiedPair G P R).rigidification

/-- Pullback of the Poincare pair on every test scheme, without extending
the represented test category. -/
def poincarePullback {T : Over (Spec (.of k))}
    (f : T ⟶ picardIdentityComponent G.hom P R) :
    RigidifiedPair G.hom η[G].left (by simp) T :=
  RigidifiedPair.map f (poincareRigidifiedPair G P R)

/-- The original comparison with the same universal pair on `G × P`. -/
def poincareUniversalPullbackIso {T : Over (Spec (.of k))}
    (f : T ⟶ picardIdentityComponent G.hom P R) :
    RigidifiedPair.Iso
      (RigidifiedPair.map (f ≫ picardIdentityComponentι G.hom P R)
        (picardUniversalRigidifiedPair G P R))
      (poincarePullback G P R f) :=
  RigidifiedPair.mapCompIso f (picardIdentityComponentι G.hom P R) _

/-- Classification of the original Poincare pullback on the represented
locally Noetherian tests, through the same supplied representative. -/
theorem poincarePullback_class {T : LocallyNoetherianOver (Spec (.of k))}
    (f : T.obj ⟶ picardIdentityComponent G.hom P R) :
    Quotient.mk _ (poincarePullback G P R f) =
      (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral
        G.hom η[G].left (by simp) R).homEquiv
          (ObjectProperty.homMk (f ≫ picardIdentityComponentι G.hom P R)) := by
  have h : (Quotient.mk _ (poincarePullback G P R f) :
      (rigidifiedPicardFunctor G.hom η[G].left (by simp)).obj (op T.obj)) =
      Quotient.mk _ (RigidifiedPair.map (f ≫ picardIdentityComponentι G.hom P R)
        (picardUniversalRigidifiedPair G P R)) :=
    Quotient.sound ⟨(poincareUniversalPullbackIso G P R f).symm⟩
  exact h.trans (universalRigidifiedPullback_class G.hom η[G].left (by simp)
      (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral
        G.hom η[G].left (by simp) R)
      (ObjectProperty.homMk (f ≫ picardIdentityComponentι G.hom P R)))

/-- The original fppf representation classifies the actual Poincare
pullback bundle, on the same represented test schemes. -/
theorem poincarePullback_fppfClass {T : LocallyNoetherianOver (Spec (.of k))}
    (f : T.obj ⟶ picardIdentityComponent G.hom P R) :
    ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app (op T.obj)).hom
        (classOf _ (poincarePullback G P R f).bundle) =
      R.homEquiv (ObjectProperty.homMk (f ≫ picardIdentityComponentι G.hom P R)) := by
  have h : classOf _ (poincarePullback G P R f).bundle =
      classOf _ (RigidifiedPair.map (f ≫ picardIdentityComponentι G.hom P R)
        (picardUniversalRigidifiedPair G P R)).bundle :=
    Quotient.sound ⟨(poincareUniversalPullbackIso G P R f).iso.symm⟩
  exact (congrArg ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app
    (op T.obj)).hom h).trans
      (fppfUniversalRigidifiedPullback_fppfClass G.hom η[G].left (by simp) R
        (ObjectProperty.homMk (f ≫ picardIdentityComponentι G.hom P R)))

/-- The represented class equation gives an actual rigidified Poincare
pullback isomorphism. Its class premise is the original one supplied by the
classifying-map consumer. -/
def poincarePullbackIsoOfClass {T : LocallyNoetherianOver (Spec (.of k))}
    (f : T.obj ⟶ picardIdentityComponent G.hom P R)
    (Q : RigidifiedPair G.hom η[G].left (by simp) T.obj)
    (h : (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral
      G.hom η[G].left (by simp) R).homEquiv
        (ObjectProperty.homMk (f ≫ picardIdentityComponentι G.hom P R)) =
          Quotient.mk _ Q) : RigidifiedPair.Iso (poincarePullback G P R f) Q :=
  Classical.choice (Quotient.exact ((poincarePullback_class G P R f).trans h))

/-- A classifying equation in the original fppf representative gives the
actual rigidified isomorphism, without changing that representative. -/
def poincarePullbackIsoOfFppfClass {T : LocallyNoetherianOver (Spec (.of k))}
    (f : T.obj ⟶ picardIdentityComponent G.hom P R)
    (Q : RigidifiedPair G.hom η[G].left (by simp) T.obj)
    (h : R.homEquiv (ObjectProperty.homMk (f ≫ picardIdentityComponentι G.hom P R)) =
      ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app (op T.obj)).hom
        (classOf _ Q.bundle)) : RigidifiedPair.Iso (poincarePullback G P R f) Q := by
  let E := rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral
    G.hom η[G].left (by simp)
  have hq : (Quotient.mk _ (poincarePullback G P R f) :
      (rigidifiedPicardFunctor G.hom η[G].left (by simp)).obj (op T.obj)) =
      Quotient.mk _ Q := by
    apply (E.app (op T.obj)).toEquiv.injective
    exact (rigidifiedPair_fppfClass G.hom η[G].left (by simp)
      (poincarePullback G P R f)).trans
        ((poincarePullback_fppfClass G P R f).trans
          (h.trans (rigidifiedPair_fppfClass G.hom η[G].left (by simp) Q).symm))
  exact Classical.choice (Quotient.exact hq)

/-- Rigidified isomorphisms from the same Poincare pullback are unique on
all tests, with the structure-sheaf condition supplied from the geometry. -/
theorem poincarePullbackIso_unique {T : Over (Spec (.of k))}
    (f : T ⟶ picardIdentityComponent G.hom P R)
    (Q : RigidifiedPair G.hom η[G].left (by simp) T)
    (e e' : RigidifiedPair.Iso (poincarePullback G P R f) Q) : e = e' :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (by simp) _ _

/-- Identity pullback of the actual Poincare pair. -/
def poincarePullbackIdIso :
    RigidifiedPair.Iso (poincarePullback G P R (𝟙 (picardIdentityComponent G.hom P R)))
      (poincareRigidifiedPair G P R) :=
  RigidifiedPair.mapIdIso _

/-- Composition pullback of the actual Poincare pair. -/
def poincarePullbackCompIso {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (g : T ⟶ picardIdentityComponent G.hom P R) :
    RigidifiedPair.Iso (poincarePullback G P R (f ≫ g))
      (RigidifiedPair.map f (poincarePullback G P R g)) :=
  RigidifiedPair.mapCompIso f g _

/-- The whole left-unit equation for actual Poincare pullback. -/
theorem poincarePullbackCompIso_id_left {T : Over (Spec (.of k))}
    (f : T ⟶ picardIdentityComponent G.hom P R) :
    (poincarePullbackCompIso G P R (𝟙 T) f).trans
        (RigidifiedPair.mapIdIso (poincarePullback G P R f)) =
      RigidifiedPair.mapCongrIso (Category.id_comp f) (poincareRigidifiedPair G P R) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (by simp) _ _

/-- The whole right-unit equation for actual Poincare pullback. -/
theorem poincarePullbackCompIso_id_right {T : Over (Spec (.of k))}
    (f : T ⟶ picardIdentityComponent G.hom P R) :
    (poincarePullbackCompIso G P R f (𝟙 (picardIdentityComponent G.hom P R))).trans
        (RigidifiedPair.Iso.map f (poincarePullbackIdIso G P R)) =
      RigidifiedPair.mapCongrIso (Category.comp_id f) (poincareRigidifiedPair G P R) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (by simp) _ _

/-- The original whole associativity equation for the Poincare pullback
comparisons, on arbitrary test schemes. -/
theorem poincarePullbackCompIso_assoc {T₀ T₁ T₂ : Over (Spec (.of k))}
    (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂) (h : T₂ ⟶ picardIdentityComponent G.hom P R) :
    (poincarePullbackCompIso G P R (f ≫ g) h).trans
        (RigidifiedPair.mapCompIso f g (poincarePullback G P R h)) =
      (RigidifiedPair.mapCongrIso (Category.assoc f g h) (poincareRigidifiedPair G P R)).trans
        ((poincarePullbackCompIso G P R f (g ≫ h)).trans
          (RigidifiedPair.Iso.map f (poincarePullbackCompIso G P R g h))) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (by simp) _ _

/-- The actual Poincare pair is trivial along the parameter identity on
every test scheme. This is transported from the original universal pair's
base-unit isomorphism using the actual inclusion's group-unit equation. -/
def poincareUnitIso (T : Over (Spec (.of k))) :
    RigidifiedPair.Iso
      (poincarePullback G P R (1 : T ⟶ picardIdentityComponent G.hom P R))
      (trivialRigidifiedPair G.hom η[G].left (by simp) T) := by
  letI := picardCommGrpObj G.hom P R
  have : IsMonHom (picardIdentityComponentι G.hom P R) :=
    isMonHom_picardIdentityComponentι G.hom P R
  exact (poincareUniversalPullbackIso G P R 1).symm.trans
    ((RigidifiedPair.mapCongrIso (MonObj.one_comp (picardIdentityComponentι G.hom P R))
      (picardUniversalRigidifiedPair G P R)).trans
        (fppfUniversalRigidifiedUnitIso G.hom η[G].left (by simp) R T))

/-- The parameter-unit isomorphism is the unique rigidified one. -/
theorem poincareUnitIso_unique (T : Over (Spec (.of k)))
    (e : RigidifiedPair.Iso
      (poincarePullback G P R (1 : T ⟶ picardIdentityComponent G.hom P R))
      (trivialRigidifiedPair G.hom η[G].left (by simp) T)) :
    e = poincareUnitIso G P R T :=
  poincarePullbackIso_unique G P R _ _ _ _

/-- Parameter-unit normalization commutes with arbitrary test pullback,
through the original composition and trivial-pair comparisons. -/
theorem poincareUnitIso_naturality {T T' : Over (Spec (.of k))} (f : T' ⟶ T) :
    poincareUnitIso G P R T' =
      (RigidifiedPair.mapCongrIso
        (show (1 : T' ⟶ picardIdentityComponent G.hom P R) =
          f ≫ (1 : T ⟶ picardIdentityComponent G.hom P R) from (MonObj.comp_one f).symm)
        (poincareRigidifiedPair G P R)).trans
        ((poincarePullbackCompIso G P R f 1).trans
          ((RigidifiedPair.Iso.map f (poincareUnitIso G P R T)).trans
            (trivialRigidifiedPairMapIso G.hom η[G].left (by simp) f))) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (by simp) _ _

set_option backward.isDefEq.respectTransparency false in
/-- Triviality along the original parameter-unit map `G → G × Pic0`, with
domain the original scheme `G`. The canonical right-unitor comparison is
proved on whole scheme maps before applying module pullback. -/
def poincareParameterUnitIso :
    (Scheme.Modules.pullback
      (lift (𝟙 G) (1 : G ⟶ picardIdentityComponent G.hom P R)).left).obj
        (poincareLineBundle G P R).val ≅
          (SheafOfModules.unit G.left.ringCatSheaf : G.left.Modules) := by
  let D := picardIdentityComponent G.hom P R
  let B := 𝟙_ (Over (Spec (.of k)))
  let t : B ⟶ D := 1
  let q : (G ⊗ B).left ⟶ (G ⊗ D).left := (familyScheme G.hom).map t
  let a : G.left ⟶ (G ⊗ B).left := (ρ_ G).inv.left
  have h : a ≫ q = (lift (𝟙 G) (1 : G ⟶ D)).left := by
    change (ρ_ G).inv.left ≫ (G ◁ t).left = _
    rw [← Over.comp_left]
    apply congrArg (fun f : G ⟶ G ⊗ D => f.left)
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, rightUnitor_inv_fst, lift_fst]
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, rightUnitor_inv_snd, lift_snd]
      exact MonObj.comp_one (toUnit G)
  exact (Scheme.Modules.pullbackCongr h.symm).app (poincareLineBundle G P R).val ≪≫
    ((Scheme.Modules.pullbackComp a q).app (poincareLineBundle G P R).val).symm ≪≫
    (Scheme.Modules.pullback a).mapIso (poincareUnitIso G P R B).iso ≪≫
    (Scheme.Modules.pullback a).mapIso
      (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
        SheafOfModules.unit (G ⊗ B).left.ringCatSheaf)) ≪≫
    Scheme.Modules.pullbackUnitIso a

end AlgebraicGeometry.Scheme.RelativePicard
