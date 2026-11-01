/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTorsorRepresentation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TorsorAction
public import Aglib.CategoryTheory.Sites.Representable.LiftedYoneda
public import Aglib.CategoryTheory.Sites.Torsors.RepresentedIso

/-!
# Actual scheme actions representing finite sheaf torsors

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Morphisms are recovered by
Yoneda evaluation on finite étale test schemes. The action and difference
morphisms then extend the sheaf torsor action to every scheme test object.
No morphism, product, action, or classification comparison is a premise.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (toEtale)
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] Over.cartesianMonoidalCategory
  Scheme.FiniteEtale.GroupDescent.coverCartesian
variable {X : Scheme.{u}}

/-- Postcomposition of genuine finite étale scheme sections. -/
def finiteRepresentedSetSheafMap {Y Z : Scheme.FiniteEtale X} (f : Y.obj ⟶ Z.obj) :
    finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z :=
  ⟨LiftedRestrictedYoneda.map.{u + 1} (Scheme.Etale.forget X) f⟩

/-- The small-site Yoneda inverse evaluates on the identity section of Y. -/
def finiteRepresentedSetSheafPreimage {Y Z : Scheme.FiniteEtale X}
    (q : finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z) : Y.obj ⟶ Z.obj :=
  LiftedRestrictedYoneda.preimage.{u + 1} (Scheme.Etale.forget X)
    (Y := (toEtale X).obj Y) (Z := (toEtale X).obj Z) q.hom

@[simp] theorem finiteRepresentedSetSheafPreimage_map {Y Z : Scheme.FiniteEtale X}
    (f : Y.obj ⟶ Z.obj) :
    finiteRepresentedSetSheafPreimage (finiteRepresentedSetSheafMap f) = f :=
  LiftedRestrictedYoneda.preimage_map.{u + 1} (Scheme.Etale.forget X)
    (Y := (toEtale X).obj Y) (Z := (toEtale X).obj Z) f

/-- Naturality recovers every component from the identity section. -/
theorem finiteRepresentedSetSheafMap_preimage {Y Z : Scheme.FiniteEtale X}
    (q : finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z) :
    finiteRepresentedSetSheafMap (finiteRepresentedSetSheafPreimage q) = q := by
  apply Sheaf.hom_ext
  exact LiftedRestrictedYoneda.map_preimage.{u + 1} (Scheme.Etale.forget X)
    (Y := (toEtale X).obj Y) (Z := (toEtale X).obj Z) q.hom

/-- Full faithfulness is a proved Yoneda equivalence, not a representability premise. -/
def finiteRepresentedSetSheafHomEquiv (Y Z : Scheme.FiniteEtale X) :
    (Y.obj ⟶ Z.obj) ≃ (finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z) :=
  LiftedRestrictedYoneda.sheafHomEquiv.{u + 1} (Scheme.Etale.forget X)
    (Scheme.smallEtaleTopology X) ((toEtale X).obj Y) ((toEtale X).obj Z)
    (finiteRepresentedSetSheaf Y).property (finiteRepresentedSetSheaf Z).property

@[simp] theorem finiteRepresentedSetSheafMap_id (Y : Scheme.FiniteEtale X) :
    finiteRepresentedSetSheafMap (𝟙 Y.obj) = 𝟙 _ := by
  apply Sheaf.hom_ext
  exact LiftedRestrictedYoneda.map_id.{u + 1} (Scheme.Etale.forget X) Y.obj

@[simp] theorem finiteRepresentedSetSheafMap_comp {Y Z W : Scheme.FiniteEtale X}
    (f : Y.obj ⟶ Z.obj) (g : Z.obj ⟶ W.obj) :
    finiteRepresentedSetSheafMap (f ≫ g) =
      finiteRepresentedSetSheafMap f ≫ finiteRepresentedSetSheafMap g := by
  apply Sheaf.hom_ext
  exact LiftedRestrictedYoneda.map_comp.{u + 1} (Scheme.Etale.forget X) f g

/-- Yoneda sends an actual scheme isomorphism to an actual set-sheaf isomorphism. -/
def finiteRepresentedSetSheafMapIso {Y Z : Scheme.FiniteEtale X} (e : Y.obj ≅ Z.obj) :
    finiteRepresentedSetSheaf Y ≅ finiteRepresentedSetSheaf Z :=
  LiftedRestrictedYoneda.sheafMapIso.{u + 1} (Scheme.Etale.forget X)
    (Scheme.smallEtaleTopology X) (finiteRepresentedSetSheaf Y).property
    (finiteRepresentedSetSheaf Z).property e

/-- An actual sheaf isomorphism uniquely determines an actual scheme isomorphism. -/
def finiteRepresentedSetSheafIso {Y Z : Scheme.FiniteEtale X}
    (e : finiteRepresentedSetSheaf Y ≅ finiteRepresentedSetSheaf Z) : Y.obj ≅ Z.obj :=
  LiftedRestrictedYoneda.sheafPreimageIso.{u + 1} (Scheme.Etale.forget X)
    (Scheme.smallEtaleTopology X) (Y := (toEtale X).obj Y) (Z := (toEtale X).obj Z)
    (finiteRepresentedSetSheaf Y).property (finiteRepresentedSetSheaf Z).property e

/-- Exact evaluation formula for the recovered Yoneda morphism. -/
theorem finiteRepresentedSetSheafPreimage_app {Y Z : Scheme.FiniteEtale X}
    (q : finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z)
    (U : X.Etale) (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    ULift.up (x ≫ finiteRepresentedSetSheafPreimage q) = q.hom.app (op U) (ULift.up x) :=
  LiftedRestrictedYoneda.preimage_app.{u + 1} (Scheme.Etale.forget X)
    (Y := (toEtale X).obj Y) (Z := (toEtale X).obj Z) q.hom (op U) x

namespace Torsor
variable (H : Grp (Over X)) [IsCommMonObj H.X]
variable (P : Torsor (representedSheaf H)) (Y : Scheme.FiniteEtale X)
variable (e : finiteRepresentedSetSheaf Y ≅ P.carrier)

/-- Represented sections identified with the actual torsor sections. -/
def representedSectionEquiv (U : X.Etale) :
    (((Scheme.Etale.forget X).obj U) ⟶ Y.obj) ≃ P.carrier.obj.obj (op U) :=
  CategoryTheory.Sheaf.Torsor.Represented.sectionEquiv.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e U

/-- Naturality of the actual representative's section identification. -/
theorem representedSectionEquiv_naturality {U V : X.Etale} (f : U ⟶ V)
    (x : (Scheme.Etale.forget X).obj V ⟶ Y.obj) :
    P.representedSectionEquiv H Y e U ((Scheme.Etale.forget X).map f ≫ x) =
      P.carrier.obj.map f.op (P.representedSectionEquiv H Y e V x) :=
  CategoryTheory.Sheaf.Torsor.Represented.sectionEquiv_naturality.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e f x

/-- The action on étale test objects, before its extension to all schemes. -/
def representedEtaleAction (U : X.Etale)
    (a : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    (Scheme.Etale.forget X).obj U ⟶ Y.obj :=
  CategoryTheory.Sheaf.Torsor.Represented.testAction.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e U a x

theorem representedEtaleAction_naturality {U V : X.Etale} (f : U ⟶ V)
    (a : (Scheme.Etale.forget X).obj V ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj V ⟶ Y.obj) :
    (Scheme.Etale.forget X).map f ≫ P.representedEtaleAction H Y e V a x =
      P.representedEtaleAction H Y e U ((Scheme.Etale.forget X).map f ≫ a)
        ((Scheme.Etale.forget X).map f ≫ x) :=
  CategoryTheory.Sheaf.Torsor.Represented.testAction_naturality.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e f a x

theorem representedEtaleAction_one (U : X.Etale)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    P.representedEtaleAction H Y e U 1 x = x :=
  CategoryTheory.Sheaf.Torsor.Represented.testAction_one.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e U x

theorem representedEtaleAction_mul (U : X.Etale)
    (a b : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    P.representedEtaleAction H Y e U (a * b) x =
      P.representedEtaleAction H Y e U a (P.representedEtaleAction H Y e U b x) :=
  CategoryTheory.Sheaf.Torsor.Represented.testAction_mul.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e U a b x

/-- Simply transitive transport on actual étale test objects. -/
theorem representedEtaleAction_transport (U : X.Etale)
    (x y : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    ∃! a, P.representedEtaleAction H Y e U a x = y :=
  CategoryTheory.Sheaf.Torsor.Represented.testAction_transport.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e U x y

variable [IsFinite H.X.hom] [Etale H.X.hom]

/-- The actual finite étale product on which the universal action is evaluated. -/
abbrev representedActionDomain : Scheme.FiniteEtale X :=
  Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H ⊗ Y

/-- The genuine scheme action morphism recovered on the universal étale test. -/
def representedActionMap : H.X ⊗ Y.obj ⟶ Y.obj :=
  CategoryTheory.Sheaf.Torsor.Represented.actionMap.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Torsor.representedActionDomain H Y))
    (CategoryTheory.Iso.refl _)

/-- The lower action map has exactly the original universal-test value. -/
theorem representedActionMap_eq_original : P.representedActionMap H Y e =
    P.representedEtaleAction H Y e ((toEtale X).obj (Torsor.representedActionDomain H Y))
      (fst H.X Y.obj) (snd H.X Y.obj) := by
  simp only [representedActionMap, CategoryTheory.Sheaf.Torsor.Represented.actionMap,
    CategoryTheory.RepresentableBinaryOperation.map, CategoryTheory.Iso.refl_hom,
    CategoryTheory.Iso.refl_inv, Category.id_comp, representedEtaleAction]
  exact Category.id_comp _

/-- Evaluation of the actual action morphism on an arbitrary scheme over X. -/
def representedAct {T : Over X} (a : T ⟶ H.X) (x : T ⟶ Y.obj) : T ⟶ Y.obj :=
  CategoryTheory.TorsorAction.actOfMap (P.representedActionMap H Y e) a x

theorem representedAct_naturality {T U : Over X} (f : T ⟶ U)
    (a : U ⟶ H.X) (x : U ⟶ Y.obj) :
    f ≫ P.representedAct H Y e a x = P.representedAct H Y e (f ≫ a) (f ≫ x) :=
  CategoryTheory.TorsorAction.actOfMap_naturality
    (P.representedActionMap H Y e) f a x

/-- The extended scheme action agrees with the original sheaf action on every
étale test scheme, by naturality on the universal product. -/
theorem representedAct_eq_etale (U : X.Etale)
    (a : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    P.representedAct H Y e a x = P.representedEtaleAction H Y e U a x :=
  CategoryTheory.Sheaf.Torsor.Represented.actionMap_value.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Torsor.representedActionDomain H Y))
    (CategoryTheory.Iso.refl _) U a x

theorem representedAct_one {T : Over X} (x : T ⟶ Y.obj) :
    P.representedAct H Y e 1 x = x :=
  CategoryTheory.TorsorAction.actOfMap_one (P.representedActionMap H Y e)
    (CategoryTheory.Sheaf.Torsor.Represented.action_one_diagram.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Torsor.representedActionDomain H Y))
    (CategoryTheory.Iso.refl _)
      ((toEtale X).obj Y) (CategoryTheory.Iso.refl _)) x

theorem representedAct_mul {T : Over X} (a b : T ⟶ H.X) (x : T ⟶ Y.obj) :
    P.representedAct H Y e (a * b) x =
      P.representedAct H Y e a (P.representedAct H Y e b x) :=
  CategoryTheory.TorsorAction.actOfMap_mul (P.representedActionMap H Y e)
    (CategoryTheory.Sheaf.Torsor.Represented.action_mul_diagram.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Torsor.representedActionDomain H Y))
    (CategoryTheory.Iso.refl _)
    ((toEtale X).obj ((Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H ⊗
      Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H) ⊗ Y))
      (CategoryTheory.Iso.refl _)) a b x

/-- The actual difference morphism is obtained from unique transport on Y×Y. -/
def representedDifferenceMap : Y.obj ⊗ Y.obj ⟶ H.X :=
  CategoryTheory.Sheaf.Torsor.Represented.differenceMap.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Y ⊗ Y)) (CategoryTheory.Iso.refl _)

omit [IsFinite H.X.hom] [Etale H.X.hom] in
/-- The lower difference keeps the original uniquely chosen universal transporter. -/
theorem representedDifferenceMap_eq_original : P.representedDifferenceMap H Y e =
    Classical.choose (P.representedEtaleAction_transport H Y e
      ((toEtale X).obj (Y ⊗ Y)) (fst Y.obj Y.obj) (snd Y.obj Y.obj)) := by
  simp only [representedDifferenceMap, CategoryTheory.Sheaf.Torsor.Represented.differenceMap,
    CategoryTheory.RepresentableBinaryOperation.map, CategoryTheory.Iso.refl_hom,
    CategoryTheory.Iso.refl_inv, Category.id_comp]
  rfl

/-- The morphism `T ⟶ H.X` obtained by applying the represented difference map to the pair
`(x, y)` . -/
def representedDifference {T : Over X} (x y : T ⟶ Y.obj) : T ⟶ H.X :=
  CategoryTheory.TorsorAction.differenceOfMap (P.representedDifferenceMap H Y e) x y

omit [IsFinite H.X.hom] [Etale H.X.hom] in
theorem representedDifference_naturality {T U : Over X} (f : T ⟶ U)
    (x y : U ⟶ Y.obj) :
    f ≫ P.representedDifference H Y e x y =
      P.representedDifference H Y e (f ≫ x) (f ≫ y) :=
  CategoryTheory.TorsorAction.differenceOfMap_naturality
    (P.representedDifferenceMap H Y e) f x y

/-- The difference morphism produces transport on all scheme test objects. -/
theorem representedAct_difference {T : Over X} (x y : T ⟶ Y.obj) :
    P.representedAct H Y e (P.representedDifference H Y e x y) x = y :=
  CategoryTheory.TorsorAction.actOfMap_difference (P.representedActionMap H Y e)
    (P.representedDifferenceMap H Y e)
    (CategoryTheory.Sheaf.Torsor.Represented.action_difference_diagram.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Torsor.representedActionDomain H Y))
      ((toEtale X).obj (Y ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)) x y

/-- Uniqueness too extends from the universal finite étale product to every
scheme test object; no geometric-point-only test is used. -/
theorem representedDifference_act {T : Over X} (a : T ⟶ H.X) (x : T ⟶ Y.obj) :
    P.representedDifference H Y e x (P.representedAct H Y e a x) = a :=
  CategoryTheory.TorsorAction.differenceOfMap_act (P.representedActionMap H Y e)
    (P.representedDifferenceMap H Y e)
    (CategoryTheory.Sheaf.Torsor.Represented.difference_action_diagram.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Torsor.representedActionDomain H Y))
      ((toEtale X).obj (Y ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)) a x

/-- The genuine sheaf action yields an actual scheme torsor action on all
scheme-valued points, suitable for `FiberTorsorActions.rho`. -/
def representedSchemeAction : TorsorAction H (toUnit Y.obj) :=
  CategoryTheory.Sheaf.Torsor.Represented.categoricalAction.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Torsor.representedActionDomain H Y))
      ((toEtale X).obj (Y ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
    ((toEtale X).obj Y)
      ((toEtale X).obj ((Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H ⊗
      Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H) ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)

/-- The A3 representative carries the transported actual scheme torsor action. -/
def finiteEtaleSchemeAction (h : Stacks03RV X)
    (hL : IsFiniteLocallyConstant (representedSheaf H)) :
    TorsorAction H (toUnit (P.finiteEtaleRepresentative h hL).obj) :=
  P.representedSchemeAction H (P.finiteEtaleRepresentative h hL)
    (P.finiteEtaleRepresentativeIso h hL)

/-- Exact evaluation of the represented scheme action on the original sheaf
sections. This is the action comparison, rather than an arbitrary bijection. -/
theorem representedSchemeAction_section (U : X.Etale)
    (a : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    e.hom.hom.app (op U) (ULift.up ((P.representedSchemeAction H Y e).act a x)) =
      P.action (op U) (ULift.up (Additive.ofMul a)) (e.hom.hom.app (op U) (ULift.up x)) :=
  CategoryTheory.Sheaf.Torsor.Represented.categoricalAction_section.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Torsor.representedActionDomain H Y))
      ((toEtale X).obj (Y ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
    ((toEtale X).obj Y)
      ((toEtale X).obj ((Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H ⊗
      Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H) ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _) U a x

omit [IsFinite H.X.hom] [Etale H.X.hom] in
include P e in
/-- Local nonemptiness forces the actual representing finite étale scheme to
be surjective, without a rational-point surjectivity assertion. -/
theorem represented_surjective : Surjective Y.obj.hom := by
  constructor
  intro x
  have h := P.locally_nonempty (etaleTerminal X)
  change _ ∈ X.smallGrothendieckTopology @Etale (etaleTerminal X) at h
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology] at h
  obtain ⟨V, f, v, ⟨t⟩, _, hv⟩ := h x
  let q := (e.inv.hom.app (op V) t).down
  refine ⟨q.left v, ?_⟩
  have hq := Over.w q
  have hf := MorphismProperty.Over.w f
  have hh : q.left ≫ Y.obj.hom = f.left := by simpa using hq.trans hf.symm
  change (q.left ≫ Y.obj.hom) v = x
  rw [hh]
  exact hv

variable (Q : Torsor (representedSheaf H)) (Z : Scheme.FiniteEtale X)
variable (d : P.Iso Q) (f : finiteRepresentedSetSheaf Z ≅ Q.carrier)

/-- A torsor isomorphism determines an actual scheme isomorphism of its
finite representatives, through the proved Yoneda transport. -/
def representedIso : Y.obj ≅ Z.obj :=
  finiteRepresentedSetSheafIso (e ≪≫ d.carrierIso ≪≫ f.symm)

omit [IsFinite H.X.hom] [Etale H.X.hom] in
theorem representedIso_section (U : X.Etale)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    f.hom.hom.app (op U) (ULift.up (x ≫ (P.representedIso H Y e Q Z d f).hom)) =
      d.carrierIso.hom.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x)) := by
  have h := finiteRepresentedSetSheafPreimage_app (e.hom ≫ d.carrierIso.hom ≫ f.inv) U x
  change ULift.up (x ≫ (P.representedIso H Y e Q Z d f).hom) =
    f.inv.hom.app (op U) (d.carrierIso.hom.hom.app (op U)
      (e.hom.hom.app (op U) (ULift.up x))) at h
  rw [h]
  exact congrArg (fun r : Q.carrier ⟶ Q.carrier => r.hom.app (op U)
    (d.carrierIso.hom.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x)))) f.inv_hom_id

/-- The representative isomorphism respects the action on every étale test. -/
theorem representedIso_equivariant_etale (U : X.Etale)
    (a : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    (P.representedSchemeAction H Y e).act a x ≫ (P.representedIso H Y e Q Z d f).hom =
      (Q.representedSchemeAction H Z f).act a (x ≫ (P.representedIso H Y e Q Z d f).hom) := by
  apply (Q.representedSectionEquiv H Z f U).injective
  change f.hom.hom.app (op U) (ULift.up _) = f.hom.hom.app (op U) (ULift.up _)
  rw [P.representedIso_section, P.representedSchemeAction_section,
    Q.representedSchemeAction_section, P.representedIso_section, d.equivariant]

/-- Equivariance holds on every scheme-valued point, in particular on the
actual geometric fibres consumed by finite-cover monodromy. -/
theorem representedIso_equivariant {T : Over X} (a : T ⟶ H.X) (x : T ⟶ Y.obj) :
    (P.representedSchemeAction H Y e).act a x ≫ (P.representedIso H Y e Q Z d f).hom =
      (Q.representedSchemeAction H Z f).act a (x ≫ (P.representedIso H Y e Q Z d f).hom) := by
  have h := P.representedIso_equivariant_etale H Y e Q Z d f
    ((toEtale X).obj (Torsor.representedActionDomain H Y)) (fst H.X Y.obj) (snd H.X Y.obj)
  have hh := congrArg (fun q => lift a x ≫ q) h
  simpa only [← Category.assoc, TorsorAction.naturality, lift_fst, lift_snd,
    lift_snd_assoc] using hh

end Torsor
/-- A surjective finite étale representative is locally inhabited on the
actual small étale site, by its actual pullback cover. -/
theorem finiteRepresentedSetSheaf_locally_nonempty (Y : Scheme.FiniteEtale X)
    [Surjective Y.obj.hom] (U : X.Etale) :
    nonemptySieve (finiteRepresentedSetSheaf Y) U ∈ Scheme.smallEtaleTopology X U := by
  change _ ∈ X.smallGrothendieckTopology @Etale U
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology]
  intro x
  let V : X.Etale := Scheme.Etale.mk (pullback.snd Y.obj.hom U.hom ≫ U.hom)
  let f : V ⟶ U := MorphismProperty.Over.homMk (pullback.snd Y.obj.hom U.hom) rfl (by trivial)
  obtain ⟨y, hy⟩ := (surjective_iff (pullback.snd Y.obj.hom U.hom)).mp inferInstance x
  refine ⟨V, f, y, ?_, inferInstanceAs (Etale (pullback.snd Y.obj.hom U.hom)), hy⟩
  exact ⟨ULift.up (Over.homMk (pullback.fst Y.obj.hom U.hom) pullback.condition)⟩

/-- Every actual surjective finite étale scheme torsor defines a genuine sheaf
torsor for the represented coefficient sheaf. -/
def torsorOfSchemeAction (H : Grp (Over X)) [IsCommMonObj H.X] (Y : Scheme.FiniteEtale X)
    [Surjective Y.obj.hom] (τ : TorsorAction H (toUnit Y.obj)) :
    Torsor (representedSheaf H) :=
  CategoryTheory.Sheaf.Torsor.Represented.ofCategoricalAction.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    Y.obj τ (finiteRepresentedSetSheaf_locally_nonempty Y)

/-- Recovering the sheaf torsor after extending its action to all schemes
returns the original torsor by its given representative isomorphism. -/
def Torsor.representedSchemeActionIso (H : Grp (Over X)) [IsCommMonObj H.X]
    [IsFinite H.X.hom] [Etale H.X.hom] (P : Torsor (representedSheaf H))
    (Y : Scheme.FiniteEtale X) [Surjective Y.obj.hom]
      (e : finiteRepresentedSetSheaf Y ≅ P.carrier) :
    Torsor.Iso (torsorOfSchemeAction H Y (P.representedSchemeAction H Y e)) P :=
  CategoryTheory.Sheaf.Torsor.Represented.sheafRoundtrip.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    P Y.obj e ((toEtale X).obj (Torsor.representedActionDomain H Y))
      ((toEtale X).obj (Y ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
    ((toEtale X).obj Y)
      ((toEtale X).obj ((Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H ⊗
      Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H) ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
    (finiteRepresentedSetSheaf_locally_nonempty Y)

/-- Starting from an actual scheme torsor recovers the same action on every
scheme-valued point, not just geometric or small-site points. -/
theorem torsorOfSchemeAction_representedSchemeAction (H : Grp (Over X)) [IsCommMonObj H.X]
    [IsFinite H.X.hom] [Etale H.X.hom] (Y : Scheme.FiniteEtale X) [Surjective Y.obj.hom]
    (τ : TorsorAction H (toUnit Y.obj)) :
    (torsorOfSchemeAction H Y τ).representedSchemeAction H Y (CategoryTheory.Iso.refl _) = τ := by
  exact CategoryTheory.Sheaf.Torsor.Represented.categoricalRoundtrip.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    Y.obj ((toEtale X).obj (Torsor.representedActionDomain H Y))
      ((toEtale X).obj (Y ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
    ((toEtale X).obj Y)
      ((toEtale X).obj ((Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H ⊗
      Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H) ⊗ Y))
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
    τ (finiteRepresentedSetSheaf_locally_nonempty Y)

/-- A genuine equivariant scheme isomorphism gives the corresponding sheaf
torsor isomorphism, with its actual Yoneda map as carrier map. -/
def torsorOfSchemeActionIso (H : Grp (Over X)) [IsCommMonObj H.X]
    (Y Z : Scheme.FiniteEtale X) [Surjective Y.obj.hom] [Surjective Z.obj.hom]
    (τ : TorsorAction H (toUnit Y.obj)) (σ : TorsorAction H (toUnit Z.obj))
    (q : Y.obj ≅ Z.obj)
    (hq : ∀ {T : Over X} (a : T ⟶ H.X) (x : T ⟶ Y.obj),
      τ.act a x ≫ q.hom = σ.act a (x ≫ q.hom)) :
    Torsor.Iso (torsorOfSchemeAction H Y τ) (torsorOfSchemeAction H Z σ) :=
  CategoryTheory.Sheaf.Torsor.Represented.ofCategoricalIso.{u + 1}
    (F := Scheme.Etale.forget X) (J := Scheme.smallEtaleTopology X) (H := H)
    (hH := (representedSheaf H).property)
    (hY := (finiteRepresentedSetSheaf Y).property)
    (hZ := (finiteRepresentedSetSheaf Z).property)
    Y.obj Z.obj τ σ (finiteRepresentedSetSheaf_locally_nonempty Y)
    (finiteRepresentedSetSheaf_locally_nonempty Z) q hq

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 13490df8d3617a248ab764a93311a38812036cca18d4ed7fb16852488dddffa0.
Definitions, hypotheses and universes are retained modulo native names. -/
