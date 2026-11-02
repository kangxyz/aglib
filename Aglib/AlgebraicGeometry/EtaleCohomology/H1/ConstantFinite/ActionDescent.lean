/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ProperHenselian.Sections
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverEpimorphisms
public import Aglib.CategoryTheory.Sites.Torsor.Transport
public import Aglib.CategoryTheory.Sites.Descent.Represented.TorsorAction

/-! # Descent of actual finite torsor actions through finite-cover restriction -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.ActionDescent

universe u

attribute [local instance] Over.cartesianMonoidalCategory
  Scheme.FiniteEtale.GroupDescent.coverCartesian

section Difference

variable {B : Scheme.{u}} {G : Grp (Over B)} {Y : Over B}
  (τ : TorsorAction G (toUnit Y))

/-- The original unique transporter, in the positive action convention. -/
abbrev difference {T : Over B} (x y : T ⟶ Y) : T ⟶ G.X :=
  τ.positiveTransport x y

/-- The original positive transporter sends its source to its target. -/
theorem act_difference {T : Over B} (x y : T ⟶ Y) :
    τ.act (difference τ x y) x = y :=
  τ.act_positiveTransport x y

/-- Unique transport recovers the original translating coefficient point. -/
theorem difference_act {T : Over B} (a : T ⟶ G.X) (x : T ⟶ Y) :
    difference τ x (τ.act a x) = a :=
  τ.positiveTransport_act a x

/-- Positive transport commutes with every change of scheme-valued test object. -/
theorem difference_naturality {T U : Over B} (g : T ⟶ U) (x y : U ⟶ Y) :
    g ≫ difference τ x y = difference τ (g ≫ x) (g ≫ y) :=
  τ.positiveTransport_naturality g x y

/-- The difference map on the actual product of two torsor carriers. -/
abbrev differenceMap : Y ⊗ Y ⟶ G.X := τ.positiveDifferenceMap

/-- Evaluation of the actual difference map is the original unique transporter. -/
theorem comp_differenceMap {T : Over B} (x y : T ⟶ Y) :
    lift x y ≫ differenceMap τ = difference τ x y :=
  τ.comp_positiveDifferenceMap x y

/-- Conjugation by the original carrier isomorphism preserves the actual coefficient action. -/
abbrev transportCarrier {Z : Over B} (e : Z ≅ Y) : TorsorAction G (toUnit Z) :=
  CategoryTheory.TorsorAction.transportCarrier τ e

end Difference

variable {X S : Scheme.{u}} (f : S ⟶ X)
  [(Scheme.FiniteEtale.baseChange f).Full]
  [(Scheme.FiniteEtale.baseChange f).Faithful]
  (G : Grp (Over X)) [IsFinite G.X.hom] [Etale G.X.hom]
  (Y : Scheme.FiniteEtale X)
  (τ : TorsorAction (baseChangedGroup f G)
    (toUnit ((Scheme.FiniteEtale.baseChange f).obj Y).obj))

/-- The actual full preimage through the finite-cover restriction square. -/
def liftedArrow (U V : Scheme.FiniteEtale X)
    (q : ((Scheme.FiniteEtale.baseChange f).obj U).obj ⟶
      ((Scheme.FiniteEtale.baseChange f).obj V).obj) :
    {r : U.obj ⟶ V.obj // (Over.pullback f).map r = q} :=
  ⟨CategoryTheory.TorsorAction.Descent.liftedArrow
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    U V q,
    CategoryTheory.TorsorAction.Descent.map_liftedArrow
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    U V q⟩

/-- The original action morphism lifted with the actual product comparison. -/
def actionMap : G.X ⊗ Y.obj ⟶ Y.obj :=
  CategoryTheory.TorsorAction.Descent.actionMap
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (Iso.refl _)

/-- The original positive difference lifted with its actual product comparison. -/
def descendedDifferenceMap : Y.obj ⊗ Y.obj ⟶ G.X :=
  CategoryTheory.TorsorAction.Descent.differenceMap
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom) (Iso.refl _)
    (Y ⊗ Y) (Iso.refl _)

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- The descended action retains its literal mapped action and product comparison. -/
theorem map_actionMap :
    (Over.pullback f).map (actionMap f G Y τ) =
      CartesianMonoidalCategory.prodComparison (Over.pullback f) G.X Y.obj ≫ τ.actionMap :=
  CategoryTheory.TorsorAction.Descent.map_actionMap
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (Iso.refl _)

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- The descended difference retains its literal positive transporter. -/
theorem map_descendedDifferenceMap :
    (Over.pullback f).map (descendedDifferenceMap f G Y τ) =
      CartesianMonoidalCategory.prodComparison (Over.pullback f) Y.obj Y.obj ≫ differenceMap τ :=
  CategoryTheory.TorsorAction.Descent.map_differenceMap
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom) (Iso.refl _)
    (Y ⊗ Y) (Iso.refl _)

/-- The square-based lift equals the original actual finite-cover preimage. -/
theorem liftedArrow_eq_original (U V : Scheme.FiniteEtale X)
    (q : ((Scheme.FiniteEtale.baseChange f).obj U).obj ⟶
      ((Scheme.FiniteEtale.baseChange f).obj V).obj) :
    (liftedArrow f U V q).val =
      ((Scheme.FiniteEtale.baseChange f).preimage (ObjectProperty.homMk q)).hom := by
  apply CategoryTheory.TorsorAction.Descent.map_injective
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm (U := U) (V := V)
  refine (liftedArrow f U V q).property.trans ?_
  exact (congrArg (fun k : (Scheme.FiniteEtale.baseChange f).obj U ⟶
    (Scheme.FiniteEtale.baseChange f).obj V => k.hom)
    ((Scheme.FiniteEtale.baseChange f).map_preimage (ObjectProperty.homMk q))).symm

/-- The whole lower action has the original chosen lift and its exact product comparison. -/
theorem actionMap_eq_original : actionMap f G Y τ =
    (liftedArrow f (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) Y
      (CartesianMonoidalCategory.prodComparison (Over.pullback f) G.X Y.obj ≫
        τ.actionMap)).val := by
  apply CategoryTheory.TorsorAction.Descent.map_injective
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    (U := Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (V := Y)
  exact (map_actionMap f G Y τ).trans
    (liftedArrow f (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) Y
      (CartesianMonoidalCategory.prodComparison (Over.pullback f) G.X Y.obj ≫
        τ.actionMap)).property.symm

/-- The whole lower difference has the original chosen positive-difference lift. -/
theorem descendedDifferenceMap_eq_original : descendedDifferenceMap f G Y τ =
    (liftedArrow f (Y ⊗ Y) (Scheme.FiniteEtale.mk G.X.hom)
      (CartesianMonoidalCategory.prodComparison (Over.pullback f) Y.obj Y.obj ≫
        differenceMap τ)).val := by
  apply CategoryTheory.TorsorAction.Descent.map_injective
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    (U := Y ⊗ Y) (V := Scheme.FiniteEtale.mk G.X.hom)
  exact (map_descendedDifferenceMap f G Y τ).trans
    (liftedArrow f (Y ⊗ Y) (Scheme.FiniteEtale.mk G.X.hom)
      (CartesianMonoidalCategory.prodComparison (Over.pullback f) Y.obj Y.obj ≫
        differenceMap τ)).property.symm

/-- The descended action on the original generalized points. -/
def act {T : Over X} (a : T ⟶ G.X) (x : T ⟶ Y.obj) : T ⟶ Y.obj :=
  CategoryTheory.TorsorAction.actOfMap (actionMap f G Y τ) a x

/-- The descended positive difference on the original generalized points. -/
def descendedDifference {T : Over X} (x y : T ⟶ Y.obj) : T ⟶ G.X :=
  CategoryTheory.TorsorAction.differenceOfMap (descendedDifferenceMap f G Y τ) x y

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- Naturality on every original scheme-valued test object. -/
theorem act_naturality {T U : Over X} (g : T ⟶ U) (a : U ⟶ G.X) (x : U ⟶ Y.obj) :
    g ≫ act f G Y τ a x = act f G Y τ (g ≫ a) (g ≫ x) :=
  CategoryTheory.TorsorAction.actOfMap_naturality (actionMap f G Y τ) g a x

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- Naturality of the original positive difference on every test. -/
theorem descendedDifference_naturality {T U : Over X} (g : T ⟶ U) (x y : U ⟶ Y.obj) :
    g ≫ descendedDifference f G Y τ x y =
      descendedDifference f G Y τ (g ≫ x) (g ≫ y) :=
  CategoryTheory.TorsorAction.differenceOfMap_naturality
    (descendedDifferenceMap f G Y τ) g x y

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- Pullback preserves the complete original action value on every test. -/
theorem map_act {T : Over X} (a : T ⟶ G.X) (x : T ⟶ Y.obj) :
    (Over.pullback f).map (act f G Y τ a x) =
      τ.act ((Over.pullback f).map a) ((Over.pullback f).map x) :=
  CategoryTheory.TorsorAction.Descent.map_act
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (Iso.refl _) a x

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- Pullback preserves the original positive transport value on every test. -/
theorem map_descendedDifference {T : Over X} (x y : T ⟶ Y.obj) :
    (Over.pullback f).map (descendedDifference f G Y τ x y) =
      difference τ ((Over.pullback f).map x) ((Over.pullback f).map y) :=
  CategoryTheory.TorsorAction.Descent.map_difference
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom) (Iso.refl _)
    (Y ⊗ Y) (Iso.refl _) x y

/-- The reflected finite unit diagram proves the unit law on all tests. -/
theorem act_one {T : Over X} (x : T ⟶ Y.obj) : act f G Y τ 1 x = x :=
  CategoryTheory.TorsorAction.actOfMap_one (actionMap f G Y τ)
    (CategoryTheory.TorsorAction.Descent.finite_one
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (Iso.refl _)
    Y (𝟙 Y.obj)) x

/-- The reflected finite product diagram proves associativity on all tests. -/
theorem act_mul {T : Over X} (a b : T ⟶ G.X) (x : T ⟶ Y.obj) :
    act f G Y τ (a * b) x = act f G Y τ a (act f G Y τ b x) :=
  CategoryTheory.TorsorAction.actOfMap_mul (actionMap f G Y τ)
    (CategoryTheory.TorsorAction.Descent.action_mul_diagram
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (Iso.refl _)
    ((Scheme.FiniteEtale.mk G.X.hom ⊗ Scheme.FiniteEtale.mk G.X.hom) ⊗ Y) (Iso.refl _)) a b x

/-- The reflected finite diagram retains positive transport on all tests. -/
theorem descended_act_difference {T : Over X} (x y : T ⟶ Y.obj) :
    act f G Y τ (descendedDifference f G Y τ x y) x = y :=
  CategoryTheory.TorsorAction.actOfMap_difference (actionMap f G Y τ)
    (descendedDifferenceMap f G Y τ)
    (CategoryTheory.TorsorAction.Descent.action_difference_diagram
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom) (Iso.refl _)
    (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (Y ⊗ Y) (Iso.refl _) (Iso.refl _)) x y

/-- The reflected finite diagram recovers every original coefficient point. -/
theorem descended_difference_act {T : Over X} (a : T ⟶ G.X) (x : T ⟶ Y.obj) :
    descendedDifference f G Y τ x (act f G Y τ a x) = a :=
  CategoryTheory.TorsorAction.differenceOfMap_act (actionMap f G Y τ)
    (descendedDifferenceMap f G Y τ)
    (CategoryTheory.TorsorAction.Descent.difference_action_diagram
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom) (Iso.refl _)
    (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (Y ⊗ Y) (Iso.refl _) (Iso.refl _)) a x

/-- Whole action descent through the original full faithful finite-cover square. -/
def descendedAction : TorsorAction G (toUnit Y.obj) :=
  CategoryTheory.TorsorAction.Descent.action
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom) (Iso.refl _)
    (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (Y ⊗ Y) (Iso.refl _) (Iso.refl _)
    ((Scheme.FiniteEtale.mk G.X.hom ⊗ Scheme.FiniteEtale.mk G.X.hom) ⊗ Y) (Iso.refl _)

/-- The actual Over adjunction recovers the original action on every test. -/
theorem pullback_descendedAction :
    SchemeTorsorBaseChange.pullbackSchemeAction f G Y (descendedAction f G Y τ) = τ :=
  CategoryTheory.TorsorAction.Descent.pullback_action
    (Scheme.FiniteEtale.forget X) (Scheme.FiniteEtale.forget S)
    (Scheme.FiniteEtale.baseChange f) (Over.pullback f)
    (Scheme.FiniteEtale.baseChangeForgetIso f).symm
    G Y τ (Scheme.FiniteEtale.mk G.X.hom) (Iso.refl _)
    (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) (Y ⊗ Y) (Iso.refl _) (Iso.refl _)
    ((Scheme.FiniteEtale.mk G.X.hom ⊗ Scheme.FiniteEtale.mk G.X.hom) ⊗ Y) (Iso.refl _)
    (Over.mapPullbackAdj f)

omit [(Scheme.FiniteEtale.baseChange f).Full] in
/-- Faithful finite-cover restriction reflects carrier surjectivity via its original
structural arrow, the canonical terminal comparison, and categorical epimorphisms. -/
theorem surjective_of_baseChange
    [Surjective ((Scheme.FiniteEtale.baseChange f).obj Y).obj.hom] : Surjective Y.obj.hom := by
  let F := Scheme.FiniteEtale.baseChange f
  let q : Y ⟶ Scheme.FiniteEtale.terminalCover X :=
    ObjectProperty.homMk (Over.homMk Y.obj.hom (Category.comp_id _))
  let q₀ : F.obj Y ⟶ Scheme.FiniteEtale.terminalCover S :=
    ObjectProperty.homMk (Over.homMk (F.obj Y).obj.hom (Category.comp_id _))
  have hq₀ : Epi q₀ := by
    apply (Scheme.FiniteEtale.forgetToScheme S).epi_of_epi_map
    change Epi (F.obj Y).obj.hom
    exact Flat.epi_of_flat_of_surjective _
  have heq : F.map q = q₀ ≫ (ProperHenselianH0.terminalIso f).inv := by
    apply (cancel_mono (ProperHenselianH0.terminalIso f).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (Scheme.FiniteEtale.terminalCoverIsTerminal S).hom_ext _ _
  have : Epi (F.map q) := by rw [heq]; infer_instance
  have : Epi q := F.epi_of_epi_map inferInstance
  exact Scheme.FiniteEtale.coverHom_surjective_of_epi q

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.ActionDescent
