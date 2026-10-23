/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ProperHenselian.Sections
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverEpimorphisms

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
def difference {T : Over B} (x y : T ⟶ Y) : T ⟶ G.X :=
  Classical.choose (τ.transport x y (toUnit_unique _ _))

/-- The original positive transporter sends its source to its target. -/
theorem act_difference {T : Over B} (x y : T ⟶ Y) :
    τ.act (difference τ x y) x = y :=
  (Classical.choose_spec (τ.transport x y (toUnit_unique _ _))).1

/-- Unique transport recovers the original translating coefficient point. -/
theorem difference_act {T : Over B} (a : T ⟶ G.X) (x : T ⟶ Y) :
    difference τ x (τ.act a x) = a :=
  ((Classical.choose_spec (τ.transport x (τ.act a x) (toUnit_unique _ _))).2 a rfl).symm

/-- Positive transport commutes with every change of scheme-valued test object. -/
theorem difference_naturality {T U : Over B} (g : T ⟶ U) (x y : U ⟶ Y) :
    g ≫ difference τ x y = difference τ (g ≫ x) (g ≫ y) := by
  apply (Classical.choose_spec
    (τ.transport (g ≫ x) (g ≫ y) (toUnit_unique _ _))).2
  rw [← τ.naturality, act_difference]

/-- The difference map on the actual product of two torsor carriers. -/
def differenceMap : Y ⊗ Y ⟶ G.X := difference τ (fst Y Y) (snd Y Y)

/-- Evaluation of the actual difference map is the original unique transporter. -/
theorem comp_differenceMap {T : Over B} (x y : T ⟶ Y) :
    lift x y ≫ differenceMap τ = difference τ x y := by
  rw [differenceMap, difference_naturality, lift_fst, lift_snd]

/-- Conjugation by the original carrier isomorphism preserves the actual coefficient action. -/
def transportCarrier {Z : Over B} (e : Z ≅ Y) : TorsorAction G (toUnit Z) where
  act a x := τ.act a (x ≫ e.hom) ≫ e.inv
  naturality g a x := by
    rw [← Category.assoc, τ.naturality, Category.assoc]
  one_act x := by simp only [τ.one_act, Category.assoc, e.hom_inv_id, Category.comp_id]
  mul_act a b x := by simp only [τ.mul_act, Category.assoc, e.inv_hom_id, Category.comp_id]
  over _ _ := toUnit_unique _ _
  transport x y _ := by
    obtain ⟨a, ha, hu⟩ := τ.transport (x ≫ e.hom) (y ≫ e.hom) (toUnit_unique _ _)
    refine ⟨a, ?_, ?_⟩
    · simp only [ha, Category.assoc, e.hom_inv_id, Category.comp_id]
    · intro b hb
      apply hu
      have h := congrArg (fun k => k ≫ e.hom) hb
      simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using h

end Difference

variable {X S : Scheme.{u}} (f : S ⟶ X)
  [(Scheme.FiniteEtale.baseChange f).Full]
  [(Scheme.FiniteEtale.baseChange f).Faithful]
  (G : Grp (Over X)) [IsFinite G.X.hom] [Etale G.X.hom]
  (Y : Scheme.FiniteEtale X)
  (τ : TorsorAction (baseChangedGroup f G)
    (toUnit ((Scheme.FiniteEtale.baseChange f).obj Y).obj))

omit [(Scheme.FiniteEtale.baseChange f).Full] in
private theorem pullback_map_injective {T Z : Scheme.FiniteEtale X}
    {a b : T.obj ⟶ Z.obj} (h : (Over.pullback f).map a = (Over.pullback f).map b) : a = b := by
  have h' : (Scheme.FiniteEtale.baseChange f).map (ObjectProperty.homMk a) =
      (Scheme.FiniteEtale.baseChange f).map (ObjectProperty.homMk b) :=
    ObjectProperty.hom_ext _ h
  exact congrArg (fun k => k.hom) ((Scheme.FiniteEtale.baseChange f).map_injective h')

/-- The native full preimage, paired with its literal original pullback equation. -/
def liftedArrow (U V : Scheme.FiniteEtale X)
    (q : ((Scheme.FiniteEtale.baseChange f).obj U).obj ⟶
      ((Scheme.FiniteEtale.baseChange f).obj V).obj) :
    {r : U.obj ⟶ V.obj // (Over.pullback f).map r = q} := by
  refine ⟨((Scheme.FiniteEtale.baseChange f).preimage (ObjectProperty.homMk q)).hom, ?_⟩
  exact congrArg (fun k : (Scheme.FiniteEtale.baseChange f).obj U ⟶
    (Scheme.FiniteEtale.baseChange f).obj V => k.hom)
      ((Scheme.FiniteEtale.baseChange f).map_preimage (ObjectProperty.homMk q))

/-- Fullness lifts the actual action map through the canonical product comparison. -/
def actionMap : G.X ⊗ Y.obj ⟶ Y.obj :=
  (liftedArrow f (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) Y
    (CartesianMonoidalCategory.prodComparison (Over.pullback f) G.X Y.obj ≫ τ.actionMap)).val

/-- Fullness separately lifts the actual positive difference map. -/
def descendedDifferenceMap : Y.obj ⊗ Y.obj ⟶ G.X :=
  (liftedArrow f (Y ⊗ Y) (Scheme.FiniteEtale.mk G.X.hom)
    (CartesianMonoidalCategory.prodComparison (Over.pullback f) Y.obj Y.obj ≫
      differenceMap τ)).val

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- The descended action map pulls back to the original action with its product comparison. -/
theorem map_actionMap :
    (Over.pullback f).map (actionMap f G Y τ) =
      CartesianMonoidalCategory.prodComparison (Over.pullback f) G.X Y.obj ≫ τ.actionMap :=
  (liftedArrow f (Scheme.FiniteEtale.mk G.X.hom ⊗ Y) Y
    (CartesianMonoidalCategory.prodComparison (Over.pullback f) G.X Y.obj ≫ τ.actionMap)).property

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- The descended difference retains the original product comparison and positive transporter. -/
theorem map_descendedDifferenceMap :
    (Over.pullback f).map (descendedDifferenceMap f G Y τ) =
      CartesianMonoidalCategory.prodComparison (Over.pullback f) Y.obj Y.obj ≫ differenceMap τ :=
  (liftedArrow f (Y ⊗ Y) (Scheme.FiniteEtale.mk G.X.hom)
    (CartesianMonoidalCategory.prodComparison (Over.pullback f) Y.obj Y.obj ≫
      differenceMap τ)).property

/-- The descended action on all original scheme-valued points. -/
def act {T : Over X} (a : T ⟶ G.X) (x : T ⟶ Y.obj) : T ⟶ Y.obj :=
  lift a x ≫ actionMap f G Y τ

/-- The descended difference on all original scheme-valued points. -/
def descendedDifference {T : Over X} (x y : T ⟶ Y.obj) : T ⟶ G.X :=
  lift x y ≫ descendedDifferenceMap f G Y τ

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- The descended action is natural on all scheme-valued test objects. -/
theorem act_naturality {T U : Over X} (g : T ⟶ U) (a : U ⟶ G.X) (x : U ⟶ Y.obj) :
    g ≫ act f G Y τ a x = act f G Y τ (g ≫ a) (g ≫ x) := by
  simp only [act, ← comp_lift, Category.assoc]

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- The descended positive difference is natural on all scheme-valued test objects. -/
theorem descendedDifference_naturality {T U : Over X} (g : T ⟶ U) (x y : U ⟶ Y.obj) :
    g ≫ descendedDifference f G Y τ x y =
      descendedDifference f G Y τ (g ≫ x) (g ≫ y) := by
  simp only [descendedDifference, ← comp_lift, Category.assoc]

omit [(Scheme.FiniteEtale.baseChange f).Full]
  [(Scheme.FiniteEtale.baseChange f).Faithful] in
private theorem map_lift_comparison {T U V : Over X} (a : T ⟶ U) (b : T ⟶ V) :
    (Over.pullback f).map (lift a b) ≫
      CartesianMonoidalCategory.prodComparison (Over.pullback f) U V =
      lift ((Over.pullback f).map a) ((Over.pullback f).map b) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- Pullback of the descended action retains the original action on every test object. -/
theorem map_act {T : Over X} (a : T ⟶ G.X) (x : T ⟶ Y.obj) :
    (Over.pullback f).map (act f G Y τ a x) =
      τ.act ((Over.pullback f).map a) ((Over.pullback f).map x) := by
  rw [act, Functor.map_comp, map_actionMap, ← Category.assoc,
    map_lift_comparison, τ.comp_actionMap]

omit [(Scheme.FiniteEtale.baseChange f).Faithful] in
/-- Pullback of the descended difference retains the original positive transporter. -/
theorem map_descendedDifference {T : Over X} (x y : T ⟶ Y.obj) :
    (Over.pullback f).map (descendedDifference f G Y τ x y) =
      difference τ ((Over.pullback f).map x) ((Over.pullback f).map y) := by
  rw [descendedDifference, Functor.map_comp, map_descendedDifferenceMap,
    ← Category.assoc, map_lift_comparison, comp_differenceMap]

private theorem act_one_finite (T : Scheme.FiniteEtale X) (x : T.obj ⟶ Y.obj) :
    act f G Y τ 1 x = x := by
  apply pullback_map_injective f (T := T) (Z := Y)
  rw [map_act, (Over.pullback f).map_one, τ.one_act]

private theorem act_mul_finite (T : Scheme.FiniteEtale X)
    (a b : T.obj ⟶ G.X) (x : T.obj ⟶ Y.obj) :
    act f G Y τ (a * b) x = act f G Y τ a (act f G Y τ b x) := by
  apply pullback_map_injective f (T := T) (Z := Y)
  rw [map_act, map_act, map_act, (Over.pullback f).map_mul, τ.mul_act]

private theorem act_difference_finite (T : Scheme.FiniteEtale X) (x y : T.obj ⟶ Y.obj) :
    act f G Y τ (descendedDifference f G Y τ x y) x = y := by
  apply pullback_map_injective f (T := T) (Z := Y)
  rw [map_act, map_descendedDifference, act_difference]

private theorem difference_act_finite (T : Scheme.FiniteEtale X)
    (a : T.obj ⟶ G.X) (x : T.obj ⟶ Y.obj) :
    descendedDifference f G Y τ x (act f G Y τ a x) = a := by
  apply pullback_map_injective f (T := T) (Z := Scheme.FiniteEtale.mk G.X.hom)
  rw [map_descendedDifference, map_act, difference_act]

/-- The descended action has the unit law on every scheme-valued test object. -/
theorem act_one {T : Over X} (x : T ⟶ Y.obj) : act f G Y τ 1 x = x := by
  have h := congrArg (fun k => x ≫ k) (act_one_finite f G Y τ Y (𝟙 Y.obj))
  simpa only [act_naturality, MonObj.comp_one, Category.comp_id] using h

/-- Finite-product faithfulness proves associativity on every scheme-valued test object. -/
theorem act_mul {T : Over X} (a b : T ⟶ G.X) (x : T ⟶ Y.obj) :
    act f G Y τ (a * b) x = act f G Y τ a (act f G Y τ b x) := by
  let D : Scheme.FiniteEtale X :=
    (Scheme.FiniteEtale.mk G.X.hom ⊗ Scheme.FiniteEtale.mk G.X.hom) ⊗ Y
  have h := congrArg (fun k => lift (lift a b) x ≫ k)
    (act_mul_finite f G Y τ D
      (fst (G.X ⊗ G.X) Y.obj ≫ fst G.X G.X)
      (fst (G.X ⊗ G.X) Y.obj ≫ snd G.X G.X) (snd (G.X ⊗ G.X) Y.obj))
  rw [act_naturality, act_naturality, act_naturality, MonObj.comp_mul] at h
  simpa using h

/-- The descended difference acts by the original positive transport convention. -/
theorem descended_act_difference {T : Over X} (x y : T ⟶ Y.obj) :
    act f G Y τ (descendedDifference f G Y τ x y) x = y := by
  have h := congrArg (fun k => lift x y ≫ k)
    (act_difference_finite f G Y τ (Y ⊗ Y) (fst Y.obj Y.obj) (snd Y.obj Y.obj))
  rw [act_naturality, descendedDifference_naturality] at h
  simpa using h

/-- The descended positive difference recovers every original coefficient point. -/
theorem descended_difference_act {T : Over X} (a : T ⟶ G.X) (x : T ⟶ Y.obj) :
    descendedDifference f G Y τ x (act f G Y τ a x) = a := by
  have h := congrArg (fun k => lift a x ≫ k)
    (difference_act_finite f G Y τ (Scheme.FiniteEtale.mk G.X.hom ⊗ Y)
      (fst G.X Y.obj) (snd G.X Y.obj))
  rw [descendedDifference_naturality, act_naturality] at h
  simpa using h

/-- Fullness and faithfulness descend the complete actual scheme torsor action.
Surjectivity of the carrier remains a separate geometric property. -/
def descendedAction : TorsorAction G (toUnit Y.obj) where
  act := act f G Y τ
  naturality := act_naturality f G Y τ
  one_act := act_one f G Y τ
  mul_act := act_mul f G Y τ
  over _ _ := toUnit_unique _ _
  transport x y _ := ⟨descendedDifference f G Y τ x y,
    descended_act_difference f G Y τ x y, fun a ha => by
      rw [← ha]
      exact (descended_difference_act f G Y τ a x).symm⟩

/-- Pulling back the descended action gives exactly the original action on every test scheme. -/
theorem pullback_descendedAction :
    SchemeTorsorBaseChange.pullbackSchemeAction f G Y (descendedAction f G Y τ) = τ := by
  apply TorsorAction.ext
  intro T a x
  change (Over.mapPullbackAdj f).unit.app T ≫ (Over.pullback f).map
      (act f G Y τ ((SchemeTorsorBaseChange.pullbackSectionMulEquiv f T G).symm a)
        ((SchemeTorsorBaseChange.pullbackSectionEquiv f T Y.obj).symm x)) = τ.act a x
  rw [map_act, τ.naturality]
  change τ.act
      (SchemeTorsorBaseChange.pullbackSectionMulEquiv f T G
        ((SchemeTorsorBaseChange.pullbackSectionMulEquiv f T G).symm a))
      (SchemeTorsorBaseChange.pullbackSectionEquiv f T Y.obj
        ((SchemeTorsorBaseChange.pullbackSectionEquiv f T Y.obj).symm x)) = τ.act a x
  rw [MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

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
