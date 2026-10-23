/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The original module unit and the constant-integer comparison

On a site with a specified terminal object, maps from the native rank-one
module and maps from the native constant integer sheaf represent the same
sections. The comparison is the actual scalar-forgetting map precomposed by
section one. In addition to the native aligned unit, a genuine lifted rank-one
module handles larger module values over the unchanged smaller scalar sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r w s

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})

set_option backward.isDefEq.respectTransparency false in
/-- Actual compatible module sections are determined by the terminal component. -/
def sectionsTerminalEquiv (M : SheafOfModules.{w} R) :
    M.sections ≃ M.val.obj (op T) where
  toFun s := s.val (op T)
  invFun m :=
    { val := fun X ↦ M.val.map (hT.from X.unop).op m
      property := fun {X Y} f ↦ by
        change M.val.map f (M.val.map (hT.from X.unop).op m) =
          M.val.map (hT.from Y.unop).op m
        rw [← M.val.map_comp_apply]
        apply M.val.congr_map_apply
        exact congrArg Quiver.Hom.op (hT.hom_ext _ _) }
  left_inv s := by
    apply Subtype.ext
    funext X
    exact s.property (hT.from X.unop).op
  right_inv m := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    change (M.val.presheaf ⋙ forget _).map (hT.from T).op m = m
    rw [h]
    simp

/-- The native module unit represents evaluation at the chosen terminal object. -/
def unitHomTerminalEquiv (M : SheafOfModules.{r} R) :
    (SheafOfModules.unit R ⟶ M) ≃ M.val.obj (op T) :=
  M.unitHomEquiv.trans (sectionsTerminalEquiv (hT := hT) (R := R) M)

/-- The unit representation evaluates the original morphism at one. -/
theorem unitHomTerminalEquiv_apply (M : SheafOfModules.{r} R)
    (f : SheafOfModules.unit R ⟶ M) :
    unitHomTerminalEquiv (hT := hT) (R := R) M f = f.val.app (op T) (1 : R.obj.obj (op T)) := rfl

variable [HasSheafify J AddCommGrpCat.{r}]

/-- Maps from the original constant integer sheaf represent terminal sections. -/
def integerHomTerminalEquiv (F : Sheaf J AddCommGrpCat.{r}) :
    ((constantSheaf J AddCommGrpCat.{r}).obj (AddCommGrpCat.of (ULift.{r} ℤ)) ⟶ F) ≃+
      F.obj.obj (op T) :=
  ((constantSheafAdj J AddCommGrpCat.{r} hT).homAddEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- The integer representation uses the original coefficient morphism. -/
theorem integerHomTerminalEquiv_comp {F G : Sheaf J AddCommGrpCat.{r}}
    (f : (constantSheaf J AddCommGrpCat.{r}).obj
      (AddCommGrpCat.of (ULift.{r} ℤ)) ⟶ F) (g : F ⟶ G) :
    integerHomTerminalEquiv hT G (f ≫ g) =
      g.hom.app (op T) (integerHomTerminalEquiv hT F f) := by
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    ((constantSheafAdj _ _ hT).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The original constant-integer map representing one in the native module unit. -/
def unitIntegerMap :
    (constantSheaf J AddCommGrpCat.{r}).obj (AddCommGrpCat.of (ULift.{r} ℤ)) ⟶
      (SheafOfModules.toSheaf R).obj (SheafOfModules.unit R) :=
  (integerHomTerminalEquiv hT _).symm (1 : R.obj.obj (op T))

/-- Section-one normalization of the actual integer-to-unit map. -/
theorem unitIntegerMap_sections :
    integerHomTerminalEquiv hT _ (unitIntegerMap hT R) =
      (1 : R.obj.obj (op T)) := AddEquiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- The original module unit and constant integers represent the same sections. -/
def unitIntegerHomEquiv (M : SheafOfModules.{r} R) :
    (SheafOfModules.unit R ⟶ M) ≃
      ((constantSheaf J AddCommGrpCat.{r}).obj (AddCommGrpCat.of (ULift.{r} ℤ)) ⟶
        (SheafOfModules.toSheaf R).obj M) :=
  (unitHomTerminalEquiv (hT := hT) (R := R) M).trans
    (integerHomTerminalEquiv hT ((SheafOfModules.toSheaf R).obj M)).symm.toEquiv

/-- The Hom comparison is literally forgetting scalars after the section-one map. -/
theorem unitIntegerHomEquiv_apply (M : SheafOfModules.{r} R)
    (f : SheafOfModules.unit R ⟶ M) :
    unitIntegerHomEquiv (hT := hT) (R := R) M f =
      unitIntegerMap hT R ≫ (SheafOfModules.toSheaf R).map f := by
  apply (integerHomTerminalEquiv hT _).injective
  have he : integerHomTerminalEquiv hT _ (unitIntegerHomEquiv (hT := hT) (R := R) M f) =
      unitHomTerminalEquiv (hT := hT) (R := R) M f := AddEquiv.apply_symm_apply _ _
  rw [he, integerHomTerminalEquiv_comp, unitIntegerMap_sections]
  rfl

end CategoryTheory.Sheaf.ModuleCoefficients

namespace PresheafOfModules


variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{s})

set_option backward.isDefEq.respectTransparency false in
/-- Rank one in the larger module universe, over the unchanged scalar presheaf. -/
def liftedUnit : PresheafOfModules.{max s w} R where
  obj X := ModuleCat.of (R.obj X) (ULift.{w} (R.obj X))
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj Y) (ULift.{w} (R.obj Y))))
    { toFun := fun x ↦ ULift.up (R.map f x.down)
      map_add' := by
        intros x y
        apply ULift.ext
        exact (R.map f).hom.map_add x.down y.down
      map_smul' := by
        intros a x
        apply ULift.ext
        exact (R.map f).hom.map_mul a x.down }
  map_id := by
    intro X
    ext x
    change ULift.up (R.map (𝟙 X) x.down) = x
    simp
  map_comp := by intros; ext x; apply ULift.ext; simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Maps from the genuinely lifted rank-one module are compatible sections. -/
def liftedUnitHomEquiv (M : PresheafOfModules.{max s w} R) :
    (liftedUnit.{u, v, w, s} R ⟶ M) ≃ M.sections where
  toFun f := sectionsMk (fun X ↦ f.app X (ULift.up (1 : R.obj X))) (by
    intros X Y g
    rw [← naturality_apply]
    congr 1
    change ULift.up (R.map g 1) = ULift.up 1
    rw [(R.map g).hom.map_one])
  invFun z :=
    { app := fun X ↦ ModuleCat.ofHom
        (((LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).symm (z.val X)).comp
          ULift.moduleEquiv.toLinearMap)
      naturality := fun {X Y} g ↦ by
        ext x
        change R.map g x.down • z.eval Y = M.map g (x.down • z.eval X)
        rw [M.map_smul, sections_property] }
  left_inv f := by
    ext X x
    change x.down • f.app X (ULift.up 1) = f.app X x
    rw [← map_smul]
    have hx : x.down • (ULift.up 1 : ULift.{w} (R.obj X)) = x := by
      apply ULift.ext
      exact mul_one x.down
    exact congrArg (f.app X) hx
  right_inv z := by
    apply sections_ext
    intro X
    change (1 : R.obj X) • z.eval X = z.eval X
    exact one_smul _ _

end PresheafOfModules

namespace SheafOfModules


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{s})

set_option backward.isDefEq.respectTransparency false in
/-- The lifted rank-one module is a sheaf by genuine underlying additive lift. -/
def liftedUnit : SheafOfModules.{max s w} R where
  val := PresheafOfModules.liftedUnit.{u, v, w, s} R.obj
  isSheaf := ((sheafCompose J AddCommGrpCat.uliftFunctor.{w, s}).obj
    ((sheafCompose J (forget₂ RingCat.{s} AddCommGrpCat.{s})).obj R)).property

/-- Hom from the lifted rank-one sheaf evaluates to the original module sections. -/
def liftedUnitHomEquiv (M : SheafOfModules.{max s w} R) :
    (liftedUnit.{u, v, w, s} R ⟶ M) ≃ M.sections :=
  (fullyFaithfulForget R).homEquiv.trans
    (PresheafOfModules.liftedUnitHomEquiv.{u, v, w, s} R.obj M.val)

end SheafOfModules

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})

/-- Terminal evaluation for modules over the unchanged smaller scalar sheaf. -/
def liftedUnitHomTerminalEquiv (M : SheafOfModules.{max r w} R) :
    (SheafOfModules.liftedUnit.{u, v, w, r} R ⟶ M) ≃ M.val.obj (op T) :=
  (SheafOfModules.liftedUnitHomEquiv.{u, v, w, r} R M).trans
    (sectionsTerminalEquiv (hT := hT) (R := R) M)

variable [HasSheafify J AddCommGrpCat.{max r w}]

/-- The actual integer-to-lifted-unit map, normalized by the lifted scalar one. -/
def liftedUnitIntegerMap :
    (constantSheaf J AddCommGrpCat.{max r w}).obj
      (AddCommGrpCat.of (ULift.{max r w} ℤ)) ⟶
      (SheafOfModules.toSheaf R).obj (SheafOfModules.liftedUnit.{u, v, w, r} R) :=
  (integerHomTerminalEquiv hT _).symm (ULift.up (1 : R.obj.obj (op T)))

/-- Section-one normalization with unchanged small scalars. -/
theorem liftedUnitIntegerMap_sections :
    integerHomTerminalEquiv hT _ (liftedUnitIntegerMap.{u, v, r, w} hT R) =
      ULift.up (1 : R.obj.obj (op T)) := AddEquiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- Both original functors represent the same terminal sections in the larger universe. -/
def liftedUnitIntegerHomEquiv (M : SheafOfModules.{max r w} R) :
    (SheafOfModules.liftedUnit.{u, v, w, r} R ⟶ M) ≃
      ((constantSheaf J AddCommGrpCat.{max r w}).obj
        (AddCommGrpCat.of (ULift.{max r w} ℤ)) ⟶ (SheafOfModules.toSheaf R).obj M) :=
  (liftedUnitHomTerminalEquiv.{u, v, r, w} (hT := hT) (R := R) M).trans
    (integerHomTerminalEquiv hT ((SheafOfModules.toSheaf R).obj M)).symm.toEquiv

/-- No assumed comparison: the Hom map is literal scalar-forgetting precomposition. -/
theorem liftedUnitIntegerHomEquiv_apply (M : SheafOfModules.{max r w} R)
    (f : SheafOfModules.liftedUnit.{u, v, w, r} R ⟶ M) :
    liftedUnitIntegerHomEquiv.{u, v, r, w} (hT := hT) (R := R) M f =
      liftedUnitIntegerMap.{u, v, r, w} hT R ≫ (SheafOfModules.toSheaf R).map f := by
  apply (integerHomTerminalEquiv hT _).injective
  have he : integerHomTerminalEquiv hT _
      (liftedUnitIntegerHomEquiv.{u, v, r, w} (hT := hT) (R := R) M f) =
      liftedUnitHomTerminalEquiv.{u, v, r, w} (hT := hT) (R := R) M f :=
    AddEquiv.apply_symm_apply _ _
  rw [he, integerHomTerminalEquiv_comp, liftedUnitIntegerMap_sections]
  rfl

end CategoryTheory.Sheaf.ModuleCoefficients
