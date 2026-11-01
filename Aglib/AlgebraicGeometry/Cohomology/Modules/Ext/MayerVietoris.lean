/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Open
public import Aglib.AlgebraicGeometry.Modules.Generators.Pullback
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Module-open Mayer–Vietoris and the original cohomology boundary

The native free module sheaves on a Mayer–Vietoris square form a short exact
sequence with maps `(iU,-iV)` and `(jU,jV)`. The integer generators give a
morphism from the original integer-open sequence to its scalar-forgotten
image. Thus unsigned precomposition by its extension class is exactly the
original Mayer–Vietoris connecting map in every natural degree.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u v u' v' w w'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{v}) [HasSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

omit [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
private theorem toSheaf_preservesZeroMorphisms_at
    [sourceZero : HasZeroMorphisms (SheafOfModules.{v} R)]
    [targetZero : HasZeroMorphisms (Sheaf J AddCommGrpCat.{v})] :
    @Functor.PreservesZeroMorphisms (SheafOfModules.{v} R) inferInstance
      (Sheaf J AddCommGrpCat.{v}) inferInstance sourceZero targetZero (toSheaf.{v} R) := by
  let nativeSourceZero : HasZeroMorphisms (SheafOfModules.{v} R) :=
    @Preadditive.preadditiveHasZeroMorphisms (SheafOfModules.{v} R) inferInstance
      (SheafOfModules.instPreadditive R)
  let nativeTargetZero : HasZeroMorphisms (Sheaf J AddCommGrpCat.{v}) :=
    @Preadditive.preadditiveHasZeroMorphisms (Sheaf J AddCommGrpCat.{v}) inferInstance
      inferInstance
  let preserves (s : HasZeroMorphisms (SheafOfModules.{v} R))
      (t : HasZeroMorphisms (Sheaf J AddCommGrpCat.{v})) : Prop :=
    @Functor.PreservesZeroMorphisms (SheafOfModules.{v} R) inferInstance
      (Sheaf J AddCommGrpCat.{v}) inferInstance s t (toSheaf.{v} R)
  have native : preserves nativeSourceZero nativeTargetZero := ⟨fun _ _ => rfl⟩
  exact Eq.mp (congrArg₂ preserves (Subsingleton.elim nativeSourceZero sourceZero)
    (Subsingleton.elim nativeTargetZero targetZero)) native

variable [HasWeakSheafify J (Type v)] (S : J.MayerVietorisSquare)

/-- A native Mayer–Vietoris square is a pushout after taking its free module sheaves. -/
theorem freeYonedaSheaf_isPushout :
    (S.toSquare.map (freeYonedaSheafFunctor R)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro M
  let T : Sheaf J (Type v) :=
    (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{v})).obj ((toSheaf R).obj M)
  have hT : (S.toSquare.op.map T.obj).IsPullback := S.sheafCondition_of_sheaf T
  refine (Square.IsPullback.iff_of_equiv _ _
    (freeYonedaSheafHomEquiv R S.X₄ M)
    (freeYonedaSheafHomEquiv R S.X₂ M)
    (freeYonedaSheafHomEquiv R S.X₃ M)
    (freeYonedaSheafHomEquiv R S.X₁ M) ?_ ?_ ?_ ?_).2 hT
  all_goals
    funext p
    exact freeYonedaSheafHomEquiv_naturality R _ M p

/-- The actual free-module Mayer–Vietoris complex, with difference then sum. -/
def mayerVietorisShortComplex : ShortComplex (SheafOfModules.{v} R) where
  X₁ := (freeYonedaSheafFunctor R).obj S.X₁
  X₂ := (freeYonedaSheafFunctor R).obj S.X₂ ⊞
    (freeYonedaSheafFunctor R).obj S.X₃
  X₃ := (freeYonedaSheafFunctor R).obj S.X₄
  f := biprod.lift ((freeYonedaSheafFunctor R).map S.f₁₂)
    (-((freeYonedaSheafFunctor R).map S.f₁₃))
  g := biprod.desc ((freeYonedaSheafFunctor R).map S.f₂₄)
    ((freeYonedaSheafFunctor R).map S.f₃₄)
  zero := (S.toSquare.map (freeYonedaSheafFunctor R)).cokernelCofork.condition

/-- Actual sheaf gluing supplies the original free-module short exact sequence. -/
theorem mayerVietorisShortComplex_shortExact :
    (mayerVietorisShortComplex R S).ShortExact := by
  have : Mono ((freeYonedaSheafFunctor R).map S.f₁₃) :=
    freeYonedaSheafFunctor_map_mono R S.f₁₃
  have : Mono ((mayerVietorisShortComplex R S).f ≫ biprod.snd) := by
    dsimp only [mayerVietorisShortComplex]
    rw [biprod.lift_snd]
    infer_instance
  have : Mono (mayerVietorisShortComplex R S).f := mono_of_mono _ biprod.snd
  have hc := (freeYonedaSheaf_isPushout R S).isColimitCokernelCofork
  have he := (mayerVietorisShortComplex R S).exact_and_epi_g_iff_g_is_cokernel.2 ⟨hc⟩
  exact { exact := he.1, epi_g := he.2 }

end SheafOfModules

attribute [local instance] SheafOfModules.toSheaf_preservesZeroMorphisms_at

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An actual short-exact-sequence morphism preserves the unsigned source boundary
under the original exact-functor Ext comparison, in every degree. -/
theorem Functor.extPrecompMap_source_extClass
    {S : ShortComplex C} (hS : S.ShortExact)
    {T : ShortComplex D} (hT : T.ShortExact) (τ : T ⟶ S.map F)
    (M : C) {n n' : ℕ} (h : 1 + n = n') (x : Ext.{w} S.X₁ M n) :
    F.extPrecompMap τ.τ₃ M n' (hS.extClass.comp x h) =
      hT.extClass.comp (F.extPrecompMap τ.τ₁ M n x) h := by
  rw [Functor.extPrecompMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Functor.extPrecompMap_apply]
  calc
    _ = ((Ext.mk₀ τ.τ₃).comp (hS.map_of_exact F).extClass (zero_add 1)).comp
        (x.mapExactFunctor F) h :=
      (Ext.comp_assoc _ _ _ (zero_add 1) h (by omega)).symm
    _ = (hT.extClass.comp (Ext.mk₀ τ.τ₁) (add_zero 1)).comp
        (x.mapExactFunctor F) h := by
      rw [hT.extClass_naturality (hS.map_of_exact F) τ]
    _ = _ := Ext.comp_assoc_of_second_deg_zero _ _ _ h

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry TopologicalSpace

variable (X : Scheme.{u}) (U V : X.Opens)

/-- The original module-open sequence, with maps `(iU,-iV)` and `(jU,jV)`. -/
abbrev moduleOpenMayerVietorisShortComplex : ShortComplex X.Modules :=
  SheafOfModules.mayerVietorisShortComplex X.ringCatSheaf (Opens.mayerVietorisSquare U V)

/-- The native module-open Mayer–Vietoris sequence is short exact on every scheme. -/
theorem moduleOpenMayerVietoris_shortExact :
    (moduleOpenMayerVietorisShortComplex X U V).ShortExact :=
  SheafOfModules.mayerVietorisShortComplex_shortExact X.ringCatSheaf
    (Opens.mayerVietorisSquare U V)

local instance : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Additive :=
  ⟨by intros; rfl⟩

private theorem moduleToSheaf_preservesZeroMorphisms
    [sourceZero : HasZeroMorphisms X.Modules]
    [targetZero : HasZeroMorphisms
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] :
    @Functor.PreservesZeroMorphisms X.Modules inferInstance
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) inferInstance
      sourceZero targetZero (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
  SheafOfModules.toSheaf_preservesZeroMorphisms_at X.ringCatSheaf
    (sourceZero := sourceZero) (targetZero := targetZero)

attribute [local instance] moduleToSheaf_preservesZeroMorphisms

/-- The image of the original module-open sequence under actual scalar forgetting. -/
def moduleOpenMayerVietorisAdditiveShortComplex :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
  letI : @Functor.PreservesZeroMorphisms X.Modules inferInstance
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) inferInstance
      inferInstance inferInstance (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := by
    exact moduleToSheaf_preservesZeroMorphisms X
      (sourceZero := inferInstance) (targetZero := inferInstance)
  exact (moduleOpenMayerVietorisShortComplex X U V).map
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf)

/-- The original integer generators form a morphism into the scalar-forgotten
actual module-open sequence. Its signs agree with the original integer sequence. -/
def moduleOpenIntegerMayerVietorisMap :
    (Opens.mayerVietorisSquare U V).shortComplex ⟶
      moduleOpenMayerVietorisAdditiveShortComplex X U V where
  τ₁ := moduleOpenIntegerMap X (U ⊓ V)
  τ₂ := biprod.desc
    (moduleOpenIntegerMap X U ≫ (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map biprod.inl)
    (moduleOpenIntegerMap X V ≫ (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map biprod.inr)
  τ₃ := moduleOpenIntegerMap X (U ⊔ V)
  comm₁₂ := by
    change moduleOpenIntegerMap X (U ⊓ V) ≫
        (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map
          (biprod.lift
            ((Scheme.Modules.openFreeFunctor X).map (homOfLE inf_le_left))
            (-((Scheme.Modules.openFreeFunctor X).map (homOfLE inf_le_right)))) =
      biprod.lift
          ((additiveOpenFreeFunctor X).map (homOfLE inf_le_left))
          (-((additiveOpenFreeFunctor X).map (homOfLE inf_le_right))) ≫
        biprod.desc
          (moduleOpenIntegerMap X U ≫
            (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map biprod.inl)
          (moduleOpenIntegerMap X V ≫
            (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map biprod.inr)
    rw [biprod.lift_desc]
    simp only [biprod.lift_eq, Functor.map_add, Functor.map_comp, Functor.map_neg,
      Preadditive.comp_add, Preadditive.comp_neg, Preadditive.neg_comp, ← Category.assoc]
    rw [moduleOpenIntegerMap_naturality, moduleOpenIntegerMap_naturality]
    rfl
  comm₂₃ := by
    apply biprod.hom_ext'
    · dsimp only [moduleOpenMayerVietorisAdditiveShortComplex, moduleOpenMayerVietorisShortComplex,
      SheafOfModules.mayerVietorisShortComplex,
        GrothendieckTopology.MayerVietorisSquare.shortComplex, ShortComplex.map_g]
      simp only [biprod.inl_desc_assoc, Category.assoc, ← Functor.map_comp, biprod.inl_desc]
      exact (moduleOpenIntegerMap_naturality X _).symm
    · dsimp only [moduleOpenMayerVietorisAdditiveShortComplex, moduleOpenMayerVietorisShortComplex,
      SheafOfModules.mayerVietorisShortComplex,
        GrothendieckTopology.MayerVietorisSquare.shortComplex, ShortComplex.map_g]
      simp only [biprod.inr_desc_assoc, Category.assoc, ← Functor.map_comp, biprod.inr_desc]
      exact (moduleOpenIntegerMap_naturality X _).symm

/-- The canonical comparison carries the actual module-open source extension
class to the unchanged native Mayer–Vietoris boundary, without a degree sign. -/
theorem moduleOpenExtCohomologyMap_mayerVietorisDelta (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (Scheme.Modules.openFree X (U ⊓ V)) M n) :
    moduleOpenExtCohomologyMap X (U ⊔ V) M (n + 1)
        ((moduleOpenMayerVietoris_shortExact X U V).extClass.comp x (by omega)) =
      (Opens.mayerVietorisSquare U V).δ (moduleAddSheaf X M) n (n + 1) rfl
        (moduleOpenExtCohomologyMap X (U ⊓ V) M n x) :=
by
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let : PreservesFiniteColimits F :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let : @Functor.PreservesZeroMorphisms X.Modules inferInstance
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) inferInstance
      inferInstance inferInstance F := by
    exact moduleToSheaf_preservesZeroMorphisms X
      (sourceZero := inferInstance) (targetZero := inferInstance)
  have h := Functor.extPrecompMap_source_extClass F
    (moduleOpenMayerVietoris_shortExact X U V)
    (Opens.mayerVietorisSquare U V).shortComplex_shortExact
    (moduleOpenIntegerMayerVietorisMap X U V) M (show 1 + n = n + 1 by omega) x
  exact h

/-- The inverse original comparison recovers precisely the unsigned module source boundary. -/
theorem moduleOpenExtCohomologyAddEquiv_symm_mayerVietorisDelta
    (M : X.Modules) (n : ℕ) (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n (U ⊓ V)) :
    (moduleOpenExtCohomologyAddEquiv X (U ⊔ V) M (n + 1)).symm
        ((Opens.mayerVietorisSquare U V).δ (moduleAddSheaf X M) n (n + 1) rfl x) =
      (moduleOpenMayerVietoris_shortExact X U V).extClass.comp
        ((moduleOpenExtCohomologyAddEquiv X (U ⊓ V) M n).symm x) (by omega) := by
  apply (moduleOpenExtCohomologyAddEquiv X (U ⊔ V) M (n + 1)).injective
  rw [AddEquiv.apply_symm_apply]
  change _ = moduleOpenExtCohomologyMap X (U ⊔ V) M (n + 1) _
  rw [moduleOpenExtCohomologyMap_mayerVietorisDelta]
  change _ = (Opens.mayerVietorisSquare U V).δ (moduleAddSheaf X M) n (n + 1) rfl
    ((moduleOpenExtCohomologyAddEquiv X (U ⊓ V) M n)
      ((moduleOpenExtCohomologyAddEquiv X (U ⊓ V) M n).symm x))
  rw [AddEquiv.apply_symm_apply]

/-- The original binary Ext decomposition followed by the two canonical open comparisons. -/
def moduleOpenMayerVietorisMiddleIso (M : X.Modules) (n : ℕ) :
    AddCommGrpCat.of (Ext.{u + 1}
      (Scheme.Modules.openFree X U ⊞ Scheme.Modules.openFree X V) M n) ≅
        Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U ⊞
          Sheaf.H'.{u + 1} (moduleAddSheaf X M) n V :=
  ((Ext.biprodAddEquiv.trans
    (AddEquiv.prodCongr (moduleOpenExtCohomologyAddEquiv X U M n)
      (moduleOpenExtCohomologyAddEquiv X V M n))).trans
      (AddCommGrpCat.biprodIsoProd _ _).symm.addCommGroupIsoToAddEquiv).toAddCommGrpIso

/-- Both original module source restrictions become the native pair of restrictions. -/
theorem moduleOpenMayerVietorisMiddleIso_toBiprod (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (Scheme.Modules.openFree X (U ⊔ V)) M n) :
    (moduleOpenMayerVietorisMiddleIso X U V M n).hom
        ((Ext.mk₀ (moduleOpenMayerVietorisShortComplex X U V).g).comp x (zero_add n)) =
      (Opens.mayerVietorisSquare U V).toBiprod (moduleAddSheaf X M) n
        (moduleOpenExtCohomologyMap X (U ⊔ V) M n x) := by
  rw [(Opens.mayerVietorisSquare U V).toBiprod_apply]
  change (AddCommGrpCat.biprodIsoProd _ _).inv (_, _) =
    (AddCommGrpCat.biprodIsoProd _ _).inv (_, _)
  congr 1
  apply Prod.ext
  · change moduleOpenExtCohomologyMap X U M n
      ((Ext.mk₀ biprod.inl).comp
        ((Ext.mk₀ (moduleOpenMayerVietorisShortComplex X U V).g).comp x (zero_add n))
          (zero_add n)) = _
    rw [Ext.mk₀_comp_mk₀_assoc]
    change moduleOpenExtCohomologyMap X U M n
      ((Ext.mk₀ (biprod.inl ≫ (moduleOpenMayerVietorisShortComplex X U V).g)).comp x
        (zero_add n)) = _
    rw [show biprod.inl ≫ (moduleOpenMayerVietorisShortComplex X U V).g =
      (Scheme.Modules.openFreeFunctor X).map (homOfLE le_sup_left) from biprod.inl_desc _ _]
    exact moduleOpenExtCohomologyMap_restriction X _ M n x
  · change moduleOpenExtCohomologyMap X V M n
      ((Ext.mk₀ biprod.inr).comp
        ((Ext.mk₀ (moduleOpenMayerVietorisShortComplex X U V).g).comp x (zero_add n))
          (zero_add n)) = _
    rw [Ext.mk₀_comp_mk₀_assoc]
    change moduleOpenExtCohomologyMap X V M n
      ((Ext.mk₀ (biprod.inr ≫ (moduleOpenMayerVietorisShortComplex X U V).g)).comp x
        (zero_add n)) = _
    rw [show biprod.inr ≫ (moduleOpenMayerVietorisShortComplex X U V).g =
      (Scheme.Modules.openFreeFunctor X).map (homOfLE le_sup_right) from biprod.inr_desc _ _]
    exact moduleOpenExtCohomologyMap_restriction X _ M n x

/-- The original signed module source map becomes the native difference of restrictions. -/
theorem moduleOpenMayerVietorisMiddleIso_fromBiprod (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (Scheme.Modules.openFree X U ⊞ Scheme.Modules.openFree X V) M n) :
    moduleOpenExtCohomologyMap X (U ⊓ V) M n
        ((Ext.mk₀ (moduleOpenMayerVietorisShortComplex X U V).f).comp x (zero_add n)) =
      (Opens.mayerVietorisSquare U V).fromBiprod (moduleAddSheaf X M) n
        ((moduleOpenMayerVietorisMiddleIso X U V M n).hom x) := by
  change moduleOpenExtCohomologyMap X (U ⊓ V) M n
      ((Ext.mk₀ (biprod.lift
        ((Scheme.Modules.openFreeFunctor X).map (homOfLE inf_le_left))
        (-((Scheme.Modules.openFreeFunctor X).map (homOfLE inf_le_right))))).comp x
          (zero_add n)) =
    (Opens.mayerVietorisSquare U V).fromBiprod (moduleAddSheaf X M) n
      ((AddCommGrpCat.biprodIsoProd _ _).inv (_, _))
  rw [(Opens.mayerVietorisSquare U V).fromBiprod_biprodIsoProd_inv_apply,
    biprod.lift_eq, Preadditive.neg_comp, Ext.mk₀_add, Ext.add_comp,
    Ext.mk₀_neg, Ext.neg_comp, map_add, map_neg]
  rw [← Ext.mk₀_comp_mk₀_assoc, ← Ext.mk₀_comp_mk₀_assoc]
  rw [moduleOpenExtCohomologyMap_restriction, moduleOpenExtCohomologyMap_restriction]
  simp only [sub_eq_add_neg]
  rfl

open ComposableArrows in
/-- The entire original contravariant module-Ext sequence is the unchanged native
abelian-sheaf Mayer–Vietoris sequence, at all natural degrees and every coefficient. -/
def moduleOpenMayerVietorisSequenceIso (M : X.Modules) (n : ℕ) :
    Ext.contravariantSequence (moduleOpenMayerVietoris_shortExact X U V) M n (n + 1)
        (by omega) ≅
      (Opens.mayerVietorisSquare U V).sequence (moduleAddSheaf X M) n (n + 1) rfl := by
  refine isoMk₅ (moduleOpenExtCohomologyAddEquiv X (U ⊔ V) M n).toAddCommGrpIso
    (moduleOpenMayerVietorisMiddleIso X U V M n)
    (moduleOpenExtCohomologyAddEquiv X (U ⊓ V) M n).toAddCommGrpIso
    (moduleOpenExtCohomologyAddEquiv X (U ⊔ V) M (n + 1)).toAddCommGrpIso
    (moduleOpenMayerVietorisMiddleIso X U V M (n + 1))
    (moduleOpenExtCohomologyAddEquiv X (U ⊓ V) M (n + 1)).toAddCommGrpIso
    ?_ ?_ ?_ ?_ ?_
  · ext x
    exact moduleOpenMayerVietorisMiddleIso_toBiprod X U V M n x
  · ext x
    exact moduleOpenMayerVietorisMiddleIso_fromBiprod X U V M n x
  · ext x
    exact moduleOpenExtCohomologyMap_mayerVietorisDelta X U V M n x
  · ext x
    exact moduleOpenMayerVietorisMiddleIso_toBiprod X U V M (n + 1) x
  · ext x
    exact moduleOpenMayerVietorisMiddleIso_fromBiprod X U V M (n + 1) x

/-- The original top-open universal map is an isomorphism with the original structure module. -/
instance moduleOpenTopUnitMap_isIso : IsIso (moduleOpenTopUnitMap X) := by
  apply isIso_of_coyoneda_map_bijective
  intro M
  have h : (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ M => moduleOpenTopUnitMap X ≫ f) =
      (Scheme.Modules.unitHomGlobalSectionsEquiv X M).trans
        (Scheme.Modules.openFreeHomEquiv X ⊤ M).symm := by
    funext f
    apply (Scheme.Modules.openFreeHomEquiv X ⊤ M).injective
    rw [Scheme.Modules.openFreeHomEquiv_comp]
    change Scheme.Modules.Hom.app f ⊤ ((Scheme.Modules.openFreeHomEquiv X ⊤ _)
      ((Scheme.Modules.openFreeHomEquiv X ⊤ _).symm (1 : Γ(X, ⊤)))) =
      (Scheme.Modules.openFreeHomEquiv X ⊤ M)
        ((Scheme.Modules.openFreeHomEquiv X ⊤ M).symm
          (Scheme.Modules.unitHomGlobalSectionsEquiv X M f))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  rw [h]
  exact Equiv.bijective _

/-- For a cover of the whole scheme, the actual module-open extension class
has source the original structure module by its original universal map. -/
def moduleOpenMayerVietorisUnitExtClass (hUV : U ⊔ V = ⊤) :
    Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules)
      (Scheme.Modules.openFree X (U ⊓ V)) 1 :=
  (Ext.mk₀ ((asIso (moduleOpenTopUnitMap X)).inv ≫
    (Scheme.Modules.openFreeFunctor X).map (homOfLE hUV.symm.le))).comp
      (moduleOpenMayerVietoris_shortExact X U V).extClass (zero_add 1)

/-- The whole-space source boundary retains both original unit/integer-one
normalizations and the unchanged native Mayer–Vietoris connecting operator. -/
theorem moduleOpenExtCohomologyMap_mayerVietorisUnitDelta (hUV : U ⊔ V = ⊤)
    (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (Scheme.Modules.openFree X (U ⊓ V)) M n) :
    moduleExtCohomologyMap X M (n + 1)
        ((moduleOpenMayerVietorisUnitExtClass X U V hUV).comp x (by omega)) =
      sheafHPrimeTopAddEquiv X (moduleAddSheaf X M) (n + 1)
        ((Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf X M) (n + 1)).map
          (homOfLE hUV.symm.le).op
          ((Opens.mayerVietorisSquare U V).δ (moduleAddSheaf X M) n (n + 1) rfl
            (moduleOpenExtCohomologyMap X (U ⊓ V) M n x))) := by
  dsimp only [moduleOpenMayerVietorisUnitExtClass]
  rw [Ext.comp_assoc _ _ _ (zero_add 1) (show 1 + n = n + 1 by omega)
      (show 0 + 1 + n = n + 1 by omega),
    ← moduleOpenExtCohomologyMap_top]
  congr 1
  rw [Ext.mk₀_comp_mk₀_assoc]
  simp only [asIso_inv, IsIso.hom_inv_id_assoc]
  rw [moduleOpenExtCohomologyMap_restriction,
    moduleOpenExtCohomologyMap_mayerVietorisDelta]

end AlgebraicGeometry.Scheme.Cohomology
