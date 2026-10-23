/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedExtNormalization
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctor
public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison

/-!
# Native resolution restriction and the represented right-derived functor

An exact functor maps a source resolution to an exact complex. The existing
comparison lift into a target injective resolution induces an actual map on
Hom complexes and their homology. The native right-derived comparison
identifies this chain-level construction with the original exact-functor Ext
map. No preservation of injective objects by the exact functor is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u₁ u₂ v e₁ e₂

namespace CategoryTheory.Sheaf.ModuleCoefficients

/-- The identity forgetful functor on additive commutative groups. -/
local instance derivedRestrictionHasForget₂ : HasForget₂ AddCommGrpCat.{v} AddCommGrpCat.{v} where
  forget₂ := 𝟭 _

local instance derivedRestrictionForget₂Additive :
    (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).Additive :=
  inferInstanceAs (Functor.Additive (𝟭 AddCommGrpCat.{v}))

local instance derivedRestrictionForget₂PreservesHomology :
    (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).PreservesHomology :=
  inferInstanceAs (Functor.PreservesHomology (𝟭 AddCommGrpCat.{v}))

variable {A : Type u₁} [Category.{v} A] [Abelian A]
  {B : Type u₂} [Category.{v} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X M : A} {Y N : B} (c : Y ⟶ F.obj X)
  (I : InjectiveResolution M) (J : InjectiveResolution N)

/-- The actual map of represented cochain complexes for any supplied resolution lift. -/
def representedResolutionRestriction
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶ J.cocomplex) :
    ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      ((preadditiveCoyoneda.obj (op Y)).mapHomologicalComplex (.up ℕ)).obj J.cocomplex where
  f n := AddCommGrpCat.ofHom
    (show (X ⟶ I.cocomplex.X n) →+ (Y ⟶ J.cocomplex.X n) from
    { toFun := fun a => c ≫ F.map a ≫ φ.f n
      map_zero' := by rw [Functor.map_zero, zero_comp, comp_zero]
      map_add' := by intros; rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add] })
  comm' i j hij := by
    ext a
    change X ⟶ I.cocomplex.X i at a
    change (c ≫ F.map a ≫ φ.f i) ≫ J.cocomplex.d i j =
      c ≫ F.map (a ≫ I.cocomplex.d i j) ≫ φ.f j
    rw [Category.assoc, Category.assoc, φ.comm]
    simp only [Functor.map_comp, Category.assoc]
    rfl

variable [EnoughInjectives A] [EnoughInjectives B]

/-- Restriction on the native represented right-derived groups, constructed on
actual injective-resolution complexes before passing to homology. -/
def representedRightDerivedRestriction (n : ℕ) :
    ((preadditiveCoyoneda.obj (op X)).rightDerived n).obj M ⟶
      ((preadditiveCoyoneda.obj (op Y)).rightDerived n).obj (F.obj M) :=
  ((injectiveResolution M).isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) n).hom ≫
    HomologicalComplex.homologyMap
      (representedResolutionRestriction F c (injectiveResolution M)
        (injectiveResolution (F.obj M))
        (InjectiveResolution.ExactFunctor.lift F (injectiveResolution M)
          (injectiveResolution (F.obj M)) (𝟙 _))) n ≫
    ((injectiveResolution (F.obj M)).isoRightDerivedObj
      (preadditiveCoyoneda.obj (op Y)) n).inv

variable [HasExt.{e₁} A] [HasExt.{e₂} B]

/-- The chain-comparison restriction is exactly the canonical original Ext restriction. -/
theorem representedRightDerivedRestriction_ext (n : ℕ) (x : Ext.{e₁} X M n) :
    representedRightDerivedRestriction F c n (extRightDerivedRepresentedAddEquiv X M n x) =
      extRightDerivedRepresentedAddEquiv Y (F.obj M) n (F.extPrecompMap c M n x) := by
  let I := injectiveResolution M
  let J := injectiveResolution (F.obj M)
  let φ := InjectiveResolution.ExactFunctor.lift F I J (𝟙 _)
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  have hmap := InjectiveResolution.ExactFunctor.extMk_mapExactFunctor_comp_mk₀
    F I J (𝟙 _) φ (InjectiveResolution.ExactFunctor.lift_commutes_zero F I J (𝟙 _)) a ha
  simp only [Ext.comp_mk₀_id] at hmap
  rw [Functor.extPrecompMap_apply, hmap, InjectiveResolution.mk₀_comp_extMk,
    extRightDerivedRepresentedAddEquiv_extMk, extRightDerivedRepresentedAddEquiv_extMk]
  let K := ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let z := K.homologyπ n (K.cyclesMk a (n + 1) (by simp) ha)
  have hi : (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) n).hom
      ((I.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) n).inv z) = z :=
    ConcreteCategory.congr_hom (I.isoRightDerivedObj
      (preadditiveCoyoneda.obj (op X)) n).inv_hom_id z
  change (J.isoRightDerivedObj (preadditiveCoyoneda.obj (op Y)) n).inv
      (HomologicalComplex.homologyMap (representedResolutionRestriction F c I J φ) n
        ((I.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) n).hom
          ((I.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) n).inv z))) = _
  rw [hi]
  exact congrArg (J.isoRightDerivedObj (preadditiveCoyoneda.obj (op Y)) n).inv
    (homologyMap_cyclesMk (representedResolutionRestriction F c I J φ) a
      (by simp) ha)

end CategoryTheory.Sheaf.ModuleCoefficients
