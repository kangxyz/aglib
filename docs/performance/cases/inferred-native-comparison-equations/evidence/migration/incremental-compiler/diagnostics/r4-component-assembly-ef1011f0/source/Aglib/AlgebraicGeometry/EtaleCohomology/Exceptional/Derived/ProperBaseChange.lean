/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.BaseChange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Conservative

/-!
# Frozen assembly from the original abelian component

The common proof takes only morphisms and an already-typed component equation.
No abelian exchange natural transformation is passed to the common helper.
These are frozen-context diagnostics, not production theorem coverage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4ComponentAssembly

private theorem isIso_original_arrow_of_component_equation
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {M N : C} {P A B Q : D} (β : M ⟶ N) (a : A ⟶ B)
    (u : P ⟶ A) (v : B ⟶ Q) (s : P ⟶ F.obj M) (t : F.obj N ⟶ Q)
    (h : u ≫ a ≫ v = s ≫ F.map β ≫ t)
    (ha : IsIso a) (hu : IsIso u) (hv : IsIso v)
    (hs : IsIso s) (ht : IsIso t) (hF : F.ReflectsIsomorphisms) : IsIso β := by
  let : IsIso a := ha
  let : IsIso u := hu
  let : IsIso v := hv
  let : IsIso s := hs
  let : IsIso t := ht
  let : F.ReflectsIsomorphisms := hF
  have hc : IsIso (s ≫ F.map β ≫ t) := by
    rw [← h]
    infer_instance
  have hr : IsIso (F.map β ≫ t) := (isIso_comp_left_iff s _).mp hc
  have : IsIso (F.map β) := (isIso_comp_right_iff _ t).mp hr
  exact isIso_of_reflects_iso β F

open Coefficients

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wAX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Diagnostic: the abelian component remains variable and the module arrow is literal. -/
theorem variableComponent (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (a : (derivedInverseImage g).obj
        ((derivedDirectImage f).obj ((moduleDerivedUnderlying Λ X).obj K)) ⟶
      (derivedDirectImage f').obj
        ((derivedInverseImage g').obj ((moduleDerivedUnderlying Λ X).obj K)))
    (hEq : (derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K) ≫
      a ≫
      (derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K) =
    (moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K) ≫
      (moduleDerivedUnderlying Λ S').map
        ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K))
    (ha : IsIso a)
    (hu : IsIso ((derivedInverseImage g).map
      ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K)))
    (hv : IsIso ((derivedDirectImage f').map
      ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K)))
    (hs : IsIso ((moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
      ((moduleDerivedDirectImage Λ f).obj K)))
    (ht : IsIso ((moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
      ((moduleDerivedInverseImage Λ g').obj K)))
    (hF : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms)
    : IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
  exact isIso_original_arrow_of_component_equation (moduleDerivedUnderlying Λ S')
    ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)
    a
    ((derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K))
    ((derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K))
    ((moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
      ((moduleDerivedDirectImage Λ f).obj K))
    ((moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
      ((moduleDerivedInverseImage Λ g').obj K)) hEq ha hu hv hs ht hF

/-- Diagnostic: instantiate the original abelian component and pass its existing fact directly. -/
theorem nativeComponentDirect (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hEq : (derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K) ≫
      ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        ((moduleDerivedUnderlying Λ X).obj K)) ≫
      (derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K) =
    (moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K) ≫
      (moduleDerivedUnderlying Λ S').map
        ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K))
    (ha : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        ((moduleDerivedUnderlying Λ X).obj K)))
    (hu : IsIso ((derivedInverseImage g).map
      ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K)))
    (hv : IsIso ((derivedDirectImage f').map
      ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K)))
    (hs : IsIso ((moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
      ((moduleDerivedDirectImage Λ f).obj K)))
    (ht : IsIso ((moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
      ((moduleDerivedInverseImage Λ g').obj K)))
    (hF : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms)
    : IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
  exact isIso_original_arrow_of_component_equation (moduleDerivedUnderlying Λ S')
    ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)
    ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        ((moduleDerivedUnderlying Λ X).obj K))
    ((derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K))
    ((derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K))
    ((moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
      ((moduleDerivedDirectImage Λ f).obj K))
    ((moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
      ((moduleDerivedInverseImage Λ g').obj K)) hEq ha hu hv hs ht hF

/-- Diagnostic control: same original component, but retrieve its given fact by instance search. -/
theorem nativeComponentInstance (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hEq : (derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K) ≫
      ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        ((moduleDerivedUnderlying Λ X).obj K)) ≫
      (derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K) =
    (moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K) ≫
      (moduleDerivedUnderlying Λ S').map
        ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K))
    [ha : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        ((moduleDerivedUnderlying Λ X).obj K))]
    (hu : IsIso ((derivedInverseImage g).map
      ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K)))
    (hv : IsIso ((derivedDirectImage f').map
      ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K)))
    (hs : IsIso ((moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
      ((moduleDerivedDirectImage Λ f).obj K)))
    (ht : IsIso ((moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
      ((moduleDerivedInverseImage Λ g').obj K)))
    (hF : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms)
    : IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
  exact isIso_original_arrow_of_component_equation (moduleDerivedUnderlying Λ S')
    ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)
    ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        ((moduleDerivedUnderlying Λ X).obj K))
    ((derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K))
    ((derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K))
    ((moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
      ((moduleDerivedDirectImage Λ f).obj K))
    ((moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
      ((moduleDerivedInverseImage Λ g').obj K)) hEq inferInstance hu hv hs ht hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4ComponentAssembly
