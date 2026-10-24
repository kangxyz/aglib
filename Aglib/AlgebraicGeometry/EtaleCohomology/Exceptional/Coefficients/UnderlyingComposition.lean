/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.NativeAdjunctionUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeMate
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.VerticalReflection
public import Aglib.CategoryTheory.Functor.CompositionCubeWhole

/-!
# Original scalar-forgetting composition and source squares

The specified native inverse-image comparison commutes with the original composition
isomorphisms. This is reflected from the original direct-image composition through the
actual adjunction mates. Its source-square compatibility retains the supplied equality
of base maps, with no cartesianness or invertibility hypothesis on exchange maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The forward native direct-image comparison retains the inverse original abelian
direct-image comparison. -/
theorem moduleDirectImageCompIso_hom_underlying {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (M : ModuleSheaf T Λ) :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map
        ((moduleDirectImageCompIso Λ f g).hom.app M) =
      (directImageCompIso f g).inv.app
        ((SheafOfModules.toSheaf.{u + 1} (constantRing T Λ)).obj M) := by
  have h : ((SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).mapIso
      ((moduleDirectImageCompIso Λ f g).app M)).symm =
      (directImageCompIso f g).app
        ((SheafOfModules.toSheaf.{u + 1} (constantRing T Λ)).obj M) := by
    apply Iso.ext
    exact moduleDirectImageCompIso_inv_underlying Λ f g M
  exact congrArg Iso.inv h

/-- The original scalar-forgetting inverse comparisons preserve the original
inverse-image composition, by reflection through their actual mates. -/
@[reassoc]
theorem moduleInverseImageUnderlyingIso_inv_comp {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (M : ModuleSheaf X Λ) :
    (inverseImageComp f g).hom.app
        ((SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).obj M) ≫
      (inverseImage g).map ((moduleInverseImageUnderlyingIso Λ f).inv.app M) ≫
      (moduleInverseImageUnderlyingIso Λ g).inv.app ((moduleInverseImage f Λ).obj M) =
    (moduleInverseImageUnderlyingIso Λ (g ≫ f)).inv.app M ≫
      (SheafOfModules.toSheaf.{u + 1} (constantRing T Λ)).map
        ((moduleInverseImageCompIso Λ f g).hom.app M) := by
  apply verticalSquareEquation
    (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ f).inv)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ g).inv)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ (g ≫ f)).inv)
    (moduleInverseImageCompIso Λ f g) (inverseImageComp f g)
    (moduleDirectImageCompIso Λ f g) (directImageCompIso f g).symm
    (moduleInverseImageAdjunction f Λ) (inverseImageAdjunction f)
    (moduleInverseImageAdjunction g Λ) (inverseImageAdjunction g)
    (moduleInverseImageAdjunction (g ≫ f) Λ) (inverseImageAdjunction (g ≫ f))
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ f g)
    (conjugateEquiv_inverseImageComp_hom f g) _ M
  intro N
  change (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map
      ((moduleDirectImageCompIso Λ f g).hom.app N) ≫
    ((mateEquiv (moduleInverseImageAdjunction f Λ) (inverseImageAdjunction f)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ f).inv)).natTrans).app
        ((moduleDirectImage g Λ).obj N) ≫
    (directImage f).map
      (((mateEquiv (moduleInverseImageAdjunction g Λ) (inverseImageAdjunction g)
        (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ g).inv)).natTrans).app N) =
    ((mateEquiv (moduleInverseImageAdjunction (g ≫ f) Λ)
      (inverseImageAdjunction (g ≫ f))
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ (g ≫ f)).inv)).natTrans).app N ≫
      (directImageCompIso f g).inv.app
        ((SheafOfModules.toSheaf.{u + 1} (constantRing T Λ)).obj N)
  rw [congr_app (mate_moduleInverseImageUnderlyingIso_inv (Λ := Λ) (f := f))
      ((moduleDirectImage g Λ).obj N),
    congr_app (mate_moduleInverseImageUnderlyingIso_inv (Λ := Λ) (f := g)) N,
    congr_app (mate_moduleInverseImageUnderlyingIso_inv (Λ := Λ) (f := g ≫ f)) N]
  let a := (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map
    ((moduleDirectImageCompIso Λ f g).hom.app N)
  let b := (directImageCompIso f g).inv.app
    ((SheafOfModules.toSheaf.{u + 1} (constantRing T Λ)).obj N)
  let Z := (moduleDirectImage g Λ ⋙
    SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)).obj N
  change a ≫ 𝟙 ((directImage f).obj Z) ≫ (directImage f).map (𝟙 Z) = 𝟙 _ ≫ b
  exact (congrArg (fun z => a ≫ 𝟙 _ ≫ z) ((directImage f).map_id Z)).trans
    ((congrArg (fun z => a ≫ z) (Category.id_comp (𝟙 ((directImage f).obj Z)))).trans
      ((Category.comp_id a).trans ((moduleDirectImageCompIso_hom_underlying Λ f g N).trans
        (Category.id_comp b).symm)))

/-- Equality transport of base maps commutes with the specified scalar-forgetting
inverse comparison. -/
@[reassoc]
theorem moduleInverseImageUnderlyingIso_inv_eqToHom {X S : Scheme.{u}}
    {f g : S ⟶ X} (h : f = g) (M : ModuleSheaf X Λ) :
    eqToHom (congrArg (fun k => (inverseImage k).obj
        ((SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).obj M)) h) ≫
      (moduleInverseImageUnderlyingIso Λ g).inv.app M =
    (moduleInverseImageUnderlyingIso Λ f).inv.app M ≫
      (SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)).map
        (eqToHom (congrArg (fun k => (moduleInverseImage k Λ).obj M) h)) := by
  subst g
  simp

/-- Equality transport at the whole-functor level retains the original scalar
comparison before either natural isomorphism is evaluated. -/
theorem moduleInverseImageUnderlyingIso_inv_eqToIso_app {X S : Scheme.{u}}
    {f g : S ⟶ X} (h : f = g) (M : ModuleSheaf X Λ) :
    (eqToIso (congrArg (fun k : S ⟶ X => inverseImage k) h)).hom.app
        ((SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).obj M) ≫
      (moduleInverseImageUnderlyingIso Λ g).inv.app M =
    (moduleInverseImageUnderlyingIso Λ f).inv.app M ≫
      (SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)).map
        ((eqToIso (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) h)).hom.app M) := by
  subst g
  let a := (moduleInverseImageUnderlyingIso Λ f).inv.app M
  let U := SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)
  change 𝟙 _ ≫ a = a ≫ U.map (𝟙 ((moduleInverseImage f Λ).obj M))
  exact (Category.id_comp a).trans
    ((congrArg (fun z => a ≫ z) (U.map_id ((moduleInverseImage f Λ).obj M))).trans
      (Category.comp_id a)).symm

private theorem module_inverse_square_whole {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    moduleInverseImageSquareIso Λ f f' g g' h =
      (moduleInverseImageCompIso Λ g f').symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ S => moduleInverseImage k Λ) h) ≪≫
          moduleInverseImageCompIso Λ f g' := rfl

/-- The original native composition equation, retained behind its literal predicate. -/
private theorem module_inverse_composition_equation {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    Functor.ComparisonCompositionEquation
      (moduleInverseImageUnderlyingIso Λ f) (moduleInverseImageUnderlyingIso Λ g)
      (moduleInverseImageUnderlyingIso Λ (g ≫ f))
      (moduleInverseImageCompIso Λ f g) (inverseImageComp f g) :=
  moduleInverseImageUnderlyingIso_inv_comp Λ f g

/-- The original equality transport, retained behind its literal predicate. -/
private theorem module_inverse_transport_equation {X S : Scheme.{u}}
    {f g : S ⟶ X} (h : f = g) :
    Functor.ComparisonTransportEquation
      (moduleInverseImageUnderlyingIso Λ f) (moduleInverseImageUnderlyingIso Λ g)
      (eqToIso (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) h))
      (eqToIso (congrArg (fun k : S ⟶ X => inverseImage k) h)) :=
  moduleInverseImageUnderlyingIso_inv_eqToIso_app Λ h

/-- The original native and abelian source squares commute as whole natural
isomorphism chains, retaining all four specified scalar comparisons and the
original base-map equality. No proper-base-change hypothesis is used. -/
theorem moduleInverseImageSquareIso_underlying_whole {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    Functor.ComparisonCubeEquation
      (moduleInverseImageUnderlyingIso Λ f) (moduleInverseImageUnderlyingIso Λ f')
      (moduleInverseImageUnderlyingIso Λ g) (moduleInverseImageUnderlyingIso Λ g')
      (moduleInverseImageSquareIso Λ f f' g g' h) (inverseImageSquareIso f f' g g' h) := by
  exact Functor.comparisonCubeEquation_of_composition
    (A := ModuleSheaf S Λ) (B := ModuleSheaf X Λ)
    (C := ModuleSheaf S' Λ) (D := ModuleSheaf X' Λ)
    (A' := AbelianSheaf.{u, u + 1} S) (B' := AbelianSheaf.{u, u + 1} X)
    (C' := AbelianSheaf.{u, u + 1} S') (D' := AbelianSheaf.{u, u + 1} X')
    (L := moduleInverseImage f Λ) (L' := moduleInverseImage f' Λ)
    (G := moduleInverseImage g Λ) (H := moduleInverseImage g' Λ)
    (K := inverseImage f) (K' := inverseImage f')
    (G' := inverseImage g) (H' := inverseImage g')
    (QA := SheafOfModules.toSheaf.{u + 1} (constantRing S Λ))
    (QB := SheafOfModules.toSheaf.{u + 1} (constantRing X Λ))
    (QC := SheafOfModules.toSheaf.{u + 1} (constantRing S' Λ))
    (QD := SheafOfModules.toSheaf.{u + 1} (constantRing X' Λ))
    (L₀ := moduleInverseImage (f' ≫ g) Λ) (L₁ := moduleInverseImage (g' ≫ f) Λ)
    (K₀ := inverseImage (f' ≫ g)) (K₁ := inverseImage (g' ≫ f))
    (moduleInverseImageUnderlyingIso Λ f) (moduleInverseImageUnderlyingIso Λ f')
    (moduleInverseImageUnderlyingIso Λ g) (moduleInverseImageUnderlyingIso Λ g')
    (moduleInverseImageUnderlyingIso Λ (f' ≫ g))
    (moduleInverseImageUnderlyingIso Λ (g' ≫ f))
    (moduleInverseImageCompIso Λ g f') (moduleInverseImageCompIso Λ f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => moduleInverseImage k Λ) h))
    (inverseImageComp g f') (inverseImageComp f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h))
    (moduleInverseImageSquareIso Λ f f' g g' h) (inverseImageSquareIso f f' g g' h)
    (module_inverse_square_whole Λ f f' g g' h)
    (inverseImageSquareIso_eq_comp f f' g g' h)
    (module_inverse_composition_equation Λ g f')
    (module_inverse_composition_equation Λ f g')
    (module_inverse_transport_equation Λ h)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
