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
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnderlyingComposition

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

open CategoryTheory.TorsionZMod.Ringed

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  moduleForget_preservesSheafification moduleForget_preservesLeftKanExtensions
  hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The forward native direct-image comparison retains the inverse original abelian
direct-image comparison. -/
theorem moduleDirectImageCompIso_hom_underlying {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (M : ModuleSheaf T Λ) :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map
        ((moduleDirectImageCompIso Λ f g).hom.app M) =
      (directImageCompIso f g).inv.app
        ((SheafOfModules.toSheaf.{u + 1} (constantRing T Λ)).obj M) :=
  ModuleCat.Sheaf.ConstantRing.moduleDirectImageCompIso_hom_underlying
    (siteBaseChange f) (siteBaseChange g) (siteBaseChange (g ≫ f))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (Scheme.smallEtaleTopology T) Λ (siteBaseChangeComp f g).symm M

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
        ((moduleInverseImageCompIso Λ f g).hom.app M) :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImageUnderlyingIso_inv_comp
    (siteBaseChange f) (siteBaseChange g) (siteBaseChange (g ≫ f))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (Scheme.smallEtaleTopology T) Λ (siteBaseChangeComp f g).symm (inverseImageComp f g)
    (conjugateEquiv_inverseImageComp_hom f g) M

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
  simpa only [eqToIso.hom, eqToHom_app] using
    Functor.comparisonTransportEquation_eqToIso
      (fun k : S ⟶ X => moduleInverseImage k Λ) (fun k : S ⟶ X => inverseImage k)
      (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ))
      (SheafOfModules.toSheaf.{u + 1} (constantRing S Λ))
      (fun k => moduleInverseImageUnderlyingIso Λ k) h M

/-- Equality transport at the whole-functor level retains the original scalar
comparison before either natural isomorphism is evaluated. -/
theorem moduleInverseImageUnderlyingIso_inv_eqToIso_app {X S : Scheme.{u}}
    {f g : S ⟶ X} (h : f = g) (M : ModuleSheaf X Λ) :
    (eqToIso (congrArg (fun k : S ⟶ X => inverseImage k) h)).hom.app
        ((SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).obj M) ≫
      (moduleInverseImageUnderlyingIso Λ g).inv.app M =
    (moduleInverseImageUnderlyingIso Λ f).inv.app M ≫
      (SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)).map
        ((eqToIso (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) h)).hom.app M) :=
  Functor.comparisonTransportEquation_eqToIso
    (fun k : S ⟶ X => moduleInverseImage k Λ) (fun k : S ⟶ X => inverseImage k)
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ))
    (SheafOfModules.toSheaf.{u + 1} (constantRing S Λ))
    (fun k => moduleInverseImageUnderlyingIso Λ k) h M

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
