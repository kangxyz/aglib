/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeMate
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.NatTrans
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquare

/-!
# The original unbounded module base-change map

The exact original inverse-image square is localized on the native derived
categories. Its mate under the actual unbounded adjunctions is the base-change
map. No invertibility, properness or finite cohomological bound is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wX' wS'

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- Localization of the original square, with the native exact composition factors. -/
def moduleUnboundedDerivedInverseImageSquareIso :
    moduleUnboundedDerivedInverseImage Λ g ⋙ moduleUnboundedDerivedInverseImage Λ f' ≅
      moduleUnboundedDerivedInverseImage Λ f ⋙ moduleUnboundedDerivedInverseImage Λ g' :=
  Functor.mapDerivedCategorySquareIso
    (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
    (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
    (moduleInverseImageSquareIso Λ f f' g g' h)

/-- The generic constructor retains the literal original localization chain. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_eq_original :
    moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h =
      Functor.mapDerivedCategoryCompIso (moduleInverseImage g Λ) (moduleInverseImage f' Λ) ≪≫
        Localization.liftNatIso DerivedCategory.Q
          (HomologicalComplex.quasiIso (ModuleSheaf S Λ) (ComplexShape.up ℤ)) _ _ _ _
          (Functor.isoWhiskerRight
            (NatIso.mapHomologicalComplex (moduleInverseImageSquareIso Λ f f' g g' h) (.up ℤ))
            DerivedCategory.Q) ≪≫
        (Functor.mapDerivedCategoryCompIso
          (moduleInverseImage f Λ) (moduleInverseImage g' Λ)).symm := rfl

/-- The actual unbounded exchange is the mate under the original derived adjunctions. -/
def moduleUnboundedDerivedBaseChangeMap :
    moduleUnboundedDerivedDirectImage Λ f ⋙ moduleUnboundedDerivedInverseImage Λ g ⟶
      moduleUnboundedDerivedInverseImage Λ g' ⋙ moduleUnboundedDerivedDirectImage Λ f' :=
  (mateEquiv (moduleUnboundedDerivedAdjunction Λ f) (moduleUnboundedDerivedAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom)).natTrans

/-- The actual unbounded component retains the original derived unit and counit. -/
theorem moduleUnboundedDerivedBaseChangeMap_app (K : DerivedCategory (ModuleSheaf X Λ)) :
    MateComponentEquation (moduleUnboundedDerivedAdjunction Λ f)
      (moduleUnboundedDerivedAdjunction Λ f')
      (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom K :=
  mateComponentEquation (moduleUnboundedDerivedAdjunction Λ f)
    (moduleUnboundedDerivedAdjunction Λ f') _ K

/-- The original adjoint equation characterizes this same unbounded exchange. -/
theorem eq_moduleUnboundedDerivedBaseChangeMap_iff
    (β : moduleUnboundedDerivedDirectImage Λ f ⋙ moduleUnboundedDerivedInverseImage Λ g ⟶
      moduleUnboundedDerivedInverseImage Λ g' ⋙ moduleUnboundedDerivedDirectImage Λ f') :
    β = moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h ↔
      ∀ K : DerivedCategory (ModuleSheaf X Λ),
        (moduleUnboundedDerivedInverseImage Λ f').map (β.app K) ≫
            (moduleUnboundedDerivedAdjunction Λ f').counit.app
              ((moduleUnboundedDerivedInverseImage Λ g').obj K) =
          (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom.app
              ((moduleUnboundedDerivedDirectImage Λ f).obj K) ≫
            (moduleUnboundedDerivedInverseImage Λ g').map
              ((moduleUnboundedDerivedAdjunction Λ f).counit.app K) :=
  eq_mateEquiv_iff (moduleUnboundedDerivedAdjunction Λ f)
    (moduleUnboundedDerivedAdjunction Λ f') _ β

end AlgebraicGeometry.Scheme.EtaleCohomology
