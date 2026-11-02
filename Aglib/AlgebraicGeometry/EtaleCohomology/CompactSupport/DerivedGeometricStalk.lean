/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.GeometricStalk

/-! # Native homology at a geometric point

Exact native inverse image and exact module sections over a separably closed
field identify the original homology stalk with the homology of actual derived
sections of the actual derived pullback.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wS wΩ wΛ

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S) (Λ : Type (u + 1)) [CommRing Λ]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wΩ} (ModuleSheaf (Spec (.of Ω)) Λ)]
  [HasDerivedCategory.{wΛ} (ModuleCat.{u + 1} Λ)]

/-- The original module stalk/homology comparison through exact field sections. -/
def moduleGeometricStalkHomologyIso (q : ℤ) :
    DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) q ⋙ moduleGeometricStalk Λ s ≅
      moduleDerivedInverseImage Λ s ⋙ moduleDerivedGlobalSections (Spec (.of Ω)) Λ ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) q)
      (moduleGeometricStalkSectionsIso Λ s) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusHomologyIso (moduleInverseImage s Λ) q).symm
      (moduleGlobalSections (Spec (.of Ω)) Λ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleDerivedInverseImage Λ s)
      (moduleFieldDerivedGlobalSectionsHomologyIso Ω Λ q).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
