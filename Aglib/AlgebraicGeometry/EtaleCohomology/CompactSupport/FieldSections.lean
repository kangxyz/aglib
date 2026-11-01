/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.GlobalSectionsUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FieldTerminal
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology

/-! # Actual module sections over a separably closed field

The terminal germ is a module morphism in the original point-fibre colimit.
The initial pointed terminal object proves it invertible, not merely invertible
on underlying groups. This identifies module sections with the exact point functor.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wS wΛ

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  (Λ : Type (u + 1)) [CommRing Λ]

/-- The original terminal germ of a module-valued presheaf is an isomorphism. -/
theorem moduleFieldTerminalGerm_isIso
    (P : (Spec (.of Ω)).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber (A := ModuleCat.{u + 1} Λ)
      (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω) P) :=
  isIso_ι_of_isTerminal (fieldTerminalPointIsInitial Ω).op
    ((Functor.Elements.π (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber).op ⋙ P)

/-- The original module-linear terminal germs compare actual sections and point fibres. -/
def moduleFieldSectionsFiberIso :
    moduleGlobalSections (Spec (.of Ω)) Λ ≅
      (moduleSheafEquivalence (Spec (.of Ω)) Λ).inverse ⋙
        (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := ModuleCat.{u + 1} Λ) := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let F := (moduleSheafEquivalence (Spec (.of Ω)) Λ).inverse.obj M
    exact @asIso (ModuleCat.{u + 1} Λ) _ _ _
      ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (A := ModuleCat.{u + 1} Λ) (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω) F.obj)
      (moduleFieldTerminalGerm_isIso Ω Λ F.obj)
  · intro M N φ
    exact ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber_naturality
      (A := ModuleCat.{u + 1} Λ)
      ((moduleSheafEquivalence (Spec (.of Ω)) Λ).inverse.map φ).hom
      (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω)).symm

/-- Actual module sections over a separably closed field are right exact. -/
instance moduleFieldGlobalSections_preservesFiniteColimits :
    PreservesFiniteColimits (moduleGlobalSections (Spec (.of Ω)) Λ) := by
  let : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  let : PreservesFiniteColimits
      ((pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
        (A := ModuleCat.{u + 1} Λ)) := inferInstance
  exact preservesFiniteColimits_of_natIso (moduleFieldSectionsFiberIso Ω Λ).symm

/-- The actual native derived sections commute with native homology over this field. -/
def moduleFieldDerivedGlobalSectionsHomologyIso
    [HasDerivedCategory.{wS} (ModuleSheaf (Spec (.of Ω)) Λ)]
    [HasDerivedCategory.{wΛ} (ModuleCat.{u + 1} Λ)] (q : ℤ) :
    moduleDerivedGlobalSections (Spec (.of Ω)) Λ ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q ≅
      DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Spec (.of Ω)) Λ) q ⋙
        moduleGlobalSections (Spec (.of Ω)) Λ :=
  Functor.rightDerivedFunctorPlusHomologyIso (moduleGlobalSections (Spec (.of Ω)) Λ) q

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
