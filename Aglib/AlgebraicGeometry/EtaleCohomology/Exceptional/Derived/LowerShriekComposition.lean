/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons
public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonBranches

/-! # The original exact lower-shriek identity and composition

These comparisons derive the original ordinary adjoint-uniqueness maps. Their
mates are the independently installed inverse-image comparisons, not newly
chosen isomorphisms between the same endpoints.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wT wV

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original lower-shriek identity has the original inverse-image mate. -/
theorem conjugateEquiv_moduleLowerShriekIdIso_hom (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id (moduleLowerShriekAdjunction (𝟙 X) Λ)
      (moduleLowerShriekIdIso Λ X).hom = (moduleInverseImageIdIso Λ X).inv :=
  conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (moduleLowerShriekAdjunction (𝟙 X) Λ) Adjunction.id (moduleInverseImageIdIso Λ X)

/-- The original lower-shriek compositor has the original inverse-image mate. -/
theorem conjugateEquiv_moduleLowerShriekCompIso_hom {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g] :
    conjugateEquiv ((moduleLowerShriekAdjunction g Λ).comp
        (moduleLowerShriekAdjunction f Λ)) (moduleLowerShriekAdjunction (g ≫ f) Λ)
      (moduleLowerShriekCompIso Λ f g).hom = (moduleInverseImageCompIso Λ f g).inv :=
  conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (moduleLowerShriekAdjunction (g ≫ f) Λ)
    ((moduleLowerShriekAdjunction g Λ).comp (moduleLowerShriekAdjunction f Λ))
    (moduleInverseImageCompIso Λ f g)

/-- Native deriving of the exact original identity. -/
def moduleDerivedLowerShriekIdIso (X : Scheme.{u})
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    moduleDerivedLowerShriek (𝟙 X) Λ ≅ 𝟭 (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  (moduleLowerShriek (𝟙 X) Λ).rightDerivedFunctorPlusIso (moduleLowerShriekIdIso Λ X) ≪≫
    Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf X Λ)

/-- Native deriving of the exact original compositor, with independent models. -/
def moduleDerivedLowerShriekCompIso {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)] :
    moduleDerivedLowerShriek (g ≫ f) Λ ≅
      moduleDerivedLowerShriek g Λ ⋙ moduleDerivedLowerShriek f Λ :=
  (moduleLowerShriek (g ≫ f) Λ).rightDerivedFunctorPlusIso
      (moduleLowerShriekCompIso Λ f g) ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
      (moduleLowerShriek g Λ) (moduleLowerShriek f Λ)

/-- The installed identity retains its original derived adjunction mate. -/
theorem conjugateEquiv_moduleDerivedLowerShriekIdIso_hom (X : Scheme.{u})
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    conjugateEquiv Adjunction.id (moduleDerivedLowerShriekAdjunction (𝟙 X) Λ)
      (moduleDerivedLowerShriekIdIso Λ X).hom = (moduleDerivedInverseImageIdIso Λ X).inv :=
  (moduleLowerShriekAdjunction (𝟙 X) Λ).rightDerivedFunctorPlus_conjugate_id
    (moduleLowerShriekIdIso Λ X) (moduleInverseImageIdIso Λ X)
    (conjugateEquiv_moduleLowerShriekIdIso_hom Λ X)

/-- The installed compositor retains its original derived adjunction mate. -/
theorem conjugateEquiv_moduleDerivedLowerShriekCompIso_hom {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)] :
    conjugateEquiv ((moduleDerivedLowerShriekAdjunction g Λ).comp
        (moduleDerivedLowerShriekAdjunction f Λ)) (moduleDerivedLowerShriekAdjunction (g ≫ f) Λ)
      (moduleDerivedLowerShriekCompIso Λ f g).hom =
        (moduleDerivedInverseImageCompIso Λ f g).inv := by
  let : (moduleInverseImage f Λ).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (moduleLowerShriekAdjunction f Λ)
  have h := Adjunction.rightDerivedFunctorPlus_conjugate_comp
    (moduleLowerShriekAdjunction g Λ) (moduleLowerShriekAdjunction f Λ)
    (moduleLowerShriekAdjunction (g ≫ f) Λ)
    (moduleLowerShriekCompIso Λ f g) (moduleInverseImageCompIso Λ f g).symm
    (conjugateEquiv_moduleLowerShriekCompIso_hom Λ f g)
  simpa only [moduleDerivedLowerShriekAdjunction, moduleDerivedLowerShriekCompIso,
    moduleDerivedInverseImageCompIso, Iso.symm_symm_eq,
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_eq_ofPreservesInjectives] using h

/-- Equality of étale maps transports the original functor, including its instance. -/
theorem moduleLowerShriek_congr {X S : Scheme.{u}} {f g : S ⟶ X}
    [Etale f] [Etale g] (h : f = g) : moduleLowerShriek f Λ = moduleLowerShriek g Λ := by
  subst g
  rfl

/-- Equality of étale maps transports the installed exact derived functor. -/
theorem moduleDerivedLowerShriek_congr {X S : Scheme.{u}} {f g : S ⟶ X}
    [Etale f] [Etale g]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] (h : f = g) :
    moduleDerivedLowerShriek f Λ = moduleDerivedLowerShriek g Λ := by
  subst g
  rfl


end AlgebraicGeometry.Scheme.EtaleCohomology
