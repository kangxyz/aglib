/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeExchange
public import Aglib.AlgebraicGeometry.Compactification.BaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsion

/-!
# Original base change through a raw compactification

The map is the original proper exchange, followed by the derived image of the
original Cartesian lower-shriek comparison. Its components are invertible on
internal torsion cohomology. Literal pullback compactifications need not be
dense, and no quasi-compactness assumption on the new base is imposed here.
This is a comparison of specified compactification models, not yet the
refinement naturality or pasting theorem for the chosen exceptional functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wS wX' wY' wT

section Squares

variable {X Y S X' Y' T : Scheme.{u}}
  (j : X ⟶ Y) (p : Y ⟶ S) (j' : X' ⟶ Y') (p' : Y' ⟶ T)
  (a : X' ⟶ X) (c : Y' ⟶ Y) (b : T ⟶ S)
  [IsOpenImmersion j] [IsOpenImmersion j'] [IsProper p]
  (hj : IsPullback a j' j c) (hp : IsPullback c p' p b)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wY'} (ModuleSheaf Y' Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- The unchanged proper exchange followed by the original open-extension
comparison, with the literal composition associators. -/
def moduleCompactifiedBaseChangeMap :
    (moduleDerivedLowerShriek j Λ ⋙ moduleDerivedDirectImage Λ p) ⋙
        moduleDerivedInverseImage Λ b ⟶
      moduleDerivedInverseImage Λ a ⋙
        (moduleDerivedLowerShriek j' Λ ⋙ moduleDerivedDirectImage Λ p') :=
  compositeExchange (moduleDerivedBaseChangeMap Λ p p' b c hp.w.symm)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j c hj Λ)

omit [IsProper p] in
/-- The map is exactly the abstract pasting of the original two exchanges.
Its component formula is `compositeExchange_app`, before any concrete expansion. -/
theorem moduleCompactifiedBaseChangeMap_fac :
    moduleCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ =
      compositeExchange (moduleDerivedBaseChangeMap Λ p p' b c hp.w.symm)
        (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j c hj Λ) := rfl

private theorem compactifiedProperExchange_isIsoOn :
    NatTrans.IsIsoOn (moduleTorsionCohomologyPlus X Λ)
      (Functor.whiskerLeft (moduleDerivedLowerShriek j Λ)
        (moduleDerivedBaseChangeMap Λ p p' b c hp.w.symm)) := by
  exact fun K hK => Proper.properModuleDerivedBaseChange_isIso_of_torsion_homology
    Λ p p' b c hp ((moduleDerivedLowerShriek j Λ).obj K)
      (moduleDerivedLowerShriek_preservesTorsionCohomology j Λ hK)

/-- The original compactified exchange is invertible on the whole torsion property. -/
theorem compactifiedExchange_isIsoOn :
    NatTrans.IsIsoOn (moduleTorsionCohomologyPlus X Λ)
      (moduleCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ) :=
  compositeExchange_isIsoOn (moduleDerivedBaseChangeMap Λ p p' b c hp.w.symm)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j c hj Λ)
    (moduleTorsionCohomologyPlus X Λ)
    (compactifiedProperExchange_isIsoOn j p p' c b hp Λ)

/-- Actual proper base change makes the original compactified comparison
invertible precisely on the torsion-cohomology input range. -/
theorem moduleCompactifiedBaseChangeMap_isIso
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    IsIso ((moduleCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ).app K) :=
  compactifiedExchange_isIsoOn j p j' p' a c b hj hp Λ K hK

/-- Restricting only the source to its native torsion full subcategory turns the
original compactified comparison into a natural isomorphism. -/
def moduleCompactifiedBaseChangeIso :
    (moduleTorsionCohomologyPlus X Λ).ι ⋙
        ((moduleDerivedLowerShriek j Λ ⋙ moduleDerivedDirectImage Λ p) ⋙
          moduleDerivedInverseImage Λ b) ≅
      (moduleTorsionCohomologyPlus X Λ).ι ⋙
        (moduleDerivedInverseImage Λ a ⋙
          (moduleDerivedLowerShriek j' Λ ⋙ moduleDerivedDirectImage Λ p')) :=
  (moduleCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ).isoOn
    (moduleTorsionCohomologyPlus X Λ)
    (compactifiedExchange_isIsoOn j p j' p' a c b hj hp Λ)

/-- Restricting to torsion changes none of the original comparison transformation. -/
theorem moduleCompactifiedBaseChangeIso_hom :
    (moduleCompactifiedBaseChangeIso j p j' p' a c b hj hp Λ).hom =
      Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleCompactifiedBaseChangeMap j p j' p' a c b hj hp Λ) := rfl

end Squares

section Compactification

variable {X S T : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) (b : T ⟶ S)

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wY'} (ModuleSheaf (pullback b C.p) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Reuse the selected pullback realization for the literal base-changed compactification. -/
local instance : HasDerivedCategory.{wY'} (ModuleSheaf (C.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wY'} (ModuleSheaf (pullback b C.p) Λ))

/-- The specified raw compactification model on the native torsion input category. -/
def moduleRawCompactificationFunctor :
    (moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
      DerivedCategory.Plus (ModuleSheaf S Λ) :=
  (moduleTorsionCohomologyPlus X Λ).ι ⋙
    (moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p)

/-- Actual arbitrary base change for a specified raw compactification. The target
uses its literal pullback, without claiming that schematic density is preserved. -/
def moduleRawCompactificationBaseChangeIso :
    moduleRawCompactificationFunctor C Λ ⋙ moduleDerivedInverseImage Λ b ≅
      moduleDerivedInverseImageTorsion (pullback.snd b f) Λ ⋙
        moduleRawCompactificationFunctor (C.baseChange b) Λ :=
  Functor.associator _ _ _ ≪≫
    moduleCompactifiedBaseChangeIso C.j C.p (C.baseChange b).j
      (pullback.fst b C.p) (pullback.snd b f) (pullback.snd b C.p) b
      (isPullback_rawCompactificationOpen C b) (IsPullback.of_hasPullback b C.p).flip Λ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDerivedInverseImageTorsionForgetIso (pullback.snd b f) Λ).symm
      (moduleDerivedLowerShriek (C.baseChange b).j Λ ⋙
        moduleDerivedDirectImage Λ (pullback.fst b C.p)) ≪≫
    Functor.associator _ _ _

end Compactification

end AlgebraicGeometry.Scheme.EtaleCohomology
