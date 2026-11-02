/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.IdentityAmbientOpenComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionTotal

/-! # The original total refinement retains both literal source and proper-arrow transports -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wW wT
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
  (T : Hom.TripleCompactifiedComposition f g h) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hW : HasDerivedCategory.{wW} (ModuleSheaf W Λ)]
  [hT : HasDerivedCategory.{wT} (ModuleSheaf T.first.Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf T.leftOuter.composite.Xbar Λ`. -/
local instance : HasDerivedCategory.{wT} (ModuleSheaf T.leftOuter.composite.Xbar Λ) := hT
/-- The local derived-category model on `ModuleSheaf T.rightTotalTransport.Xbar Λ`. -/
local instance : HasDerivedCategory.{wT} (ModuleSheaf T.rightTotalTransport.Xbar Λ) := hT

local instance : IsOpenImmersion
    (show X ⟶ T.first.Xbar from T.leftOuter.composite.j) :=
  inferInstanceAs (IsOpenImmersion T.first.j)
local instance : IsOpenImmersion
    (show X ⟶ T.first.Xbar from T.rightTotalTransport.j) :=
  inferInstanceAs (IsOpenImmersion ((𝟙 X) ≫ T.first.j))

omit [QuasiCompact f] [QuasiCompact g] [QuasiCompact h] in
/-- The transported source retains its literal identity composite. -/
theorem tripleTotalOpenEquality : T.rightTotalTransport.j = T.leftOuter.composite.j :=
  Category.id_comp T.first.j

omit [QuasiCompact f] [QuasiCompact g] [QuasiCompact h] in
/-- The total proper arrows differ by exactly the original scheme associativity. -/
theorem tripleTotalProperEquality : T.rightTotalTransport.p = T.leftOuter.composite.p :=
  (Category.assoc T.first.p T.middle.p T.last.p).symm

/-- With a single supplied top model, the actual total map has precisely these two transports. -/
theorem moduleTripleTotalImageComparison :
    CategoryTheory.imageComparison (moduleDerivedRefinementComparison T.totalRefinement Λ)
      (moduleDerivedRefinementDirectImageIso Λ T.totalRefinement) =
    Functor.whiskerRight
        (eqToHom (@moduleDerivedLowerShriek_congr Λ _ T.first.Xbar X
          T.rightTotalTransport.j T.leftOuter.composite.j
          (inferInstanceAs (Etale ((𝟙 X) ≫ T.first.j)))
          (inferInstanceAs (Etale T.first.j)) hT hX (tripleTotalOpenEquality T)))
        (moduleDerivedDirectImage Λ T.rightTotalTransport.p) ≫
      Functor.whiskerLeft (moduleDerivedLowerShriek T.leftOuter.composite.j Λ)
        (eqToHom (congrArg (fun p : T.first.Xbar ⟶ W => moduleDerivedDirectImage Λ p)
          (tripleTotalProperEquality T))) :=
  moduleRawImageComparison_identity_eq_both Λ (X := X) (Y := T.first.Xbar) (S := W)
    T.leftOuter.composite.j T.rightTotalTransport.j
    (Hom.DenseCompactification.isPullback_open T.totalRefinement)
    (tripleTotalOpenEquality T) T.leftOuter.composite.p T.rightTotalTransport.p
    (tripleTotalProperEquality T)

/-- Restriction is the original mixed transition, not an isomorphic replacement. -/
theorem moduleTripleTotalMixedComparison :
    @moduleCompactificationMixedTransition X W ((f ≫ g) ≫ h) _ Λ _ hX hW
        T.leftOuter.composite T.rightTotalTransport T.totalRefinement hT hT =
    Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
      (Functor.whiskerRight
          (eqToHom (@moduleDerivedLowerShriek_congr Λ _ T.first.Xbar X
          T.rightTotalTransport.j T.leftOuter.composite.j
          (inferInstanceAs (Etale ((𝟙 X) ≫ T.first.j)))
          (inferInstanceAs (Etale T.first.j)) hT hX (tripleTotalOpenEquality T)))
          (moduleDerivedDirectImage Λ T.rightTotalTransport.p) ≫
        Functor.whiskerLeft (moduleDerivedLowerShriek T.leftOuter.composite.j Λ)
          (eqToHom (congrArg (fun p : T.first.Xbar ⟶ W => moduleDerivedDirectImage Λ p)
            (tripleTotalProperEquality T)))) :=
  congrArg (Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι)
    (moduleTripleTotalImageComparison T Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
