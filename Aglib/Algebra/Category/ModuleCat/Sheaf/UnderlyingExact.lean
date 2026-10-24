/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Exact forgetting for native constant-ring module sheaves

The literal underlying-abelian functor preserves finite limits by the native
presheaf inclusion and finite colimits by the native sheafification comparison
and counit. The scalar-ring and module-value universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf

universe u v r

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R] [HasSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] hasSheafify forget_preservesSheafification

/-- Forgetting the actual module-sheaf action preserves finite limits. -/
instance underlying_preservesFiniteLimits : PreservesFiniteLimits (underlying R J) := by
  let U : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{max u v} := forget₂ _ _
  let : PreservesLimitsOfSize.{0, 0} U :=
    ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{0, 0, max u v, r}
  let : PreservesFiniteLimits U := PreservesLimitsOfSize0.preservesFiniteLimits U
  refine ⟨fun I _ _ => ?_⟩
  let W := (Functor.whiskeringRight Cᵒᵖ
    (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).obj U
  let : PreservesLimitsOfShape I W := whiskeringRight_preservesLimitsOfShape U
  let : PreservesLimitsOfShape I
      (underlying R J ⋙ sheafToPresheaf J AddCommGrpCat.{max u v}) := by
    change PreservesLimitsOfShape I (sheafToPresheaf J (ModuleCat.{max u v} R) ⋙ W)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (underlying R J) (sheafToPresheaf J AddCommGrpCat.{max u v})

/-- Forgetting the actual module-sheaf action preserves finite colimits.
The proof uses the original sheafification comparison and its original counit. -/
instance underlying_preservesFiniteColimits : PreservesFiniteColimits (underlying R J) := by
  let U : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{max u v} := forget₂ _ _
  let : PreservesColimitsOfSize.{0, 0} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max u v, r, 0, 0} R
  let : PreservesFiniteColimits U := PreservesColimitsOfSize0.preservesFiniteColimits U
  refine ⟨fun I _ _ => ?_⟩
  refine ⟨fun {F} => ?_⟩
  let L := presheafToSheaf J (ModuleCat.{max u v} R)
  let G := underlying R J
  let P := F ⋙ sheafToPresheaf J (ModuleCat.{max u v} R)
  let e := sheafComposeNatIso J U
    (sheafificationAdjunction J (ModuleCat.{max u v} R))
    (sheafificationAdjunction J AddCommGrpCat.{max u v})
  let : PreservesColimit P (L ⋙ G) := preservesColimit_of_natIso P e
  let h := isColimitOfPreserves L (colimit.isColimit P)
  let : PreservesColimit (P ⋙ L) G :=
    preservesColimit_of_preserves_colimit_cocone h
      (isColimitOfPreserves (L ⋙ G) (colimit.isColimit P))
  let c : P ⋙ L ≅ F := Functor.isoWhiskerLeft F
    (asIso (sheafificationAdjunction J (ModuleCat.{max u v} R)).counit)
  exact preservesColimit_of_iso_diagram G c

end ModuleCat.Sheaf
