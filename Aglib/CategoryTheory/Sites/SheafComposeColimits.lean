/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Colimits under original coefficient composition

A coefficient functor preserving colimits and sheafification preserves the
same colimits on native sheaves. The proof uses the original sheafification
adjunction and its original coefficient comparison.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe c h a b v w i j

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    {A : Type a} [Category.{v} A] {B : Type b} [Category.{w} B]
    (U : A ⥤ B) [HasWeakSheafify J A] [HasWeakSheafify J B]
    [J.HasSheafCompose U] [J.PreservesSheafification U]
    {I : Type i} [Category.{j} I] [HasColimitsOfShape I A]
    [PreservesColimitsOfShape I U]

/-- Native coefficient composition preserves every colimit shape preserved
by its coefficient functor, provided that functor preserves sheafification. -/
theorem sheafCompose_preservesColimitsOfShape :
    PreservesColimitsOfShape I (sheafCompose J U) where
  preservesColimit {F} := by
    let L := presheafToSheaf J A
    let V := sheafCompose J U
    let P := F ⋙ sheafToPresheaf J A
    let : PreservesColimitsOfShape I (L ⋙ V) :=
      preservesColimitsOfShape_of_natIso
        (sheafComposeNatIso J U (sheafificationAdjunction J A)
          (sheafificationAdjunction J B))
    let : PreservesColimit (P ⋙ L) V :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit P))
        (isColimitOfPreserves (L ⋙ V) (colimit.isColimit P))
    exact preservesColimit_of_iso_diagram V
      ((Functor.associator F (sheafToPresheaf J A) L) ≪≫
        Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J A).counit) ≪≫
          F.rightUnitor)

end CategoryTheory
