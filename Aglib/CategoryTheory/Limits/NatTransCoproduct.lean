/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Invertible natural-transformation components on coproducts

The comparison is proved using the original mapped coproduct injections. No replacement
component or chosen natural isomorphism is assumed.
-/

/-!
Source: `Quillen/CategoryTheory/Limits/NatTransCoproduct.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 38]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
universe v u v' u' w
open CategoryTheory.Limits
namespace CategoryTheory.NatTrans
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
/-- A transformation between coproduct-preserving functors is invertible on a coproduct
when its original components on all summands are invertible. -/
theorem isIso_app_coproduct (F G : C ⥤ D) (α : F ⟶ G)
    {I : Type w} (f : I → C) [HasCoproduct f]
    [PreservesColimitsOfShape (Discrete I) F] [PreservesColimitsOfShape (Discrete I) G]
    [∀ i, IsIso (α.app (f i))] : IsIso (α.app (∐ f)) := by
  let hF := isColimitOfPreserves F (coproductIsCoproduct f)
  let hG := isColimitOfPreserves G (coproductIsCoproduct f)
  let e := hF.coconePointsIsoOfNatIso hG
    (Discrete.natIso fun i => asIso (α.app (f i.as)))
  have h : α.app (∐ f) = e.hom := by
    apply hF.hom_ext
    intro i
    dsimp only [e]
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact α.naturality (Sigma.ι f i.as)
  rw [h]
  infer_instance
end CategoryTheory.NatTrans
