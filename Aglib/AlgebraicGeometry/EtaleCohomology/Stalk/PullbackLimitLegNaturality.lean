/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackLimitCohomologyLeg

/-! # Coefficient naturality of the original structural cohomology leg -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e uI vI
attribute [local instance] hasSheafifyLarge
open Continuity

variable {I : Type uI} [Category.{vI} I] (Y : I ⥤ Scheme.{u}ᵒᵖ)
  (b : Cone Y) (c : Cocone Y) (l : b.pt ⟶ c.pt)
  (hl : ∀ i, b.π.app i ≫ c.ι.app i = l)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (Y.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  {F G : AbelianSheaf.{u, u + 1} b.pt.unop} (g : F ⟶ G) (q : ℕ)

/-- The original structural leg commutes with the original inverse-image coefficient maps. -/
theorem pullbackLimitCohomologyLeg_naturality (i : I) :
    pullbackLimitCohomologyLeg Y b c l hl F q i ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((inverseImage l.unop).map g) q) =
      AddCommGrpCat.ofHom (Sheaf.H.map ((inverseImage (b.π.app i).unop).map g) q) ≫
        pullbackLimitCohomologyLeg Y b c l hl G q i :=
  cohomologyTransfer_naturality (X := (Y.obj i).unop) (Y := c.pt.unop)
    (c.ι.app i).unop
    ((pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
      (congrArg Quiver.Hom.unop (hl i))).inv.app F)
    ((pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
      (congrArg Quiver.Hom.unop (hl i))).inv.app G)
    ((inverseImage (b.π.app i).unop).map g) ((inverseImage l.unop).map g)
    ((pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
      (congrArg Quiver.Hom.unop (hl i))).inv.naturality g) q

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
