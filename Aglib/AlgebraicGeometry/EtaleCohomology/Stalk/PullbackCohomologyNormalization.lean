/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackLimitCoefficient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyCocone

/-! # Original fixed-coefficient cohomology comparison legs -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e uI vI
attribute [local instance] hasSheafifyLarge
open Continuity

variable {I : Type uI} [Category.{vI} I] (Y : I ⥤ Scheme.{u}ᵒᵖ)
  (b : Cone Y) (c : Cocone Y) (l : b.pt ⟶ c.pt)
  (hl : ∀ i, b.π.app i ≫ c.ι.app i = l)
  (F : AbelianSheaf.{u, u + 1} b.pt.unop)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (Y.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [IsConnected I]
  [HasColimit (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F))]

/-- Transporting the actual compatible-system leg recovers the original structural pullback. -/
theorem diagramCohomologyLeg_pullbackLimitCoefficientIso (n : ℕ) (i : I) :
    diagramCohomologyLeg Y c (pullbackCoefficientSystem Y b F) n i ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (pullbackLimitCoefficientIso Y b c l hl F).hom n) =
      cohomologyTransfer (X := (Y.obj i).unop) (Y := c.pt.unop) (c.ι.app i).unop
        ((pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
          (congrArg Quiver.Hom.unop (hl i))).inv.app F) n := by
  apply ConcreteCategory.ext_apply
  intro x
  change Sheaf.H.map (pullbackLimitCoefficientIso Y b c l hl F).hom n
      (Sheaf.H.map
        (colimit.ι (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)) i) n
        (cohomologyPullback (X := (Y.obj i).unop) (S := c.pt.unop)
          (c.ι.app i).unop _ n x)) = _
  let z : Sheaf.H.{e}
      ((coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)).obj i) n :=
    cohomologyPullback (X := (Y.obj i).unop) (S := c.pt.unop)
      (c.ι.app i).unop ((pullbackCoefficientSystem Y b F).obj i) n x
  exact (Sheaf.H.map_comp_apply
    (colimit.ι (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)) i)
    (pullbackLimitCoefficientIso Y b c l hl F).hom z).symm.trans
      (congrArg
        (fun t : (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)).obj i ⟶
          (inverseImage l.unop).obj F => Sheaf.H.map t n z)
        (ι_pullbackLimitCoefficientIso_hom Y b c l hl F i))

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
