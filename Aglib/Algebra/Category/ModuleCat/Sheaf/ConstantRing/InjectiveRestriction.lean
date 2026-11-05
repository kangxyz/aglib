/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InjectiveRestriction
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Original section extension for genuine constant-ring injectives

The native coefficient equivalence transfers genuine injectivity to the
unchanged module-valued coefficient. Its original underlying comparison then
transfers the restriction epimorphism back to the original ringed coefficient.
The underlying abelian sheaf is not asserted to be injective.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf.ConstantRing

universe c h r t

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R] [HasWeakSheafify J RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}]
  [HasSheafify J (ModuleCat.{max c h r t} R)]
  [HasWeakSheafify J AddCommGrpCat.{max c h r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r t}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max c h r t} R)
    AddCommGrpCat.{max c h r t})]

/-- Restriction of the original underlying sheaf of a genuine ringed injective
is epic along every original monomorphism of site objects. -/
theorem underlying_restriction_epi_of_injective
    (I : ModuleSheaf.{c, h, r, max c h r t} J R) [Injective I]
    {U V : C} (f : U ⟶ V) [Mono f] :
    Epi (((SheafOfModules.toSheaf (constantRing J R)).obj I).obj.map f.op) := by
  let E := moduleSheafEquivalence.{c, h, r, max c h r t} J R
  let K := E.inverse.obj I
  have : Injective K := inferInstance
  have : Epi (K.obj.map f.op) :=
    ModuleCat.Sheaf.restriction_epi_of_injective J R K f
  let A := sheafCompose J
    (forget₂ (ModuleCat.{max c h r t} R) AddCommGrpCat.{max c h r t})
  let e : A.obj K ≅ (SheafOfModules.toSheaf (constantRing J R)).obj I :=
    (moduleSheafUnderlyingIso J R).symm.app K ≪≫
      (SheafOfModules.toSheaf (constantRing J R)).mapIso (E.counitIso.app I)
  have : Epi ((A.obj K).obj.map f.op) :=
    inferInstanceAs (Epi ((forget₂ (ModuleCat.{max c h r t} R)
      AddCommGrpCat.{max c h r t}).map (K.obj.map f.op)))
  have : Epi ((A.obj K).obj.map f.op ≫ e.hom.hom.app (op U)) := inferInstance
  exact epi_of_epi_fac (e.hom.hom.naturality f.op).symm

end ModuleCat.Sheaf.ConstantRing
