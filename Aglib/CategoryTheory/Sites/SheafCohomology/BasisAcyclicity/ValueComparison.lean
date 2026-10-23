/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.LiftedInjectives
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLiftZero

/-! # Original cohomology comparison across coefficient universes

The equivalence is defined from the actual exact-functor Ext map and the
constant-integer source map normalized by the universal section. Its proof uses
acyclic lifted small injectives, rather than preservation of injectives.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe e e' c h w t

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasSheafify J AddCommGrpCat.{max c h w}]
  [HasSheafify J AddCommGrpCat.{max c h w t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h w t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max c h w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{max c h w t})]
  [J.WEqualsLocallyBijective (Type (max c h w t))]
  [J.PreservesSheafification AddCommGrpCat.free.{max c h w t}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max c h w})]
  [HasExt.{e'} (Sheaf J AddCommGrpCat.{max c h w t})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max c h w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max c h w t})]
  (B : CoverBasis.{c, h, max c w} J) {T : C} (hT : IsTerminal T) (hBT : B.objects T)

include B hBT

/-- The original all-degree comparison is bijective. Covers remain small and
source and target Ext universes remain independent. -/
theorem valueLiftCohomologyMap_bijective
    (F : Sheaf J AddCommGrpCat.{max c h w}) (n : ℕ) :
    Function.Bijective (valueLiftCohomologyMap.{e, e', c, h, max c h w, t} hT F n) :=
  (valueLift.{c, h, max c h w, t} J).extPrecompMap_bijective_of_acyclic_injectives
    (valueLiftConstantMap.{c, h, max c h w, t} hT)
    (fun F => valueLiftCohomologyMap_zero_bijective.{e, e', c, h, max c h w, t} hT F)
    (fun I _ n => valueLift_injective_cohomology_subsingleton.{e', c, h, w, t}
      B I hT hBT n) F n

/-- The additive universe comparison whose forward map is the actual
exact-functor Ext comparison, with the original constant source. -/
def valueLiftCohomologyAddEquiv
    (F : Sheaf J AddCommGrpCat.{max c h w}) (n : ℕ) :
    Sheaf.H.{e} F n ≃+
      Sheaf.H.{e'} ((valueLift.{c, h, max c h w, t} J).obj F) n :=
  AddEquiv.ofBijective (valueLiftCohomologyMap.{e, e', c, h, max c h w, t} hT F n)
    (valueLiftCohomologyMap_bijective.{e, e', c, h, w, t} B hT hBT F n)

/-- The equivalence retains the original Ext map rather than choosing an
unrelated additive group isomorphism. -/
theorem valueLiftCohomologyAddEquiv_apply
    (F : Sheaf J AddCommGrpCat.{max c h w}) (n : ℕ) (x : Sheaf.H.{e} F n) :
    valueLiftCohomologyAddEquiv.{e, e', c, h, w, t} B hT hBT F n x =
      (Ext.mk₀ (valueLiftConstantMap.{c, h, max c h w, t} hT)).comp
        (x.mapExactFunctor (valueLift.{c, h, max c h w, t} J)) (Nat.zero_add n) := rfl

end CategoryTheory.Sheaf.BasisAcyclicity
