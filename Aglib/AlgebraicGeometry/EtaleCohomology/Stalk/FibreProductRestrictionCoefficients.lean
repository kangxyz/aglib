/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductOriginalDiagram

/-! # Coefficient naturality of the original fibre-product restriction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u e e'

attribute [local instance] hasSheafifyLarge

section Restriction

variable {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Etale} (g : V ⟶ U)
  [hU : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hV : HasExt.{e'} (AbelianSheaf.{u, u + 1} (pullback V.hom f))]

local instance constantModulePresheafSource_hasExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) := hU
local instance constantModulePresheafTarget_hasExt : HasExt.{e'}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj V).left) := hV
local instance constantModulePresheafSourceIdentity_hasExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj ((siteBaseChange f).obj U).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hU
local instance constantModulePresheafTargetIdentity_hasExt : HasExt.{e'}
    (Sheaf ((𝟭 Scheme.{u}).obj ((siteBaseChange f).obj V).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hV

/-- The actual fibre-product restriction commutes with every original
coefficient morphism, before any resizing or passage to germs. -/
theorem fibreProductCohomologyRestriction_coefficientMap
    {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    fibreProductCohomologyRestriction f g G q
        (Sheaf.H.map ((inverseImage (pullback.snd U.hom f)).map a) q x) =
      Sheaf.H.map ((inverseImage (pullback.snd V.hom f)).map a) q
        (fibreProductCohomologyRestriction f g F q x) := by
  let k := ((siteBaseChange f).map g).left
  let t := (pullbackTriangleIso ((siteBaseChange f).obj V).hom
    ((siteBaseChange f).obj U).hom k
    (MorphismProperty.Over.w ((siteBaseChange f).map g))).inv
  change Sheaf.H.map.{e'} (t.app G) q
      (cohomologyPullback.{u, e, e'} k _ q
        (Sheaf.H.map.{e} ((inverseImage (pullback.snd U.hom f)).map a) q x)) =
    Sheaf.H.map.{e'} ((inverseImage (pullback.snd V.hom f)).map a) q
      (Sheaf.H.map.{e'} (t.app F) q (cohomologyPullback.{u, e, e'} k _ q x))
  have hpb := cohomologyPullback_coefficientMap.{u, e, e'} k
    ((inverseImage ((siteBaseChange f).obj U).hom).map a) q x
  have hfirst := congrArg (Sheaf.H.map.{e'} (t.app G) q) hpb
  have hlast := congrArg
    (fun z => Sheaf.H.map.{e'} z q
      (cohomologyPullback.{u, e, e'} k
        ((inverseImage ((siteBaseChange f).obj U).hom).obj F) q x))
    (t.naturality a)
  simp only [Functor.comp_map, Sheaf.H.map_comp_apply] at hlast
  exact hfirst.trans hlast

end Restriction

end AlgebraicGeometry.Scheme.EtaleCohomology
