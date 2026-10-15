/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
/-!
# Open base change for module sheaves

The base-change isomorphism is constructed from the actual restriction
adjunction and the pullback square. Its only nonformal step is the equality
of opens showing that the relevant adjunction unit is an isomorphism.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

open Scheme.Modules

variable {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion a]

/-- On opens coming from the base-change chart, the restriction unit is an
isomorphism, since the projection has precisely the required open range. -/
lemma isIso_openBaseChangeUnit :
    IsIso (Functor.whiskerRight (restrictAdjunction (pullback.fst j a)).unit
      (pushforward j ⋙ restrictFunctor a)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  change IsIso (M.presheaf.map (homOfLE
    ((pullback.fst j a).image_preimage_le (j ⁻¹ᵁ (a ''ᵁ W)))).op)
  have heq : (pullback.fst j a) ''ᵁ
      ((pullback.fst j a) ⁻¹ᵁ (j ⁻¹ᵁ (a ''ᵁ W))) = j ⁻¹ᵁ (a ''ᵁ W) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_pullbackFst]
    exact inf_eq_right.mpr (j.preimage_mono (a.image_le_opensRange W))
  have : IsIso (homOfLE ((pullback.fst j a).image_preimage_le
      (j ⁻¹ᵁ (a ''ᵁ W)))) := by
    convert (inferInstance : IsIso (eqToHom heq)) using 1
    exact Subsingleton.elim _ _
  infer_instance

/-- Restriction to an open subscheme commutes with direct image through its
actual pullback square. No quasicoherence hypothesis is needed. -/
def openBaseChange :
    pushforward j ⋙ restrictFunctor a ≅
      restrictFunctor (pullback.fst j a) ⋙ pushforward (pullback.snd j a) := by
  let p := pullback.fst j a
  let q := pullback.snd j a
  letI := isIso_openBaseChangeUnit j a
  exact
    (Functor.leftUnitor _).symm ≪≫
    asIso (Functor.whiskerRight (restrictAdjunction p).unit
      (pushforward j ⋙ restrictFunctor a)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restrictFunctor p)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pushforwardComp p j) (restrictFunctor a) ≪≫
        Functor.isoWhiskerRight (pushforwardCongr (pullback.condition (f := j) (g := a)))
          (restrictFunctor a) ≪≫
        Functor.isoWhiskerRight (pushforwardComp q a).symm (restrictFunctor a) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (pushforward q) (restrictFunctorAdjCounitIso a) ≪≫
        Functor.rightUnitor _)

end AlgebraicGeometry.Scheme.Modules
