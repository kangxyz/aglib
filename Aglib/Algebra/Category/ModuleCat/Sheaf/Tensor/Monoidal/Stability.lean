/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.LocalIso
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.TensorAdjunction

/-!
# Tensor stability of actual module local isomorphisms

Currying into the actual presheaf-source Hom sheaf transfers the native sheaf-target
bijection criterion across tensoring. This proves stability in both tensor factors,
without points and without assuming the desired monoidality of the localization class.

The actual input ring and module carriers are `max uC vC r`. The final supplier is a
theorem that callers can install at their explicit common world: the residual universe
is not inferred from a `max` expression. Plain Hom keeps its independent universes.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory MonoidalCategory
open SheafOfModules.InternalHom.PresheafSource
  (tensorHomEquiv tensorHomEquivRight
    tensorHomEquiv_whiskerLeft_comp tensorHomEquivRight_whiskerRight_comp)

universe uC vC r

namespace SheafOfModulesOfCommRing

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})
  [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]

/-- The actual local-isomorphism class is stable under tensoring on the left. -/
theorem presheafLocalIso_whiskerLeft
    (B : PresheafOfModulesOfCommRing.{max uC vC r} R.obj)
    {P Q : PresheafOfModulesOfCommRing.{max uC vC r} R.obj}
    (f : P ⟶ Q) (hf : presheafLocalIso R f) : presheafLocalIso R (B ◁ f) := by
  apply (presheafLocalIso_iff_bijective R (B ◁ f)).2
  intro N
  let H : SheafOfModulesOfCommRing R :=
    SheafOfModules.InternalHom.PresheafSource.sheaf R B N
  let eP := tensorHomEquiv.{uC, vC, r} R B P N
  let eQ := tensorHomEquiv.{uC, vC, r} R B Q N
  have h := (presheafLocalIso_iff_bijective R f).1 hf H
  have key : (fun g : B ⊗ Q ⟶ N.val => (B ◁ f) ≫ g) =
      eP.symm ∘ (fun g : Q ⟶ H.val => f ≫ g) ∘ eQ := by
    funext g
    apply eP.injective
    exact (tensorHomEquiv_whiskerLeft_comp.{uC, vC, r} R f g).trans
      (eP.apply_symm_apply _).symm
  exact key.symm ▸ (eP.symm.bijective.comp (h.comp eQ.bijective))

/-- The actual local-isomorphism class is stable under tensoring on the right. -/
theorem presheafLocalIso_whiskerRight
    (B : PresheafOfModulesOfCommRing.{max uC vC r} R.obj)
    {P Q : PresheafOfModulesOfCommRing.{max uC vC r} R.obj}
    (f : P ⟶ Q) (hf : presheafLocalIso R f) : presheafLocalIso R (f ▷ B) := by
  apply (presheafLocalIso_iff_bijective R (f ▷ B)).2
  intro N
  let H : SheafOfModulesOfCommRing R :=
    SheafOfModules.InternalHom.PresheafSource.sheaf R B N
  let eP := tensorHomEquivRight.{uC, vC, r} R B P N
  let eQ := tensorHomEquivRight.{uC, vC, r} R B Q N
  have h := (presheafLocalIso_iff_bijective R f).1 hf H
  have key : (fun g : Q ⊗ B ⟶ N.val => (f ▷ B) ≫ g) =
      eP.symm ∘ (fun g : Q ⟶ H.val => f ≫ g) ∘ eQ := by
    funext g
    apply eP.injective
    exact (tensorHomEquivRight_whiskerRight_comp.{uC, vC, r} R f g).trans
      (eP.apply_symm_apply _).symm
  exact key.symm ▸ (eP.symm.bijective.comp (h.comp eQ.bijective))

/-- The monoidal localization-class supplier in the explicitly chosen common universe sector. -/
theorem presheafLocalIso_isMonoidal : (presheafLocalIso R).IsMonoidal where
  whiskerLeft B _ _ f hf := presheafLocalIso_whiskerLeft.{uC, vC, r} R B f hf
  whiskerRight f hf B := presheafLocalIso_whiskerRight.{uC, vC, r} R B f hf
  __ := presheafLocalIso_isMultiplicative R

end SheafOfModulesOfCommRing
