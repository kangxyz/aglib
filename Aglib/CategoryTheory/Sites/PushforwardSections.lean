/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Continuous

/-! # Sections of the native continuous sheaf pushforward

Normalize the whole section functor and its identity components while the site
categories remain abstract, before substituting geometric base-change functors.
-/

@[expose] public section

open Opposite

namespace CategoryTheory.Functor

universe uC vC uD vD uA vA

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) (A : Type uA) [Category.{vA} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]

/-- Sections of the original continuous pushforward are the original sections
on the image object, as an isomorphism of whole coefficient functors. -/
def sheafPushforwardContinuousSectionsIso (U : C) :
    F.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op U) ≅
      (sheafSections K A).obj (op (F.obj U)) := Iso.refl _

/-- The whole section comparison has the literal identity as every component. -/
theorem sheafPushforwardContinuousSectionsIso_hom_app (U : C) (P : Sheaf K A) :
    (F.sheafPushforwardContinuousSectionsIso A J K U).hom.app P =
      𝟙 (P.obj.obj (op (F.obj U))) := rfl

/-- The inverse section comparison also retains the literal identity component. -/
theorem sheafPushforwardContinuousSectionsIso_inv_app (U : C) (P : Sheaf K A) :
    (F.sheafPushforwardContinuousSectionsIso A J K U).inv.app P =
      𝟙 (P.obj.obj (op (F.obj U))) := rfl

end CategoryTheory.Functor
