/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.TripleComposition
public import Aglib.CategoryTheory.Adjunction.TripleTransport

/-! # The original canonical map under specified composite-adjunction comparisons -/
@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory.Adjunction
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {J S : A ⥤ C} {U : C ⥤ A}
  {J₁ S₁ : A ⥤ B} {U₁ : B ⥤ A} {J₂ S₂ : B ⥤ C} {U₂ : C ⥤ B}
  (t : Triple J U S) (t₁ : Triple J₁ U₁ S₁) (t₂ : Triple J₂ U₂ S₂)
  [J.Full] [J.Faithful] [J₁.Full] [J₁.Faithful] [J₂.Full] [J₂.Faithful]

/-- Retain the whole original canonical-comparison composition square. -/
def TripleCompositionTransportEquation (eJ : J ≅ J₁ ⋙ J₂) (eS : S ≅ S₁ ⋙ S₂) : Prop :=
  eJ.hom ≫ whiskerRight t₁.leftToRight J₂ ≫ whiskerLeft S₁ t₂.leftToRight =
    t.leftToRight ≫ eS.hom

/-- Original conjugacies and original triple composition prove the specified square. -/
theorem Triple.leftToRight_comp_transport (eJ : J ≅ J₁ ⋙ J₂)
    (eU : U ≅ U₂ ⋙ U₁) (eS : S ≅ S₁ ⋙ S₂)
    (hJ : conjugateEquiv (t₁.adj₁.comp t₂.adj₁) t.adj₁ eJ.hom = eU.inv)
    (hU : conjugateEquiv (t₂.adj₂.comp t₁.adj₂) t.adj₂ eU.hom = eS.inv) :
    TripleCompositionTransportEquation t t₁ t₂ eJ eS := by
  have h := Triple.leftToRight_transport t (t₁.comp t₂) eJ eU eS hJ hU
  change _ = _ at h ⊢
  rw [Triple.leftToRight_comp] at h
  exact h
end CategoryTheory.Adjunction
