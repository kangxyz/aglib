/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperModuleConstructibleModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleBaseChange

/-! # Actual proper coefficient models in the original ringed category

The canonical original module-sheaf equivalence transports the already actual
same-ring model. The output is an original ringed coefficient and original
ringed inverse-image isomorphism, suitable for the original higher images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]

/-- A constructible original ringed module and its proper finitely presented
morphism have an actual proper Noetherian model over the unchanged ring. -/
theorem exists_proper_noetherian_constructible_ringed_module_model
    (R : Type u) [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f]
    (F : Coefficients.ModuleSheaf X Λ)
    (hF : Constructible.Modules.IsConstructible
      ((Coefficients.moduleSheafEquivalence X Λ).inverse.obj F)) :
    ∃ (Y T : Scheme.{u}) (g : Y ⟶ T) (a : Spec (.of R) ⟶ T) (p : X ⟶ Y),
      IsNoetherian T ∧ IsProper g ∧ IsPullback p f g a ∧
      ∃ G : Coefficients.ModuleSheaf Y Λ,
        Constructible.Modules.IsConstructible
          ((Coefficients.moduleSheafEquivalence Y Λ).inverse.obj G) ∧
        Nonempty ((Coefficients.moduleInverseImage p Λ).obj G ≅ F) := by
  obtain ⟨Y, T, g, a, p, hT, hg, H, G, hG, ⟨eG⟩⟩ :=
    exists_proper_noetherian_constructible_module_model Λ R f
      ((Coefficients.moduleSheafEquivalence X Λ).inverse.obj F) hF
  let E := Coefficients.moduleSheafEquivalence Y Λ
  let G' := E.functor.obj G
  have hG' : Constructible.Modules.IsConstructible (E.inverse.obj G') :=
    (Constructible.Modules.isConstructible_iff_of_iso (E.unitIso.app G)).mp hG
  let e : (Coefficients.moduleSheafEquivalence X Λ).inverse.obj
      ((Coefficients.moduleInverseImage p Λ).obj G') ≅
      (Coefficients.moduleSheafEquivalence X Λ).inverse.obj F :=
    (moduleInverseImageValuedIso Λ p).app G' ≪≫
      (Constructible.Modules.moduleInverseImage Λ p).mapIso (E.unitIso.app G).symm ≪≫ eG
  exact ⟨Y, T, g, a, p, hT, hg, H, G', hG',
    ⟨(Coefficients.moduleSheafEquivalence X Λ).fullyFaithfulInverse.preimageIso e⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
