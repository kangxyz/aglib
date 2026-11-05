/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperModuleFinitePresentationSpec

/-! # Original proper module higher images over an arbitrary affine target

Source-only consumer of the actual spectrum theorem and original comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- The canonical affine-spectrum isomorphism transports the actual result
back to the original affine target and original higher image. -/
theorem moduleHigherDirectImage_proper_finitePresentation_isConstructible_of_isAffine
    {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    (F : ModuleSheaf X Λ)
    (hF : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj F)) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj F)) := by
  let g := f ≫ S.isoSpec.hom
  let := HasDerivedCategory.standard (ModuleSheaf (Spec (.of Γ(S, ⊤))) Λ)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (Spec (.of Γ(S, ⊤))))
  have hg := moduleHigherDirectImage_proper_finitePresentation_isConstructible_of_spec
    Γ(S, ⊤) g Λ n hn hΛ F hF q
  have H : IsPullback (𝟙 X) f g S.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [g]⟩
  let P : ObjectProperty (ModuleSheaf S Λ) := fun M =>
    Constructible.Modules.IsConstructible ((moduleSheafEquivalence S Λ).inverse.obj M)
  let : P.IsClosedUnderIsomorphisms := {
    of_iso := fun e h => (Constructible.Modules.isConstructible_iff_of_iso
      ((moduleSheafEquivalence S Λ).inverse.mapIso e)).mp h }
  have hbase := (Proper.properModuleHigherBaseChange_property_iff
    Λ g f S.isoSpec.hom (𝟙 X) H n hn hΛ q F P).mp
      (moduleIsConstructible_inverseImage Λ S.isoSpec.hom _ hg)
  exact (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence S Λ).inverse.mapIso
      (((moduleDirectImage f Λ).rightDerived q).mapIso
        ((moduleInverseImageIdIso Λ X).app F)))).mp hbase


end AlgebraicGeometry.Scheme.EtaleCohomology
