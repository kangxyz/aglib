/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperRingedModuleModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.RingedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.ProperNoetherianRing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.ModuleHigherBaseChangeProperty

/-! # Actual proper module constructibility over an arbitrary spectrum

Source-only final consumer, pending the genuine Noetherian endpoint and original
proper higher-image producer. The model and coefficient ring are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Actual same-ring descent and original proper exchange prove all-degree
constructibility over an arbitrary affine spectrum. -/
theorem moduleHigherDirectImage_proper_finitePresentation_isConstructible_of_spec
    (R : Type u) [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wMS} (ModuleSheaf (Spec (.of R)) Λ)]
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    (F : ModuleSheaf X Λ)
    (hF : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj F)) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence (Spec (.of R)) Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj F)) := by
  obtain ⟨Y, T, g, a, p, hT, hg, H, G, hG, ⟨eG⟩⟩ :=
    exists_proper_noetherian_constructible_ringed_module_model Λ R f F hF
  let : IsNoetherian T := hT
  let : IsProper g := hg
  let := HasDerivedCategory.standard (ModuleSheaf Y Λ)
  let := HasDerivedCategory.standard (ModuleSheaf T Λ)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} Y)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} T)
  have hmodel := moduleHigherDirectImage_proper_noetherian_isConstructible
    g Λ n hn hΛ G hG q
  let P : ObjectProperty (ModuleSheaf (Spec (.of R)) Λ) := fun M =>
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence (Spec (.of R)) Λ).inverse.obj M)
  let : P.IsClosedUnderIsomorphisms := {
    of_iso := fun e h => (Constructible.Modules.isConstructible_iff_of_iso
      ((moduleSheafEquivalence (Spec (.of R)) Λ).inverse.mapIso e)).mp h }
  have hbase := (Proper.properModuleHigherBaseChange_property_iff
    Λ g f a p H n hn hΛ q G P).mp (moduleIsConstructible_inverseImage Λ a _ hmodel)
  exact (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence (Spec (.of R)) Λ).inverse.mapIso
      (((moduleDirectImage f Λ).rightDerived q).mapIso eG))).mp hbase


end AlgebraicGeometry.Scheme.EtaleCohomology
