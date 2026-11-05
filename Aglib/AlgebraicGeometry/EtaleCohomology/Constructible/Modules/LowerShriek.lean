/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImagePartitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructibleSums
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Exactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleOpenPart

/-! # Constructibility of original module extension by zero

The original native lower shriek restricts to the original coefficient on the
open and to zero on its reduced closed complement. The actual open-complement
partition therefore proves constructibility over a Noetherian scheme. The
coefficient ring is arbitrary commutative: finite-type module values need not
have finite underlying additive groups, and the ring need not be Noetherian.

The module-valued statement uses the existing coefficient equivalence. Neither
statement replaces the original extension functor or chooses a derived model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- The original module extension by zero restricts to zero on the actual
complementary closed subscheme. The proof uses the original localization
arrows and adjunction triangle, without a derived realization. -/
theorem isZero_moduleInverseImage_lowerShriek
    {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [Ring Λ]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (M : Coefficients.ModuleSheaf U Λ) :
    IsZero ((Coefficients.moduleInverseImage i Λ).obj
      ((moduleLowerShriek j Λ).obj M)) := by
  let K := (moduleLowerShriek j Λ).obj M
  let adj := Coefficients.moduleInverseImageAdjunction i Λ
  have : IsIso ((moduleLowerShriekAdjunction j Λ).counit.app K) :=
    (moduleLowerShriekAdjunction j Λ).isIso_counit_app_of_iso (Iso.refl _)
  have hη : adj.unit.app K = 0 := by
    apply (cancel_epi ((moduleLowerShriekAdjunction j Λ).counit.app K)).mp
    simpa only [comp_zero] using
      moduleLocalization_counit_comp_unit j Λ i hcomp K
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← adj.left_triangle_components K, hη, Functor.map_zero, zero_comp]

namespace Constructible.Modules

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The original native extension by zero preserves finite-type module
constructibility over a Noetherian target. Its coefficient interpretation is
the existing native module-valued equivalence, with the same original module. -/
theorem isConstructible_moduleLowerShriek_of_isNoetherian
    {U X : Scheme.{u}} [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Coefficients.ModuleSheaf U Λ)
    (hM : IsConstructible ((Coefficients.moduleSheafEquivalence U Λ).inverse.obj M)) :
    IsConstructible ((Coefficients.moduleSheafEquivalence X Λ).inverse.obj
      ((moduleLowerShriek j Λ).obj M)) := by
  classical
  let K := (moduleLowerShriek j Λ).obj M
  let F := (Coefficients.moduleSheafEquivalence X Λ).inverse.obj K
  let I := IdealSheafData.vanishingIdeal j.opensRange.compl
  let q := FiniteLocallyClosedPartition.singleton I.subscheme
  let p := FiniteLocallyClosedPartition.attachOpen j q
  have hI : Set.range I.subschemeι = (Set.range j)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  have hcomp : Set.range j = (Set.range I.subschemeι)ᶜ := by
    rw [hI, compl_compl]
  have hopen : IsConstructible ((moduleInverseImage Λ j).obj F) := by
    let e : (moduleInverseImage Λ j).obj F ≅
        (Coefficients.moduleSheafEquivalence U Λ).inverse.obj M :=
      ((moduleInverseImageValuedIso Λ j).app K).symm ≪≫
        (Coefficients.moduleSheafEquivalence U Λ).inverse.mapIso
          ((moduleLowerShriekInverseImageIso j Λ).app M)
    exact (isConstructible_iff_of_iso e).mpr hM
  have hclosed : IsConstructible ((moduleInverseImage Λ I.subschemeι).obj F) := by
    have hz : IsZero ((moduleInverseImage Λ I.subschemeι).obj F) :=
      ((Coefficients.moduleSheafEquivalence I.subscheme Λ).inverse.map_isZero
        (isZero_moduleInverseImage_lowerShriek j Λ I.subschemeι hcomp M)).of_iso
          ((moduleInverseImageValuedIso Λ I.subschemeι).app K).symm
    exact (isConstructible_iff_of_iso hz.isoZero).mpr (isConstructible_zero I.subscheme)
  change IsConstructible F
  apply isConstructible_of_noetherian_partition p
  suffices ∀ a : Option (Fin q.count),
      IsConstructible ((moduleInverseImage Λ
        (FiniteLocallyClosedPartition.attachOpenInclusion j q a)).obj F) by
    intro k
    exact this ((Fintype.equivFin (Option (Fin q.count))).symm k)
  intro a
  cases a with
  | none => exact hopen
  | some k =>
    change IsConstructible ((moduleInverseImage Λ ((𝟙 I.subscheme) ≫ I.subschemeι)).obj F)
    simpa only [Category.id_comp] using hclosed

/-- The actual module-valued slice extension has the same constructibility
property through its original comparison with native lower shriek. -/
theorem isConstructible_moduleValuedLowerShriek_of_isNoetherian
    {U X : Scheme.{u}} [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j]
    {F : ModuleSheaf Λ U} (hF : IsConstructible F) :
    IsConstructible ((moduleValuedLowerShriek j Λ).obj F) := by
  let E := Coefficients.moduleSheafEquivalence U Λ
  have h : IsConstructible (E.inverse.obj (E.functor.obj F)) :=
    (isConstructible_iff_of_iso (E.unitIso.app F)).mp hF
  have hnative := isConstructible_moduleLowerShriek_of_isNoetherian j (E.functor.obj F) h
  let e : (Coefficients.moduleSheafEquivalence X Λ).inverse.obj
        ((moduleLowerShriek j Λ).obj (E.functor.obj F)) ≅
      (moduleValuedLowerShriek j Λ).obj F :=
    (moduleLowerShriekValuedIso j Λ).app (E.functor.obj F) ≪≫
      (moduleValuedLowerShriek j Λ).mapIso (E.unitIso.app F).symm
  exact (isConstructible_iff_of_iso e).mp hnative

end Constructible.Modules

end AlgebraicGeometry.Scheme.EtaleCohomology
