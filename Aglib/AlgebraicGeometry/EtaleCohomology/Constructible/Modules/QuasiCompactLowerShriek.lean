/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.RingedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureSums
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.RetrocompactOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleOpenPart
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Exactness

/-! # Original extension by zero over a qcqs target

A quasi-compact open immersion permits adjoining the actual closed complement
to the original finite partition. No Noetherian target or finite carrier is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- The original module extension by zero restricts to zero on the actual
complementary closed subscheme. The proof uses the original localization
arrows and adjunction triangle, without a derived realization. -/
theorem isZero_moduleInverseImage_qcLowerShriek
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

/-- Genuine qc-open extension by zero on a qcqs target, over an arbitrary ring. -/
theorem isConstructible_moduleLowerShriek_of_qcqs
    {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (Λ : Type (u + 1)) [Ring Λ]
    (M : Coefficients.ModuleSheaf U Λ)
    (hM : IsConstructible ((Coefficients.moduleSheafEquivalence U Λ).inverse.obj M)) :
    IsConstructible ((Coefficients.moduleSheafEquivalence X Λ).inverse.obj
      ((moduleLowerShriek j Λ).obj M)) := by
  classical
  let : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  let : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated j
  let K := (moduleLowerShriek j Λ).obj M
  let F := (Coefficients.moduleSheafEquivalence X Λ).inverse.obj K
  let I := IdealSheafData.vanishingIdeal j.opensRange.compl
  have hretro : IsRetrocompact (Set.range j) :=
    (isCompact_range j.continuous).isRetrocompact j.isOpenEmbedding.isOpen_range
  let e : (moduleInverseImage Λ j).obj F ≅
      (Coefficients.moduleSheafEquivalence U Λ).inverse.obj M :=
    ((moduleInverseImageValuedIso Λ j).app K).symm ≪≫
      (Coefficients.moduleSheafEquivalence U Λ).inverse.mapIso
        ((moduleLowerShriekInverseImageIso j Λ).app M)
  obtain ⟨t⟩ := nonempty_constructiblePartition ((isConstructible_iff_of_iso e).mpr hM)
  let p := t.toFiniteLocallyClosedPartition.extendOpen j hretro
  have hI : Set.range I.subschemeι = (Set.range j)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  have hcomp : Set.range j = (Set.range I.subschemeι)ᶜ := by
    rw [hI, compl_compl]
  have hclosed : IsFiniteTypeLocallyConstant ((moduleInverseImage Λ I.subschemeι).obj F) := by
    have hz : IsZero ((moduleInverseImage Λ I.subschemeι).obj F) :=
      ((Coefficients.moduleSheafEquivalence I.subscheme Λ).inverse.map_isZero
        (isZero_moduleInverseImage_qcLowerShriek j Λ I.subschemeι hcomp M)).of_iso
          ((moduleInverseImageValuedIso Λ I.subschemeι).app K).symm
    exact (isFiniteTypeLocallyConstant_iff_of_iso hz.isoZero).mpr
      (isFiniteTypeLocallyConstant_zero I.subscheme)
  let a := FiniteLocallyClosedPartition.extendOpenInclusion j t.toFiniteLocallyClosedPartition
  have hlocal (i : Option (Fin t.count)) :
      IsFiniteTypeLocallyConstant ((moduleInverseImage Λ (a i)).obj F) := by
    cases i with
    | none => exact hclosed
    | some i =>
      exact (isFiniteTypeLocallyConstant_iff_of_iso
        ((moduleInverseImageComp Λ j (t.inclusion i)).app F)).mpr
          (t.locally_constant i)
  let q : ConstructiblePartition F :=
    { toFiniteLocallyClosedPartition := p
      locally_constant := fun k =>
        hlocal ((Fintype.equivFin (Option (Fin t.count))).symm k) }
  intro V
  have : IsAffine V.1.toScheme := V.property
  exact ⟨q.baseChange V.1.ι⟩

end Constructible.Modules
end AlgebraicGeometry.Scheme.EtaleCohomology
