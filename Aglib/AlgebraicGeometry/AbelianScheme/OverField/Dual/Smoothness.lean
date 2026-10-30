/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Properness
public import Aglib.AlgebraicGeometry.Group.Dimension.Smoothness
public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentBaseChangeMap
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.QuasiCompactSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Smoothness and dimension of the same dual Picard component from the original H1 bound

Over an algebraically closed field, the actual ample-map finite kernel gives local
quasi-finiteness. The original H1 inequality then forces regularity of the actual Pic0 unit;
the native translation criterion gives smoothness, and the general smooth-group dimension
theorem gives equality with the original source dimension.

Over every field, the same H1 inequality transports through the existing proper coherent
base-change map. The source's relative smooth dimension is unchanged, and the original ample
bundle pulls back to an ample bundle. Applying the algebraically closed criterion to the
canonical base changes of `A`, `P` and `R`, then using the proved original Pic0 structure-map
triangle, descends smoothness fpqc. No second Picard representative or new field-extension
inequality is an input. The original H1 inequality remains explicit until its native supplier
has been proved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The original H1 inequality makes the same Picard component smooth of the source dimension
over an algebraically closed field. The actual ample map supplies its finite kernel. -/
theorem smooth_and_dimension_picardIdentityComponent_of_structureH1_le_of_isAlgClosed
    [IsAlgClosed k] (L : LineBundle A.left) (hL : L.IsAmple)
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    Smooth (picardIdentityComponent A.hom P R).hom ∧
      topologicalKrullDim (picardIdentityComponent A.hom P R).left =
        topologicalKrullDim A.left := by
  let := picardCommGrpObj A.hom P R
  let J := picardIdentityComponent A.hom P R
  let φ := lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)
  let fg := lineBundleClassIdentityComponentGroupHom A P R (classOf A.left L)
  have : Flat A.hom := inferInstance
  have : IsFinite (Group.Kernel.group fg).X.hom :=
    isFinite_kernel_lineBundleClassIdentityComponentGroupHom A P R L hL
  have hf : LocallyQuasiFinite fg.hom.hom.left :=
    Group.Kernel.locallyQuasiFinite_of_isFinite_group fg
  have : LocallyQuasiFinite φ.left := hf
  have : IsMonHom φ := isMonHom_lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : PreconnectedSpace A.left := inferInstance
  have : LocallyOfFiniteType J.hom := by
    change LocallyOfFiniteType ((identityComponent P.obj).ι ≫ P.obj.hom)
    infer_instance
  have hdata := unit_dimension_cotangent_and_regular_picardIdentityComponent_of_structureH1_le
    A P R φ hH1
  have : IsRegularLocalRing (J.left.presheaf.stalk (Group.unitPoint J)) := hdata.2.2
  have hs : Smooth J.hom := Group.smooth_of_isRegularLocalRing_unit_of_isAlgClosed J
  have hjdim := Group.topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected J
  have hadim := Group.topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected A
  have hcot : (Module.finrank k (Cotangent.Space η[J]) : WithBot ℕ∞) =
      Module.finrank k (Cotangent.Space η[A]) := by exact_mod_cast hdata.2.1
  exact ⟨hs, hjdim.trans (hcot.trans hadim.symm)⟩

/-- The same chosen Picard component is proper, smooth and of the original source dimension
over every field, under the displayed original-H1 inequality. All ample-map, base-change and
fpqc descent inputs are discharged from the original data. -/
theorem isProper_smooth_and_dimension_picardIdentityComponent_of_structureH1_le
    (L : LineBundle A.left) (hL : L.IsAmple)
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    IsProper (picardIdentityComponent A.hom P R).hom ∧
      Smooth (picardIdentityComponent A.hom P R).hom ∧
      topologicalKrullDim (picardIdentityComponent A.hom P R).left =
        topologicalKrullDim A.left := by
  let := picardCommGrpObj A.hom P R
  let J := picardIdentityComponent A.hom P R
  have hproper :=
    (surjective_lineBundleClassMorphismIdentityComponent_and_isProper_of_structureH1_le
      A P R L hL hH1).2
  let K := AlgebraicClosure k
  let b : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let A' := fieldBaseChange K A
  let : GrpObj A' := by
    change GrpObj ((Over.pullback b).obj A)
    exact Functor.grpObjObj (F := Over.pullback b) (G := A)
  let P' := LocallyNoetherianOver.baseChange b P
  let R' := baseChangeRepresentableBy A.hom b P R
  have : IsProper A'.hom := by
    change IsProper (pullback.snd A.hom b)
    infer_instance
  have : Smooth A'.hom := by
    change Smooth (pullback.snd A.hom b)
    infer_instance
  have : GeometricallyIntegral A'.hom := by
    change GeometricallyIntegral (pullback.snd A.hom b)
    infer_instance
  have : IsSeparated P'.obj.hom := by
    change IsSeparated (pullback.snd P.obj.hom b)
    infer_instance
  have hbAffine : IsAffineHom b := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    infer_instance
  let hAffineBC : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom.{u}) :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
  have : IsAffineHom (pullback.fst A.hom b) :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback _ _ _ hAffineBC)
      (IsPullback.of_hasPullback A.hom b).flip hbAffine
  let L' : LineBundle A'.left := pullbackLineBundle (pullback.fst A.hom b) L
  have hL' : L'.IsAmple := hL.pullback_of_isAffineHom (pullback.fst A.hom b)
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : PreconnectedSpace A.left := inferInstance
  let d := Module.finrank k (Cotangent.Space η[A])
  have hd : SmoothOfRelativeDimension d A.hom :=
    Group.smoothOfRelativeDimension_finrank_identityCotangent_of_preconnected A
  let hDimensionBC : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} d) :=
    AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have hd' : SmoothOfRelativeDimension d A'.hom := by
    change SmoothOfRelativeDimension d (pullback.snd A.hom b)
    exact (@MorphismProperty.IsStableUnderBaseChange.of_isPullback _ _ _ hDimensionBC)
      (IsPullback.of_hasPullback A.hom b) hd
  have hcot' : Module.finrank K (Cotangent.Space η[A']) = d := Cotangent.finrank η[A'] d
  have : Module.Free k (structureCohomology k A 1) := Module.Free.of_divisionRing k _
  have hbase : Module.finrank K (structureCohomology K A' 1) =
      Module.finrank k (structureCohomology k A 1) :=
    (LinearEquiv.ofBijective (structureCohomologyBaseChangeMap K A 1)
      (structureCohomologyBaseChangeMap_bijective_of_isProper K A 1)).finrank_eq.symm.trans
        (Module.finrank_baseChange (R := K) (S := k))
  have hH1' : Module.finrank K (structureCohomology K A' 1) ≤
      Module.finrank K (Cotangent.Space η[A']) := hbase.le.trans (hH1.trans hcot'.ge)
  have hsK : Smooth (picardIdentityComponent A'.hom P' R').hom :=
    (smooth_and_dimension_picardIdentityComponent_of_structureH1_le_of_isAlgClosed
      A' P' R' L' hL' hH1').1
  have hsbase : Smooth (pullback.snd J.hom b) := by
    rw [← picardIdentityComponentBaseChangeIso_hom_comp A.hom P R K]
    infer_instance
  have : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Surjective b := ⟨Function.surjective_to_subsingleton _⟩
  have : QuasiCompact b := quasiCompact_of_compactSpace b
  have hs : Smooth J.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := J.hom) (g := b)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsbase
  let φ := lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)
  let fg := lineBundleClassIdentityComponentGroupHom A P R (classOf A.left L)
  have : Flat A.hom := inferInstance
  have : IsFinite (Group.Kernel.group fg).X.hom :=
    isFinite_kernel_lineBundleClassIdentityComponentGroupHom A P R L hL
  have hf : LocallyQuasiFinite fg.hom.hom.left :=
    Group.Kernel.locallyQuasiFinite_of_isFinite_group fg
  have : LocallyQuasiFinite φ.left := hf
  have : IsMonHom φ := isMonHom_lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)
  have hdata := unit_dimension_cotangent_and_regular_picardIdentityComponent_of_structureH1_le
    A P R φ hH1
  have hjdim := Group.topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected J
  have hadim := Group.topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected A
  have hcot : (Module.finrank k (Cotangent.Space η[J]) : WithBot ℕ∞) =
      Module.finrank k (Cotangent.Space η[A]) := by exact_mod_cast hdata.2.1
  exact ⟨hproper, hs, hjdim.trans (hcot.trans hadim.symm)⟩

end AlgebraicGeometry.Scheme.RelativePicard
