/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.MorphismExt
public import Aglib.AlgebraicGeometry.Curves.GenericExtension
public import Aglib.AlgebraicGeometry.Curves.Nodal.LineGeometry
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.BranchComparison`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`09bd3778c95ee312d11c130086332e1fbc7498f12b9e3bd82fa0fecc1c15830d`.
Only source16–117, actual constant-preserving automorphisms and reindexing of maps from the fixed
  homogeneous projective line. The original normal/proper curve-extension input H stays explicit.
  Smoothness and normality reuse the existing canonical pinched-line comparison, with private
  proof helpers and no new projective-line carrier.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme

section GenericBirationalComparison


/-! A genuine source reindexing from actual induced function-field maps.
No equality of differently parameterized maps is assumed. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
namespace AlgebraicGeometry.Scheme.ProjectiveLine.Birational
universe u
private lemma smoothStructureMap (k : Type u) [Field k] :
    SmoothOfRelativeDimension 1 (Scheme.ProjectiveLine.structureMap k) := by
  have hs : SmoothOfRelativeDimension 1
      ((Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k).inv ≫
        Scheme.PinchedLine.lineStructure k) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  rw [← Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over, Iso.inv_hom_id_assoc] at hs
  exact hs

private lemma normalProjectiveLine (k : Type u) [Field k] :
    Scheme.NormalStalks (Scheme.ProjectiveLine.projectiveP1 k) := by
  let := smoothStructureMap k
  exact Scheme.smoothFieldNormality k _ (Scheme.ProjectiveLine.structureMap k)
    (SmoothOfRelativeDimension.smooth 1 _)

private lemma map_id (X : Scheme.{u}) [IsIntegral X] :
    Scheme.functionFieldMap (𝟙 X) = RingHom.id X.functionField := by
  unfold Scheme.functionFieldMap
  change (X.presheaf.stalkSpecializes (specializes_refl (genericPoint X)) ≫
    (𝟙 X : X ⟶ X).stalkMap (genericPoint X)).hom = _
  rw [TopCat.Presheaf.stalkSpecializes_refl, Scheme.Hom.stalkMap_id, Category.id_comp]
  rfl

open AlgebraicGeometry.Scheme.FunctionField



variable (k : Type u) [Field k]
local notation "P" => AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 k
local notation "sP" => AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k

/-- Every actual constant-preserving function-field automorphism extends to
an actual P1 automorphism; inverse identities are proved by generic uniqueness. -/
theorem exists_projectiveLineIso_of_fieldEquiv
    (H : NormalProperCurveGenericExtension.{u}) (φ : (P).functionField ≃+* (P).functionField)
    (hφ : φ.toRingHom.comp (AlgebraicGeometry.Scheme.functionFieldConstants _ sP) =
      AlgebraicGeometry.Scheme.functionFieldConstants _ sP) :
    ∃ e : P ≅ P, e.hom ≫ sP = sP ∧
      AlgebraicGeometry.Scheme.functionFieldMap e.hom = φ.toRingHom := by
  have hψ : φ.symm.toRingHom.comp (AlgebraicGeometry.Scheme.functionFieldConstants _ sP) =
    AlgebraicGeometry.Scheme.functionFieldConstants _ sP := by
    ext c
    apply φ.injective
    simpa using (DFunLike.congr_fun hφ c).symm
  let f := extend sP sP φ.toRingHom H inferInstance
    (smoothStructureMap k)
    (normalProjectiveLine k) inferInstance hφ
  let g := extend sP sP φ.symm.toRingHom H inferInstance
    (smoothStructureMap k)
    (normalProjectiveLine k) inferInstance hψ
  have hf : f ≫ sP = sP := extend_over _ _ _ _ _ _ _ _ _
  have hg : g ≫ sP = sP := extend_over _ _ _ _ _ _ _ _ _
  let : IsDominant f := extend_dominant _ _ _ _ _ _ _ _ _
  let : IsDominant g := extend_dominant _ _ _ _ _ _ _ _ _
  have hff : AlgebraicGeometry.Scheme.functionFieldMap f = φ.toRingHom :=
    extend_fieldMap _ _ _ _ _ _ _ _ _
  have hgf : AlgebraicGeometry.Scheme.functionFieldMap g = φ.symm.toRingHom :=
    extend_fieldMap _ _ _ _ _ _ _ _ _
  have hfg : f ≫ g = 𝟙 P := by
    apply AlgebraicGeometry.Scheme.FunctionField.hom_ext sP _ _
    · simp only [Category.assoc, hf, hg, Category.id_comp]
    · rw [AlgebraicGeometry.Scheme.functionFieldMap_comp,
        map_id, hff, hgf]
      ext x
      exact φ.apply_symm_apply x
  have hgf' : g ≫ f = 𝟙 P := by
    apply AlgebraicGeometry.Scheme.FunctionField.hom_ext sP _ _
    · simp only [Category.assoc, hf, hg, Category.id_comp]
    · rw [AlgebraicGeometry.Scheme.functionFieldMap_comp,
        map_id, hff, hgf]
      ext x
      exact φ.symm_apply_apply x
  exact ⟨⟨f, g, hfg, hgf'⟩, hf, hff⟩

/-- Two genuinely birational P1 maps to the same separated integral curve
are compared by a constructed source automorphism, not asserted equal. -/
theorem exists_reindexing {Z : Scheme.{u}} [IsIntegral Z]
    (sZ : Z ⟶ Spec (.of k)) [IsSeparated sZ]
    (f g : P ⟶ Z) [IsDominant f] [IsDominant g]
    [IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap f))]
    [IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap g))]
    (hf : f ≫ sZ = sP) (hg : g ≫ sZ = sP)
    (H : NormalProperCurveGenericExtension.{u}) :
    ∃ e : P ≅ P, e.hom ≫ sP = sP ∧ e.hom ≫ g = f := by
  let ef := (asIso (CommRingCat.ofHom
    (AlgebraicGeometry.Scheme.functionFieldMap f))).commRingCatIsoToRingEquiv
  let eg := (asIso (CommRingCat.ofHom
    (AlgebraicGeometry.Scheme.functionFieldMap g))).commRingCatIsoToRingEquiv
  let φ := eg.symm.trans ef
  have hfc : ef.toRingHom.comp (AlgebraicGeometry.Scheme.functionFieldConstants _ sZ) =
    AlgebraicGeometry.Scheme.functionFieldConstants _ sP := by
    exact (AlgebraicGeometry.Scheme.FunctionField.map_constants f sZ).trans (congrArg
      (AlgebraicGeometry.Scheme.functionFieldConstants _) hf)
  have hgc : eg.toRingHom.comp (AlgebraicGeometry.Scheme.functionFieldConstants _ sZ) =
    AlgebraicGeometry.Scheme.functionFieldConstants _ sP := by
    exact (AlgebraicGeometry.Scheme.FunctionField.map_constants g sZ).trans (congrArg
      (AlgebraicGeometry.Scheme.functionFieldConstants _) hg)
  have hφ : φ.toRingHom.comp (AlgebraicGeometry.Scheme.functionFieldConstants _ sP) =
    AlgebraicGeometry.Scheme.functionFieldConstants _ sP := by
    ext c
    change ef (eg.symm (AlgebraicGeometry.Scheme.functionFieldConstants _ sP c)) =
      AlgebraicGeometry.Scheme.functionFieldConstants _ sP c
    have hc : AlgebraicGeometry.Scheme.functionFieldConstants _ sP c = eg
      (AlgebraicGeometry.Scheme.functionFieldConstants _ sZ c) := (DFunLike.congr_fun hgc c).symm
    rw [hc, eg.symm_apply_apply]
    exact (DFunLike.congr_fun hfc c).trans (DFunLike.congr_fun hgc c).symm
  obtain ⟨e, he, heφ⟩ := exists_projectiveLineIso_of_fieldEquiv k H φ hφ
  refine ⟨e, he, ?_⟩
  apply AlgebraicGeometry.Scheme.FunctionField.hom_ext sZ _ _
  · simpa only [Category.assoc, hg, he] using hf.symm
  · rw [AlgebraicGeometry.Scheme.functionFieldMap_comp, heφ]
    ext z
    change ef (eg.symm (eg z)) = ef z
    rw [eg.symm_apply_apply]

end AlgebraicGeometry.Scheme.ProjectiveLine.Birational

end -- noncomputable section
end GenericBirationalComparison
