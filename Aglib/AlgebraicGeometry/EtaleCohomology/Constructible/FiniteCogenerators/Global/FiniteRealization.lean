/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.GeneratedAlgebra
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.RelativeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Actual finite global realization of generated subalgebras

Native relative-gluing cartesian charts prove that the actual structural map
is finite. The original ambient ring inclusions give a source comparison over
the whole base; integrality and injectivity give its actual surjectivity by
lying over. No local finite morphism is composed with an open immersion and
asserted finite over the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open AffineZariskiSite Scheme.Modules Scheme.Modules.QuasiCoherent

section Relative

variable {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {a : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (ha : a.Coequifibered)

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual finite structural affine maps give an actual finite global map
through the original native cartesian chart squares. -/
theorem relativeGluing_toBase_isFinite
    (hf : ∀ U : X.AffineZariskiSite, (a.app (op U)).hom.Finite) :
    IsFinite (relativeGluingData ha).toBase := by
  let d := relativeGluingData ha
  have : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  have : HasAffineProperty (@AlgebraicGeometry.IsFinite.{u})
      (fun S _ h _ => IsAffine S ∧ RingHom.Finite (h.appTop).hom) := inferInstance
  have : IsZariskiLocalAtTarget (@AlgebraicGeometry.IsFinite.{u}) :=
    HasAffineProperty.instIsZariskiLocalAtTarget
      (P := @AlgebraicGeometry.IsFinite.{u})
      (Q := fun S _ h _ => IsAffine S ∧ RingHom.Finite (h.appTop).hom)
  apply (IsZariskiLocalAtTarget.iff_of_openCover
    (P := @AlgebraicGeometry.IsFinite.{u}) (directedCover X)).mpr
  intro U
  have : IsFinite (Spec.map (a.app (op U))) :=
    (IsFinite.SpecMap_iff (a.app (op U))).mpr (hf U)
  have ht : IsFinite (d.natTrans.app U) := by
    change IsFinite (Spec.map (a.app (op U)) ≫ U.2.isoSpec.inv)
    infer_instance
  let sq := (d.isPullback_natTrans_ι_toBase U).flip
  have hfin : IsFinite (sq.isoPullback.inv ≫ d.natTrans.app U) := inferInstance
  change IsFinite (pullback.snd d.toBase ((directedCover X).f U))
  exact (congrArg (fun k : pullback d.toBase ((directedCover X).f U) ⟶
    (directedCover X).X U => IsFinite k) sq.isoPullback_inv_snd).mp hfin

end Relative

/-- The actual map from an affine source has the original Spec map on every
original inverse-image affine chart. -/
@[reassoc]
theorem relativeMapFromAffine_chart {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    {G : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {b : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G} (hb : b.Coequifibered)
    (φ : G ⟶ (toOpensFunctor X).op ⋙ relativeSectionDiagram f)
    (U : X.AffineZariskiSite) :
    (U.2.preimage f).fromSpec ≫ relativeMapFromAffine f hb φ =
      Spec.map (φ.app (op U)) ≫ (relativeGluingData hb).cover.f U := by
  let e := relativeSourceIso f
  let c : Spec Γ(Y, f ⁻¹ᵁ U.1) ⟶ (relativeAffineData f).glued :=
    (relativeAffineData f).cover.f U
  let m := relativeAlgebraMap (relativeSectionMap_coequifibered f) hb φ
  have hc : c ≫ e.hom = (U.2.preimage f).fromSpec := relativeCover_toSource f U
  have hc' : (U.2.preimage f).fromSpec ≫ e.inv = c :=
    (congrArg (fun k => k ≫ e.inv) hc.symm).trans
      ((Category.assoc c e.hom e.inv).trans
        ((congrArg (fun k => c ≫ k) e.hom_inv_id).trans (Category.comp_id c)))
  exact (Category.assoc (U.2.preimage f).fromSpec e.inv m).symm.trans
    ((congrArg (fun k => k ≫ m) hc').trans
      (relativeAlgebraMap_chart (relativeSectionMap_coequifibered f) hb φ U))

section Generated

variable {Y X : Scheme.{u}} (f : Y ⟶ X) {J : Type u}
  (M : J → X.Modules) (i : ∀ j, M j ⟶ pushforwardStructureSheaf f)
  (hM : ∀ j, affineLocallyFiniteType X (M j))

/-- The actual scheme obtained by gluing the generated affine subalgebras. -/
abbrev generatedAlgebraScheme [IsAffineHom f] : Scheme.{u} := (generatedSectionData f M i hM).glued

/-- Its original structural morphism to the entire original base. -/
def generatedAlgebraMorphism [IsAffineHom f] : generatedAlgebraScheme f M i hM ⟶ X :=
  (generatedSectionData f M i hM).toBase

instance generatedAlgebraMorphism_isFinite [IsIntegralHom f] [Finite J] :
    IsFinite (generatedAlgebraMorphism f M i hM) := by
  have (j : J) : (M j).IsQuasicoherent :=
    quasicoherent_of_affineCharts (M j) (fun R a _ => (hM j R a).1)
  exact relativeGluing_toBase_isFinite
    (generatedSectionStructuralMap_coequifibered f M i)
    (fun U => generatedSectionStructuralApp_finite f M i hM U)

/-- The actual original subalgebra inclusions give the original source map. -/
def generatedAlgebraComparison [IsAffineHom f] : Y ⟶ generatedAlgebraScheme f M i hM := by
  haveI (j : J) : (M j).IsQuasicoherent :=
    quasicoherent_of_affineCharts (M j) (fun R a _ => (hM j R a).1)
  exact relativeMapFromAffine f (generatedSectionStructuralMap_coequifibered f M i)
    ((toOpensFunctor X).op.whiskerLeft (generatedSectionEmbedding f M i))

/-- The comparison retains the full original structural triangle. -/
@[reassoc]
theorem generatedAlgebraComparison_over [IsAffineHom f] :
    generatedAlgebraComparison f M i hM ≫ generatedAlgebraMorphism f M i hM = f := by
  have (j : J) : (M j).IsQuasicoherent :=
    quasicoherent_of_affineCharts (M j) (fun R a _ => (hM j R a).1)
  apply relativeMapFromAffine_over
  apply NatTrans.ext
  funext U
  exact generatedSectionStructuralApp_inclusion f M i U.unop.1

/-- The comparison is literally Spec of the original subalgebra inclusion
on each actual original inverse-image affine chart. -/
@[reassoc]
theorem generatedAlgebraComparison_chart [IsAffineHom f] (U : X.AffineZariskiSite) :
    (U.2.preimage f).fromSpec ≫ generatedAlgebraComparison f M i hM =
      Spec.map (generatedSectionInclusion f M i U.1) ≫
        (generatedSectionData f M i hM).cover.f U := by
  have (j : J) : (M j).IsQuasicoherent :=
    quasicoherent_of_affineCharts (M j) (fun R a _ => (hM j R a).1)
  exact relativeMapFromAffine_chart f
    (generatedSectionStructuralMap_coequifibered f M i)
    ((toOpensFunctor X).op.whiskerLeft (generatedSectionEmbedding f M i)) U

/-- Integrality over the original base implies integrality of the actual
intermediate subalgebra inclusion, using the full original ring-map triangle. -/
theorem generatedSectionInclusion_integral [IsIntegralHom f] (U : X.affineOpens) :
    (generatedSectionInclusion f M i U.1).hom.IsIntegral := by
  have hc : ((generatedSectionInclusion f M i U.1).hom.comp
      (generatedSectionStructuralApp f M i U.1).hom).IsIntegral := by
    change (generatedSectionStructuralApp f M i U.1 ≫
      generatedSectionInclusion f M i U.1).hom.IsIntegral
    rw [generatedSectionStructuralApp_inclusion]
    exact IsIntegralHom.isIntegral_app f U.1 U.2
  exact RingHom.IsIntegral.tower_top
    (generatedSectionStructuralApp f M i U.1).hom
    (generatedSectionInclusion f M i U.1).hom hc

/-- Lying over for the literal original injective subalgebra inclusions
makes the actual global comparison surjective. -/
instance generatedAlgebraComparison_surjective [IsIntegralHom f] :
    Surjective (generatedAlgebraComparison f M i hM) := by
  constructor
  intro z
  let d := generatedSectionData f M i hM
  let U : X.AffineZariskiSite := d.cover.idx z
  obtain ⟨zU, hzU⟩ := d.cover.covers z
  have hi : Function.Injective (generatedSectionInclusion f M i U.1).hom := by
    intro a b h
    exact Subtype.ext h
  obtain ⟨yU, hyU⟩ := (generatedSectionInclusion_integral f M i U).comap_surjective hi zU
  refine ⟨(U.2.preimage f).fromSpec yU, ?_⟩
  have h := congrArg (fun k : Spec Γ(Y, f ⁻¹ᵁ U.1) ⟶ generatedAlgebraScheme f M i hM => k yU)
    (generatedAlgebraComparison_chart f M i hM U)
  exact h.trans ((congrArg (d.cover.f U) hyU).trans hzU)

instance generatedAlgebraComparison_integral [IsIntegralHom f] [Finite J] :
    IsIntegralHom (generatedAlgebraComparison f M i hM) := by
  have : IsIntegralHom (generatedAlgebraComparison f M i hM ≫
      generatedAlgebraMorphism f M i hM) := by
    rw [generatedAlgebraComparison_over]
    infer_instance
  exact IsIntegralHom.of_comp (generatedAlgebraComparison f M i hM)
    (generatedAlgebraMorphism f M i hM)

end Generated
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
