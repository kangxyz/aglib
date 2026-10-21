/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotientRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartScalarRestriction
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.PresentationCompatibility

/-! # Original chart quotient restriction as a shared compatibility property -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {Z : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (c : Spec R ⟶ Z) (d : Spec S ⟶ Z)
  [IsOpenImmersion c] [IsOpenImmersion d] [IsOpenImmersion (Spec.map φ)]
  (hc : Spec.map φ ≫ c = d) (Q : Z.Modules) [Q.IsQuasicoherent]
  (N : ModuleCat.{u} R) (N' : ModuleCat.{u} S)
  (q : moduleSpecΓFunctor.obj (Q.restrict c) ⟶ N)
  (q' : moduleSpecΓFunctor.obj (Q.restrict d) ⟶ N')
  (b : (ModuleCat.extendScalars φ.hom).obj N ≅ N')

/-- The exact original sheaf quotient square on two commuting affine charts. -/
def affineChartQuotientRestrictionEquation : Prop :=
  (restrictFunctor (Spec.map φ)).map (affineQuotientFromSections (Q.restrict c) N q) ≫
    (affineSheafIsoOfSectionIso ((tilde N).restrict (Spec.map φ)) N'
      ((affineRestrictGlobalSectionsIso φ (tilde N)).symm ≪≫
        (ModuleCat.extendScalars φ.hom).mapIso (tilde.toTildeΓNatIso.app N).symm ≪≫ b)).hom =
  (affineChartRestrictionIso φ c d hc Q).hom ≫
    affineQuotientFromSections (Q.restrict d) N' q'

/-- Pass from the original named scalar-presentation square to the original
named sheaf quotient square before specializing chart rings or coefficients. -/
theorem affineChartQuotientRestrictionEquation_of_presentation
    {B : Type u} [CommRing B] [Algebra B R] (L : ModuleCat.{u} B)
    (e : moduleSpecΓFunctor.obj (Q.restrict c) ≅ ModuleCat.of R (R ⊗[B] L))
    (h : ModuleCat.algebraTensorPresentationCompatible φ.hom e q q' b.hom
      (affineChartScalarRestriction φ c d hc Q)) :
    affineChartQuotientRestrictionEquation φ c d hc Q N N' q q' b := by
  apply affineQuotientFromSections_restriction φ (Q.restrict c) (Q.restrict d) N N'
    q q' (affineChartRestrictionIso φ c d hc Q).hom b
  simpa only [ModuleCat.algebraTensorPresentationCompatible,
    affineChartScalarRestriction, Category.assoc] using h

end AlgebraicGeometry.Scheme.Modules.Coherent
