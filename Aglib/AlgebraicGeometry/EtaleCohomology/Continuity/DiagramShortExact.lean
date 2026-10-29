/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.Cokernel
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! # Short exact sequences of original limit coefficients

A compatible morphism and its pointwise cokernel give a short complex of the
actual coefficient diagrams on a scheme cone point. Its component at each
index is the original cokernel short complex mapped by exact inverse image.
The original coefficient-colimit maps therefore form a short exact sequence
when the input is pointwise monic and the indexing category is filtered.

Exactness of the sheaf colimit is obtained from exact sheafification and exact
filtered colimits of abelian groups. No preservation of filtered colimits by
the sheaf-to-presheaf inclusion, geometric continuity, or injectivity of an
inverse-image sheaf is assumed. The index object and morphism universes remain
independent; only existence of colimits of that shape in the original value
category is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (c : Cocone X) {F Q : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F Q)

local instance coneLeftPreservesFiniteLimits :
    ∀ i, PreservesFiniteLimits ((diagramConeAdjunctionData X c).left i) := by
  intro i
  exact inverseImage_preservesFiniteLimits (c.ι.app i).unop

/-- The two actual natural transformations have zero composite. -/
theorem coneCoefficientNatTrans_comp_cokernelπ :
    coneCoefficientNatTrans X c η ≫ coneCoefficientNatTrans X c
        (InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η) = 0 := by
  exact (diagramConeAdjunctionData X c).coefficientNatTrans_comp_cokernelπ η

/-- The original pulled-back coefficient diagrams and their actual quotient
maps, packaged as a short complex in the functor category. -/
def coneCoefficientCokernelComplex :
    ShortComplex (I ⥤ AbelianSheaf.{u, u + 1} c.pt.unop) :=
  (diagramConeAdjunctionData X c).coefficientCokernelComplex η

/-- Evaluation recovers the original pointwise cokernel sequence after the
specified scheme projection's inverse image. -/
theorem coneCoefficientCokernelComplex_component (i : I) :
    (coneCoefficientCokernelComplex X c η).map
        ((CategoryTheory.evaluation I (AbelianSheaf.{u, u + 1} c.pt.unop)).obj i) =
      (InjectiveSystem.System.cokernelShortComplex (diagramAdjunctionData X) η i).map
        (inverseImage (c.ι.app i).unop) := rfl

/-- Exact inverse image carries each original cokernel sequence to an exact
sequence on the cone point. -/
theorem coneCoefficientCokernelComplex_exact :
    (coneCoefficientCokernelComplex X c η).Exact := by
  exact (diagramConeAdjunctionData X c).coefficientCokernelComplex_exact η

/-- A monic stage component gives the original short exact inverse-image
sequence, without an injectivity assertion about any pulled-back object. -/
theorem coneCoefficientCokernelComplex_component_shortExact (i : I)
    [Mono (η.app i)] :
    ((coneCoefficientCokernelComplex X c η).map
      ((CategoryTheory.evaluation I (AbelianSheaf.{u, u + 1} c.pt.unop)).obj i)).ShortExact := by
  exact (diagramConeAdjunctionData X c).coefficientCokernelComplex_component_shortExact η i

/-- A pointwise monic system morphism gives a short exact sequence of the
actual coefficient diagrams on the cone point. -/
theorem coneCoefficientCokernelComplex_shortExact (hη : ∀ i, Mono (η.app i)) :
    (coneCoefficientCokernelComplex X c η).ShortExact :=
  (diagramConeAdjunctionData X c).coefficientCokernelComplex_shortExact η hη

section Colimits

variable [HasColimitsOfShape I AddCommGrpCat.{u + 1}]

/-- The short complex whose arrows are the original maps on coefficient
colimits, not independently chosen morphisms with the same endpoints. -/
def coneCoefficientColimitCokernelComplex :
    ShortComplex (AbelianSheaf.{u, u + 1} c.pt.unop) :=
  (diagramConeAdjunctionData X c).coefficientColimitCokernelComplex η

@[simp]
theorem coneCoefficientColimitCokernelComplex_f :
    (coneCoefficientColimitCokernelComplex X c η).f =
      coneCoefficientColimitMap X c η := rfl

@[simp]
theorem coneCoefficientColimitCokernelComplex_g :
    (coneCoefficientColimitCokernelComplex X c η).g =
      coneCoefficientColimitMap X c
        (InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η) := rfl

private abbrev exactFilteredSheafColimits [IsFiltered I] (S : Scheme.{u}) :
    HasExactColimitsOfShape I (AbelianSheaf.{u, u + 1} S) := by
  let : HasExactColimitsOfShape I AddCommGrpCat.{u + 1} :=
    hasExactFilteredColimitsOfShape_addCommGrpCat_of_category I
  exact Sheaf.hasExactColimitsOfShape (K := I) (A := AddCommGrpCat.{u + 1})
    S.smallEtaleTopology

/-- Filtered colimits in the original sheaf category preserve the actual
cokernel sequence of compatible coefficients. -/
theorem coneCoefficientColimitCokernelComplex_exact [IsFiltered I] :
    (coneCoefficientColimitCokernelComplex X c η).Exact := by
  let : HasExactColimitsOfShape I (AbelianSheaf.{u, u + 1} c.pt.unop) :=
    exactFilteredSheafColimits c.pt.unop
  exact (diagramConeAdjunctionData X c).coefficientColimitCokernelComplex_exact η

/-- The original limit coefficients of a compatible monomorphism and its
constructed quotient form a short exact sequence. -/
theorem coneCoefficientColimitCokernelComplex_shortExact [IsFiltered I]
    (hη : ∀ i, Mono (η.app i)) :
    (coneCoefficientColimitCokernelComplex X c η).ShortExact := by
  let : HasExactColimitsOfShape I (AbelianSheaf.{u, u + 1} c.pt.unop) :=
    exactFilteredSheafColimits c.pt.unop
  exact (diagramConeAdjunctionData X c).coefficientColimitCokernelComplex_shortExact η hη

end Colimits

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
