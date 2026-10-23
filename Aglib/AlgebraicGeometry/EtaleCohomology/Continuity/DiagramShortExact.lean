/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.Cokernel
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
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

/-- The two actual natural transformations have zero composite. -/
theorem coneCoefficientNatTrans_comp_cokernelπ :
    coneCoefficientNatTrans X c η ≫ coneCoefficientNatTrans X c
        (InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η) = 0 := by
  apply NatTrans.ext
  funext i
  change (inverseImage (c.ι.app i).unop).map (η.app i) ≫
      (inverseImage (c.ι.app i).unop).map
        ((InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η).app i) = 0
  rw [← Functor.map_comp, InjectiveSystem.System.comp_cokernelπ, Functor.map_zero]

/-- The original pulled-back coefficient diagrams and their actual quotient
maps, packaged as a short complex in the functor category. -/
def coneCoefficientCokernelComplex :
    ShortComplex (I ⥤ AbelianSheaf.{u, u + 1} c.pt.unop) :=
  ShortComplex.mk (coneCoefficientNatTrans X c η)
    (coneCoefficientNatTrans X c
      (InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η))
    (coneCoefficientNatTrans_comp_cokernelπ X c η)

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
  apply ShortComplex.exact_of_evaluation
  intro i
  rw [coneCoefficientCokernelComplex_component]
  exact (InjectiveSystem.System.cokernelShortComplex_exact
    (diagramAdjunctionData X) η i).map (inverseImage (c.ι.app i).unop)

/-- A monic stage component gives the original short exact inverse-image
sequence, without an injectivity assertion about any pulled-back object. -/
theorem coneCoefficientCokernelComplex_component_shortExact (i : I)
    [Mono (η.app i)] :
    ((coneCoefficientCokernelComplex X c η).map
      ((CategoryTheory.evaluation I (AbelianSheaf.{u, u + 1} c.pt.unop)).obj i)).ShortExact := by
  rw [coneCoefficientCokernelComplex_component]
  exact (InjectiveSystem.System.cokernelShortComplex_shortExact
    (diagramAdjunctionData X) η i).map_of_exact (inverseImage (c.ι.app i).unop)

/-- A pointwise monic system morphism gives a short exact sequence of the
actual coefficient diagrams on the cone point. -/
theorem coneCoefficientCokernelComplex_shortExact (hη : ∀ i, Mono (η.app i)) :
    (coneCoefficientCokernelComplex X c η).ShortExact where
  exact := coneCoefficientCokernelComplex_exact X c η
  mono_f := by
    have (i : I) : Mono ((coneCoefficientCokernelComplex X c η).f.app i) := by
      have : Mono (η.app i) := hη i
      exact (coneCoefficientCokernelComplex_component_shortExact X c η i).mono_f
    exact NatTrans.mono_of_mono_app _
  epi_g := by
    have (i : I) : Epi ((coneCoefficientCokernelComplex X c η).g.app i) := by
      change Epi ((inverseImage (c.ι.app i).unop).map
        ((InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η).app i))
      infer_instance
    exact NatTrans.epi_of_epi_app _

section Colimits

variable [HasColimitsOfShape I AddCommGrpCat.{u + 1}]

/-- The short complex whose arrows are the original maps on coefficient
colimits, not independently chosen morphisms with the same endpoints. -/
def coneCoefficientColimitCokernelComplex :
    ShortComplex (AbelianSheaf.{u, u + 1} c.pt.unop) :=
  (coneCoefficientCokernelComplex X c η).map colim

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
  let E : I ≌ AsSmall.{max (u + 1) uI vI} I := AsSmall.equiv (C := I)
  have : IsFiltered (AsSmall.{max (u + 1) uI vI} I) := IsFiltered.of_equivalence E
  let : HasExactColimitsOfShape I AddCommGrpCat.{max (u + 1) uI vI} :=
    HasExactColimitsOfShape.of_domain_equivalence AddCommGrpCat.{max (u + 1) uI vI} E.symm
  let : HasExactColimitsOfShape I AddCommGrpCat.{u + 1} :=
    HasExactColimitsOfShape.domain_of_functor I AddCommGrpCat.uliftFunctor.{max uI vI, u + 1}
  exact Sheaf.hasExactColimitsOfShape (K := I) (A := AddCommGrpCat.{u + 1})
    S.smallEtaleTopology

/-- Filtered colimits in the original sheaf category preserve the actual
cokernel sequence of compatible coefficients. -/
theorem coneCoefficientColimitCokernelComplex_exact [IsFiltered I] :
    (coneCoefficientColimitCokernelComplex X c η).Exact := by
  let : HasExactColimitsOfShape I (AbelianSheaf.{u, u + 1} c.pt.unop) :=
    exactFilteredSheafColimits c.pt.unop
  exact (coneCoefficientCokernelComplex_exact X c η).map colim

/-- The original limit coefficients of a compatible monomorphism and its
constructed quotient form a short exact sequence. -/
theorem coneCoefficientColimitCokernelComplex_shortExact [IsFiltered I]
    (hη : ∀ i, Mono (η.app i)) :
    (coneCoefficientColimitCokernelComplex X c η).ShortExact := by
  let : HasExactColimitsOfShape I (AbelianSheaf.{u, u + 1} c.pt.unop) :=
    exactFilteredSheafColimits c.pt.unop
  exact (coneCoefficientCokernelComplex_shortExact X c η hη).map_of_exact colim

end Colimits

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
