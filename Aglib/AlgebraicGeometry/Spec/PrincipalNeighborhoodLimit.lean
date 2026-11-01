/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.LocalizationColimit
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The original local spectrum as a limit of principal neighborhoods

The limit vertex is the spectrum of the supplied localization. Its projections
are the actual universal principal-localization maps. Taking the denominator
submonoid to be a prime complement gives genuine principal neighborhoods of
that prime, without constructing another local-ring realization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

universe u

open IsLocalization.PrincipalDiagram

variable {R : Type u} [CommRing R] (M : Submonoid R)
variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The spectra of the original principal localization stages. -/
def specDiagram : (Finset M)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram M).op ⋙ Scheme.Spec

/-- The cone with literal vertex `Spec S` and canonical localization projections. -/
def specCone : Cone (specDiagram M) :=
  Scheme.Spec.mapCone (ringCocone M S).op

/-- The universal property of the original localization supplies the limit. -/
def specConeIsLimit : IsLimit (specCone M S) :=
  isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit M S).op

/-- The projection is the actual spectrum of the principal localization lift. -/
@[simp]
theorem specCone_projection (s : (Finset M)ᵒᵖ) :
    (specCone M S).π.app s = Spec.map (CommRingCat.ofHom (projection M S s.unop)) := rfl

/-- Every transition is affine, since both its source and target are affine. -/
instance transition_isAffine {s t : (Finset M)ᵒᵖ} (f : s ⟶ t) :
    IsAffineHom ((specDiagram M).map f) := by
  change IsAffineHom (Spec.map _)
  infer_instance

/-- The structural map of a principal stage is a genuine open immersion. -/
instance stage_isOpenImmersion (s : Finset M) :
    IsOpenImmersion (Spec.algebraMap R (stage M s)) := by
  dsimp [Spec.algebraMap]
  infer_instance

/-- The diagram retains its original coefficient maps. -/
def baseStructure : specDiagram M ⟶
    (Functor.const (Finset M)ᵒᵖ).obj (Spec (.of R)) where
  app s := Spec.algebraMap R (stage M s.unop)
  naturality s t f := by
    change Spec.map (CommRingCat.ofHom (transition M (leOfHom f.unop))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (stage M t.unop))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (stage M s.unop)))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact transition_algebraMap M (leOfHom f.unop) r

/-- The projection's structural composite is the original localization map. -/
theorem baseStructure_fac (s : (Finset M)ᵒᵖ) :
    (specCone M S).π.app s ≫ (baseStructure M).app s = Spec.algebraMap R S := by
  change Spec.map (CommRingCat.ofHom (projection M S s.unop)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (stage M s.unop))) =
      Spec.map (CommRingCat.ofHom (algebraMap R S))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  exact projection_algebraMap M S s.unop r

/-- The same principal diagram over the original coefficient spectrum. -/
def baseDiagram : (Finset M)ᵒᵖ ⥤ Over (Spec (.of R)) :=
  Over.lift (specDiagram M) (baseStructure M)

/-- The original local spectrum cone over its original base map. -/
def baseCone : Cone (baseDiagram M) :=
  Over.liftCone (specDiagram M) (baseStructure M) (specCone M S)
    (Spec.algebraMap R S) (baseStructure_fac M S)

/-- The cone is limiting also over the unchanged coefficient spectrum. -/
def baseConeIsLimit : IsLimit (baseCone M S) :=
  Over.isLimitLiftCone (specDiagram M) (baseStructure M) (specCone M S)
    (Spec.algebraMap R S) (baseStructure_fac M S) (specConeIsLimit M S)

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
