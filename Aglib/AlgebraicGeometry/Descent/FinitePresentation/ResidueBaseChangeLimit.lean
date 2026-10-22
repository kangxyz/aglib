/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.ResidueColimit
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The marked closed-fibre base-change limit

The original residue field is the colimit of the residue fields of the
finite-generated coefficient stages. Native over-category limits then give
the corresponding inverse limit of scheme base changes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeResidueLimit

universe u

open Algebra.FiniteTypeSubalgebraLimit

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (p : Ideal A) [p.IsMaximal]

/-- The spectrum diagram at the specified inverse-image primes. -/
def specDiagram : (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
  (residueDiagram R A p).op ⋙ Scheme.Spec

/-- Its cone from the specified residue field. -/
def specCone : Cone (specDiagram R A p) :=
  Scheme.Spec.mapCone (residueCocone R A p).op

/-- The spectrum cone is limiting. -/
def specConeIsLimit : IsLimit (specCone R A p) :=
  isLimitOfPreserves Scheme.Spec (residueCoconeIsColimit R A p).op

/-- Every residue stage retains the coefficient-ring structure. -/
def baseStructure : specDiagram R A p ⟶
    (Functor.const (Finset A)ᵒᵖ).obj (Spec (.of R)) where
  app s := Spec.algebraMap R (stagePrime R A p s.unop).ResidueField
  naturality s t g := by
    change Spec.map (CommRingCat.ofHom (residueTransition R A p g.unop)) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (stagePrime R A p t.unop).ResidueField)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (stagePrime R A p s.unop).ResidueField))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    change residueTransition R A p g.unop
      (algebraMap R (stagePrime R A p t.unop).ResidueField r) =
        algebraMap R (stagePrime R A p s.unop).ResidueField r
    rw [IsScalarTower.algebraMap_apply R (stage R A t.unop)
        (stagePrime R A p t.unop).ResidueField r,
      residueTransition_algebraMap,
      IsScalarTower.algebraMap_apply R (stage R A s.unop)
        (stagePrime R A p s.unop).ResidueField r]
    rfl

/-- The marked residue cone is over the original coefficient spectrum. -/
theorem baseStructure_fac (s : (Finset A)ᵒᵖ) :
    (specCone R A p).π.app s ≫ (baseStructure R A p).app s =
      Spec.algebraMap R p.ResidueField := by
  change Spec.map (CommRingCat.ofHom (residueInclusion R A p s.unop)) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap R (stagePrime R A p s.unop).ResidueField)) =
    Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  change residueInclusion R A p s.unop
    (algebraMap R (stagePrime R A p s.unop).ResidueField r) =
      algebraMap R p.ResidueField r
  rw [IsScalarTower.algebraMap_apply R (stage R A s.unop)
      (stagePrime R A p s.unop).ResidueField r,
    residueInclusion_algebraMap, IsScalarTower.algebraMap_apply R A p.ResidueField r]
  rfl

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual marked residue-stage base changes. -/
def schemeDiagram : (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
  Over.lift (specDiagram R A p) (baseStructure R A p) ⋙
    Over.pullback f ⋙ Over.forget X

/-- The cone obtained using the native over-category pullback. -/
def schemeCone : Cone (schemeDiagram R A p f) :=
  (Over.pullback f ⋙ Over.forget X).mapCone
    (Over.liftCone (specDiagram R A p) (baseStructure R A p) (specCone R A p)
      (Spec.algebraMap R p.ResidueField) (baseStructure_fac R A p))

/-- The prescribed closed-fibre base change is the inverse limit of the
prescribed stage residue-field base changes. -/
def schemeConeIsLimit : IsLimit (schemeCone R A p f) :=
  isLimitOfPreserves (Over.pullback f ⋙ Over.forget X)
    (Over.isLimitLiftCone (specDiagram R A p) (baseStructure R A p) (specCone R A p)
      (Spec.algebraMap R p.ResidueField) (baseStructure_fac R A p)
      (specConeIsLimit R A p))

end AlgebraicGeometry.Scheme.FiniteTypeResidueLimit
