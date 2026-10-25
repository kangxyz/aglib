/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartGeometricStalkIndex

/-! # The original pointed-neighborhood limit over an arbitrary base

The actual affine spectrum cone extends along the initial marked-chart index.
Its apex, original structural map, and chosen geometric point are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u
open Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {S : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (η : Spec (.of Ω) ⟶ S) (hη : Spec.algebraMap R Ω ≫ j = η)

/-- The original scheme diagram of all marked étale neighborhoods. -/
def pointedNeighborhoodDiagram : (pointSmallEtale η).fiber.Elements ⥤ Scheme.{u} :=
  Functor.Elements.π (pointSmallEtale η).fiber ⋙ Etale.forget S ⋙ Over.forget S

/-- The literal spectrum cone regarded over the restricted original diagram. -/
def chartPointedNeighborhoodCone :
    Cone (chartToPointElements R Ω j η hη ⋙ pointedNeighborhoodDiagram Ω η) where
  pt := (specCone R Ω).pt
  π :=
    { app := fun i => (specCone R Ω).π.app i
      naturality := fun _ _ a => (specCone R Ω).π.naturality a }

/-- The restricted cone has the original spectrum universal property. -/
def chartPointedNeighborhoodConeIsLimit :
    IsLimit (chartPointedNeighborhoodCone R Ω j η hη) := by
  exact specConeIsLimit R Ω

/-- The actual cone on every original marked étale neighborhood. -/
def pointedNeighborhoodCone : Cone (pointedNeighborhoodDiagram Ω η) :=
  Functor.Initial.extendCone.obj (chartPointedNeighborhoodCone R Ω j η hη)

/-- Initiality transfers the actual spectrum limit to the full original index. -/
def pointedNeighborhoodConeIsLimit :
    IsLimit (pointedNeighborhoodCone R Ω j η hη) :=
  (Functor.Initial.isLimitExtendConeEquiv (chartToPointElements R Ω j η hη)
    (chartPointedNeighborhoodCone R Ω j η hη)).symm
    (chartPointedNeighborhoodConeIsLimit R Ω j η hη)

/-- At each chart neighborhood, the extended leg is the original spectrum map. -/
lemma pointedNeighborhoodCone_π_chart (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
    (pointedNeighborhoodCone R Ω j η hη).π.app
      ((chartToPointElements R Ω j η hη).obj i) = (specCone R Ω).π.app i :=
  Functor.Initial.limit_cone_comp_aux (chartPointedNeighborhoodCone R Ω j η hη) i

/-- Any actual pointed refinement computes the full cone projection. -/
lemma pointedNeighborhoodCone_π_refinement
    (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ)
    (d : (pointSmallEtale η).fiber.Elements)
    (a : (chartToPointElements R Ω j η hη).obj i ⟶ d) :
    (pointedNeighborhoodCone R Ω j η hη).π.app d =
      (specCone R Ω).π.app i ≫ a.hom.left :=
  Functor.Initial.extendCone_obj_π_app' (chartPointedNeighborhoodCone R Ω j η hη) a

/-- Every extended projection lies over the literal original structural map. -/
lemma pointedNeighborhoodCone_π_structure (d : (pointSmallEtale η).fiber.Elements) :
    (pointedNeighborhoodCone R Ω j η hη).π.app d ≫ d.obj.hom =
      Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j := by
  let T := chartToPointElements R Ω j η hη
  let i := Functor.Initial.lift T d
  let a := Functor.Initial.homToLift T d
  have ha : a.hom.left ≫ d.obj.hom = Spec.algebraMap R i.unop.algebra ≫ j :=
    MorphismProperty.Over.w a.hom
  exact (congrArg (fun z => z ≫ d.obj.hom)
    (pointedNeighborhoodCone_π_refinement R Ω j η hη i d a)).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun z => (specCone R Ω).π.app i ≫ z)
      ha).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ j) (π_structure R Ω i.unop)))))

/-- The chosen field point maps to the marked point at every original neighborhood. -/
lemma point_pointedNeighborhoodCone_π (d : (pointSmallEtale η).fiber.Elements) :
    point R Ω ≫ (pointedNeighborhoodCone R Ω j η hη).π.app d = d.val.left := by
  let T := chartToPointElements R Ω j η hη
  let i := Functor.Initial.lift T d
  let a := Functor.Initial.homToLift T d
  have ha := congrArg
    (fun k : Over.mk η ⟶ (Etale.forget S).obj d.obj => k.left) a.map_val
  have hp : Spec.map (CommRingCat.ofHom i.unop.point.toRingHom) ≫ a.hom.left =
      d.val.left := ha
  exact (congrArg (fun z => point R Ω ≫ z)
    (pointedNeighborhoodCone_π_refinement R Ω j η hη i d a)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ a.hom.left) (point_π R Ω i.unop)).trans hp))

include hη in
omit [IsSepClosed Ω] [Etale j] [Mono j] in
/-- The retained geometric point lies over the given original base point. -/
lemma point_pointedNeighborhood_structure :
    point R Ω ≫ (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) = η :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ j) (point_structure R Ω)).trans hη)

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
