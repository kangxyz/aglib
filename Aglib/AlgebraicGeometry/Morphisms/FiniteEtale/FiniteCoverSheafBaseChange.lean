/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverConstant
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.EtaleRestriction

/-! For an étale chart, actual inverse image of the represented finite-cover
section sheaf is the section sheaf of the actual scheme pullback. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.EtaleH1

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

universe u

/-- The section-sheaf functor on finite étale covers, sending a cover morphism to
postcomposition. -/
def finiteCoverSectionSheafFunctor (X : Scheme.{u}) :
    Scheme.FiniteEtale X ⥤ Sheaf (Scheme.smallEtaleTopology X) (Type (u + 1)) where
  obj Y := finiteCoverSectionSheaf Y
  map f := { hom := {
    app U := ↾fun p => ULift.up (p.down ≫ f.hom)
    naturality {U V} g := by
      ext p
      exact congrArg ULift.up (Category.assoc _ _ _) } }
  map_id Y := by
    ext U p
    exact congrArg ULift.up (Category.comp_id p.down)
  map_comp f g := by
    ext U p
    exact congrArg ULift.up (Category.assoc _ _ _).symm

/-- The section-sheaf isomorphism induced by the cover isomorphism `e`. -/
def finiteCoverSectionSheafIso {X : Scheme.{u}} {Y Z : Scheme.FiniteEtale X} (e : Y ≅ Z) :
    finiteCoverSectionSheaf Y ≅ finiteCoverSectionSheaf Z :=
  (finiteCoverSectionSheafFunctor X).mapIso e

/-- The section equivalence for étale restriction along `f`, induced by the map-pullback
adjunction. -/
def finiteCoverRestrictionPointEquiv {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]
    (Y : Scheme.FiniteEtale X) (U : S.Etale) :
    (finiteCoverSectionSheaf Y).obj.obj (op ((siteEtalePostcompose f).obj U)) ≃
      (finiteCoverSectionSheaf ((baseChange f).obj Y)).obj.obj (op U) := by
  change ULift.{u + 1} (Over.mk (U.hom ≫ f) ⟶ Y.obj) ≃
    ULift.{u + 1} (Over.mk U.hom ⟶ ((baseChange f).obj Y).obj)
  exact Equiv.ulift.trans
    (((Over.mapPullbackAdj f).homEquiv (Over.mk U.hom) Y.obj).trans Equiv.ulift.symm)

/-- The isomorphism from the restriction of a cover's section sheaf to the section sheaf of its
pullback. -/
def finiteCoverRestrictionIso {X S : Scheme.{u}} (f : S ⟶ X) [Etale f] (Y : Scheme.FiniteEtale X) :
    (setEtaleRestriction f).obj (finiteCoverSectionSheaf Y) ≅
      finiteCoverSectionSheaf ((baseChange f).obj Y) where
  hom := { hom := {
    app U := ↾(finiteCoverRestrictionPointEquiv f Y U.unop)
    naturality {U V} g := by
      ext p
      apply ULift.ext
      change (Over.mapPullbackAdj f).homEquiv (Over.mk V.unop.hom) Y.obj
          ((Over.map f).map ((Scheme.Etale.forget S).map g.unop) ≫ p.down) =
        ((Scheme.Etale.forget S).map g.unop) ≫
          (Over.mapPullbackAdj f).homEquiv (Over.mk U.unop.hom) Y.obj p.down
      exact (Over.mapPullbackAdj f).homEquiv_naturality_left _ _ } }
  inv := { hom := {
    app U := ↾(finiteCoverRestrictionPointEquiv f Y U.unop).symm
    naturality {U V} g := by
      ext p
      apply ULift.ext
      change ((Over.mapPullbackAdj f).homEquiv (Over.mk V.unop.hom) Y.obj).symm
          (((Scheme.Etale.forget S).map g.unop) ≫ p.down) =
        (Over.map f).map ((Scheme.Etale.forget S).map g.unop) ≫
          ((Over.mapPullbackAdj f).homEquiv (Over.mk U.unop.hom) Y.obj).symm p.down
      exact (Over.mapPullbackAdj f).homEquiv_naturality_left_symm _ _ } }
  hom_inv_id := by
    ext U p
    exact (finiteCoverRestrictionPointEquiv f Y U.unop).symm_apply_apply p
  inv_hom_id := by
    ext U p
    exact (finiteCoverRestrictionPointEquiv f Y U.unop).apply_symm_apply p

/-- The comparison from the inverse image of a cover's section sheaf to the section sheaf of its
pullback. -/
def finiteCoverSectionSheafBaseChangeIso {X S : Scheme.{u}}
    (f : S ⟶ X) [Etale f] (Y : Scheme.FiniteEtale X) :
    (setInverseImage f).obj (finiteCoverSectionSheaf Y) ≅
      finiteCoverSectionSheaf ((baseChange f).obj Y) :=
  (setInverseImageEtaleIso f).app (finiteCoverSectionSheaf Y) ≪≫
    finiteCoverRestrictionIso f Y

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3e4248001d5442fbb25e59f7c04cb1bfae7854669d2ef60cc49bf83dbf9421ba.
Definitions, hypotheses and universes are retained modulo native names. -/
