/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverSheafQuotient

/-! Naturality in the finite cover of the actual section-sheaf/base-change comparison. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural comparison from étale restriction of section sheaves to section sheaves of
pulled-back covers. -/
def finiteCoverRestrictionNatIso {X S : Scheme.{u}} (f : S ⟶ X) [Etale f] :
    finiteCoverSectionSheafFunctor X ⋙ setEtaleRestriction f ≅
      baseChange f ⋙ finiteCoverSectionSheafFunctor S :=
  NatIso.ofComponents (finiteCoverRestrictionIso f) (fun {Y Z} g => by
    ext U p
    apply ULift.ext
    change (Over.mapPullbackAdj f).homEquiv (Over.mk U.unop.hom) Z.obj (p.down ≫ g.hom) =
      (Over.mapPullbackAdj f).homEquiv (Over.mk U.unop.hom) Y.obj p.down ≫
        (Over.pullback f).map g.hom
    exact (Over.mapPullbackAdj f).homEquiv_naturality_right p.down g.hom)

/-- This is natural in all finite-cover arrows, hence compares entire action diagrams. -/
def finiteCoverSectionSheafBaseChangeNatIso {X S : Scheme.{u}}
    (f : S ⟶ X) [Etale f] :
    finiteCoverSectionSheafFunctor X ⋙ setInverseImage f ≅
      baseChange f ⋙ finiteCoverSectionSheafFunctor S :=
  Functor.isoWhiskerLeft (finiteCoverSectionSheafFunctor X) (setInverseImageEtaleIso f) ≪≫
    finiteCoverRestrictionNatIso f

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 9f2383b8a315d5cf883a47198e6392cd8c9731f985d161365e91b082358481a3.
Definitions, hypotheses and universes are retained modulo native names. -/
