/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverSheafQuotient
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.EtaleSheafDescentAction
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! The sheaf-point fibre of an actual finite-cover section sheaf is naturally
the lifted actual point-lift fibre. This comparison uses the site point, not a
Galois-category premise. -/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.EtaleH1

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite smallEtaleFiberIso toEtale)

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural identification of lifted Yoneda presheaves of finite étale objects with their
section presheaves. -/
def finiteCoverLiftedYonedaNatIso (X : Scheme.{u}) :
    toEtale X ⋙ uliftYoneda.{u + 1} ≅
      finiteCoverSectionSheafFunctor X ⋙
        sheafToPresheaf (Scheme.smallEtaleTopology X) (Type (u + 1)) :=
  NatIso.ofComponents finiteRepresentedYonedaIso (fun {Y Z} f => by
    ext U p
    apply ULift.ext
    exact (Scheme.Etale.forget X).map_comp p.down ((toEtale X).map f))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isomorphism from geometric-point fibers of cover section sheaves to lifted
finite cover fibers. -/
def coverSheafPointFiberIso {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) :
    finiteCoverSectionSheafFunctor X ⋙
        (Scheme.pointSmallEtale s).sheafFiber (A := Type (u + 1)) ≅
      fiberToFinite s ⋙ FintypeCat.incl ⋙ uliftFunctor.{u + 1} := by
  let Φ := Scheme.pointSmallEtale s
  let e : yoneda ⋙ Φ.presheafFiber (A := Type u) ≅ Φ.fiber :=
    Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm (Φ.presheafFiber (A := Type u)) ≪≫
      Φ.shrinkYonedaCompPresheafFiberIso
  exact Functor.isoWhiskerRight (finiteCoverLiftedYonedaNatIso X).symm
      (Φ.presheafFiber (A := Type (u + 1))) ≪≫
    Functor.isoWhiskerLeft (toEtale X ⋙ yoneda) (Φ.presheafFiberCompIso uliftFunctor.{u + 1}) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (toEtale X) e) uliftFunctor.{u + 1} ≪≫
    Functor.isoWhiskerRight (smallEtaleFiberIso s) uliftFunctor.{u + 1}

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 dc651b0128fbb3b1c29bbea60ea1ce383087757a555ba162b207ae6f445bc574.
Definitions, hypotheses and universes are retained modulo native names. -/
