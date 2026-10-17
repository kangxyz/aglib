/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildePullback

/-! Focused consumer of the composition compatibility of the affine pullback comparison
`Scheme.Modules.tildePullbackIso`. The objects are Mathlib's `ModuleCat`, `tilde.functor` and
`Scheme.Modules.pullback`; the composition isomorphisms are Mathlib's `pullbackComp` and
`ModuleCat.extendScalarsComp`. Universes: `CommRingCat.{u}`, `ModuleCat.{u}`. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

variable {R S T : CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) (N : ModuleCat.{u} R)

example (h : Spec.map (a ≫ b) = Spec.map b ≫ Spec.map a) :
    (pullbackCongr h).hom.app ((tilde.functor R).obj N) ≫
        (pullbackComp (Spec.map b) (Spec.map a)).inv.app ((tilde.functor R).obj N) ≫
        (pullback (Spec.map b)).map ((tildePullbackIso a).hom.app N) ≫
        (tildePullbackIso b).hom.app ((ModuleCat.extendScalars a.hom).obj N) =
      (tildePullbackIso (a ≫ b)).hom.app N ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp a.hom b.hom).hom.app N) :=
  tildePullbackIso_comp_hom_app a b h N

example : conjugateEquiv
      ((ModuleCat.extendRestrictScalarsAdj a.hom).comp (tilde.adjunction (R := S)))
      ((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map a)))
      (tildePullbackIso a).hom = (pushforwardGlobalSectionsIso a).inv :=
  conjugateEquiv_tildePullbackIso_hom a

/--
info: 'AlgebraicGeometry.Scheme.Modules.tildePullbackIso_comp_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tildePullbackIso_comp_hom

/--
info: 'AlgebraicGeometry.Scheme.Modules.tildePullbackIso_comp_hom_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tildePullbackIso_comp_hom_app

/--
info: 'AlgebraicGeometry.Scheme.Modules.conjugateEquiv_tildePullbackIso_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms conjugateEquiv_tildePullbackIso_hom
