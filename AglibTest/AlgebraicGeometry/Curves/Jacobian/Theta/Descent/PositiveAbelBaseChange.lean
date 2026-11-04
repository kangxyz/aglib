/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.PositiveAbelBaseChange

/-! Native consumers of the original positive Abel map under field extension. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Scheme Scheme.RelativePicard Scheme.OverField Scheme.OverField.Curve
open Scheme.OverField.Curve.Abel.BoundedFamily

open Scheme.Cohomology

universe u

variable {S S' Y : Scheme.{u}} (p : Y ⟶ S) (b : S' ⟶ S)

example (n : ℕ) (i : Fin n) :
    (parameterBaseChangeIso p b n).hom ≫
        (Over.pullback b).map (finiteProductOverπ (fun _ : Fin n => Over.mk p) i) =
      finiteProductOverπ (fun _ : Fin n => Over.mk (pullback.snd p b)) i :=
  parameterBaseChangeIso_hom_π p b n i

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : FScheme k}
  (hX : Properties X) (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let X' := fieldBaseChange K X
    letI := hX.smooth
    letI := hX.proper
    letI := (curveProperties_baseChange hX K b).smooth
    letI := (curveProperties_baseChange hX K b).proper
    (parameterBaseChangeIso X.hom b 0).hom ≫
        (Over.pullback b).map (positiveAbelMorphism X P R 0).hom =
      (positiveAbelMorphism X' (LocallyNoetherianOver.baseChange b P)
        (baseChangeRepresentableBy X.hom b P R) 0).hom :=
  positiveAbelMorphism_baseChange hX K P R 0

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.positiveAbelMorphism_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveAbelMorphism_baseChange
