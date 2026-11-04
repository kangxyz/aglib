/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Descent.Single

/-! Singleton morphism descent with independent category and fibre universes. -/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Pseudofunctor

universe v u v' u'

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {Y Z : C} (f : Y ⟶ Z)
  [(F.toDescentData (fun _ : PUnit.{1} => f)).Full]
  {M N : F.obj (.mk (op Z))}

example (φ : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ⟶
    (F.toDescentData (fun _ : PUnit.{1} => f)).obj N) :
    (F.map f.op.toLoc).toFunctor.map (SingleDescent.liftHom F f φ) = φ.hom PUnit.unit :=
  SingleDescent.liftHom_value F f φ

variable [(F.toDescentData (fun _ : PUnit.{1} => f)).Faithful]

example (e : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ≅
    (F.toDescentData (fun _ : PUnit.{1} => f)).obj N) :
    (F.toDescentData (fun _ : PUnit.{1} => f)).mapIso (SingleDescent.liftIso F f e) = e :=
  SingleDescent.map_liftIso F f e
