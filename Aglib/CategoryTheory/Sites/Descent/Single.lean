/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Morphism descent between the original objects along one map

Full faithfulness of the original singleton descent functor lifts morphisms
and isomorphisms between its given objects. Its native preimage supplies the
whole-map and upstairs equations, uniqueness and composition. Native descent
pullback gives the base-change law. No descended object or equivalence inverse
is selected.
-/

@[expose] public noncomputable section

open Opposite

namespace CategoryTheory.Pseudofunctor.SingleDescent

universe v u v' u'

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {Y Z : C} (f : Y ⟶ Z)
  [(F.toDescentData (fun _ : PUnit.{1} => f)).Full]
  {M N P : F.obj (.mk (op Z))}

/-- Lift the given descent morphism between the same original objects. -/
def liftHom (φ : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ⟶
    (F.toDescentData (fun _ : PUnit.{1} => f)).obj N) : M ⟶ N :=
  (F.toDescentData (fun _ : PUnit.{1} => f)).preimage φ

/-- The whole original descent morphism is recovered. -/
theorem map_liftHom (φ : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ⟶
    (F.toDescentData (fun _ : PUnit.{1} => f)).obj N) :
    (F.toDescentData (fun _ : PUnit.{1} => f)).map (liftHom F f φ) = φ :=
  (F.toDescentData (fun _ : PUnit.{1} => f)).map_preimage φ

/-- The lifted morphism has the given value on the original covering object. -/
theorem liftHom_value (φ : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ⟶
    (F.toDescentData (fun _ : PUnit.{1} => f)).obj N) :
    (F.map f.op.toLoc).toFunctor.map (liftHom F f φ) = φ.hom PUnit.unit :=
  congrArg (fun a => a.hom PUnit.unit) (map_liftHom F f φ)

variable [(F.toDescentData (fun _ : PUnit.{1} => f)).Faithful]

/-- The upstairs value determines the morphism between these original objects. -/
theorem liftHom_unique (φ : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ⟶
    (F.toDescentData (fun _ : PUnit.{1} => f)).obj N) (ψ : M ⟶ N)
    (hψ : (F.map f.op.toLoc).toFunctor.map ψ = φ.hom PUnit.unit) :
    ψ = liftHom F f φ := by
  apply (F.toDescentData (fun _ : PUnit.{1} => f)).map_injective
  rw [map_liftHom]
  apply DescentData.hom_ext
  intro i
  cases i
  exact hψ

/-- Identity is preserved on the same original object. -/
@[simp]
theorem liftHom_id : liftHom F f (𝟙 ((F.toDescentData
    (fun _ : PUnit.{1} => f)).obj M)) = 𝟙 M :=
  (F.toDescentData (fun _ : PUnit.{1} => f)).preimage_id

/-- Composition is preserved before evaluating any transition. -/
theorem liftHom_comp
    (φ : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ⟶
      (F.toDescentData (fun _ : PUnit.{1} => f)).obj N)
    (ψ : (F.toDescentData (fun _ : PUnit.{1} => f)).obj N ⟶
      (F.toDescentData (fun _ : PUnit.{1} => f)).obj P) :
    liftHom F f (φ ≫ ψ) = liftHom F f φ ≫ liftHom F f ψ :=
  (F.toDescentData (fun _ : PUnit.{1} => f)).preimage_comp φ ψ

/-- Lift an isomorphism without choosing another realization of either object. -/
def liftIso (e : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ≅
    (F.toDescentData (fun _ : PUnit.{1} => f)).obj N) : M ≅ N :=
  (F.toDescentData (fun _ : PUnit.{1} => f)).preimageIso e

/-- The complete original isomorphism is recovered by the same descent functor. -/
theorem map_liftIso (e : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ≅
    (F.toDescentData (fun _ : PUnit.{1} => f)).obj N) :
    (F.toDescentData (fun _ : PUnit.{1} => f)).mapIso (liftIso F f e) = e := by
  apply Iso.ext
  exact map_liftHom F f e.hom

section BaseChange

variable {Y' Z' : C} (f' : Y' ⟶ Z') (p : Z' ⟶ Z) (a : Y' ⟶ Y)
  (w : a ≫ f = f' ≫ p)
  [(F.toDescentData (fun _ : PUnit.{1} => f')).Full]
  [(F.toDescentData (fun _ : PUnit.{1} => f')).Faithful]

omit [(F.toDescentData (fun _ : PUnit.{1} => f)).Faithful] in
/-- The original base-change map is the unique lift of the original pulled descent morphism. -/
theorem liftHom_baseChange
    (φ : (F.toDescentData (fun _ : PUnit.{1} => f)).obj M ⟶
      (F.toDescentData (fun _ : PUnit.{1} => f)).obj N) :
    (F.map p.op.toLoc).toFunctor.map (liftHom F f φ) =
      liftHom F f'
        (((DescentData.toDescentDataCompPullFunctorIso F
          (f := fun _ : PUnit.{1} => f) (f' := fun _ : PUnit.{1} => f')
          (p := p) (p' := fun _ : PUnit.{1} => a)
          (α := fun _ : PUnit.{1} => PUnit.unit) (fun _ : PUnit.{1} => w)).app M).inv ≫
          (DescentData.pullFunctor F
          (f := fun _ : PUnit.{1} => f) (f' := fun _ : PUnit.{1} => f')
          (p := p) (p' := fun _ : PUnit.{1} => a) (α := fun _ : PUnit.{1} => PUnit.unit)
            (fun _ : PUnit.{1} => w)).map φ ≫
          ((DescentData.toDescentDataCompPullFunctorIso F
          (f := fun _ : PUnit.{1} => f) (f' := fun _ : PUnit.{1} => f')
          (p := p) (p' := fun _ : PUnit.{1} => a)
            (α := fun _ : PUnit.{1} => PUnit.unit) (fun _ : PUnit.{1} => w)).app N).hom) := by
  let θ := DescentData.toDescentDataCompPullFunctorIso F
          (f := fun _ : PUnit.{1} => f) (f' := fun _ : PUnit.{1} => f')
          (p := p) (p' := fun _ : PUnit.{1} => a)
    (α := fun _ : PUnit.{1} => PUnit.unit) (fun _ : PUnit.{1} => w)
  apply (F.toDescentData (fun _ : PUnit.{1} => f')).map_injective
  rw [map_liftHom]
  change (F.toDescentData (fun _ : PUnit.{1} => f')).map
      ((F.map p.op.toLoc).toFunctor.map (liftHom F f φ)) =
    (θ.app M).inv ≫
      (DescentData.pullFunctor F
        (f := fun _ : PUnit.{1} => f) (f' := fun _ : PUnit.{1} => f')
        (p := p) (p' := fun _ : PUnit.{1} => a)
        (α := fun _ : PUnit.{1} => PUnit.unit) (fun _ : PUnit.{1} => w)).map φ ≫
      (θ.app N).hom
  have h := θ.hom.naturality (liftHom F f φ)
  change (DescentData.pullFunctor F
          (f := fun _ : PUnit.{1} => f) (f' := fun _ : PUnit.{1} => f')
          (p := p) (p' := fun _ : PUnit.{1} => a) (α := fun _ : PUnit.{1} => PUnit.unit)
      (fun _ : PUnit.{1} => w)).map
        ((F.toDescentData (fun _ : PUnit.{1} => f)).map (liftHom F f φ)) ≫
      (θ.app N).hom =
    (θ.app M).hom ≫ (F.toDescentData (fun _ : PUnit.{1} => f')).map
      ((F.map p.op.toLoc).toFunctor.map (liftHom F f φ)) at h
  rw [map_liftHom] at h
  apply (cancel_epi (θ.app M).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h.symm

end BaseChange

end CategoryTheory.Pseudofunctor.SingleDescent
