/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Local bijectivity from covering tests

For a property of objects that covers every object, componentwise injectivity
or surjectivity on those objects implies the corresponding local property.
-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ D} (a : P ⟶ Q)

namespace Presheaf

/-- Injectivity on a covering property of objects implies local injectivity. -/
theorem isLocallyInjective_of_injective_on_cover (B : ObjectProperty C)
    (hB : ∀ U : C, Sieve.generate (fun {V} (_ : V ⟶ U) => B V) ∈ J U)
    (h : ∀ U : C, B U → Function.Injective (a.app (op U))) :
    IsLocallyInjective J a where
  equalizerSieve_mem {U} x y hxy := by
    refine J.superset_covering ?_ (hB U.unop)
    rw [Sieve.generate_le_iff]
    intro V g hV
    change P.map g.op x = P.map g.op y
    apply h V hV
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

/-- Surjectivity on a covering property of objects implies local surjectivity. -/
theorem isLocallySurjective_of_surjective_on_cover (B : ObjectProperty C)
    (hB : ∀ U : C, Sieve.generate (fun {V} (_ : V ⟶ U) => B V) ∈ J U)
    (h : ∀ U : C, B U → Function.Surjective (a.app (op U))) :
    IsLocallySurjective J a where
  imageSieve_mem {U} x := by
    refine J.superset_covering ?_ (hB U)
    rw [Sieve.generate_le_iff]
    intro V g hV
    exact h V hV (Q.map g.op x)

end Presheaf

end CategoryTheory
