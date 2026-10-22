/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Sheaf.Units
public import Aglib.RingTheory.Ideal.SquareZeroUnits
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local lifting of units through square-zero ring-sheaf quotients

An actual locally surjective ring-sheaf map with square-zero section kernels
induces a locally surjective map on its native sheaves of units. The proof
lifts a unit and its inverse on the intersection of their two covering sieves;
it does not assume surjectivity on sections over every object.

This supplies local unit lifting for the Picard square-zero obstruction sequence.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Units lift locally through a locally surjective square-zero ring quotient. -/
theorem unitsMap_isLocallySurjective {R S : Sheaf J CommRingCat.{w}}
    (f : R ⟶ S) [Presheaf.IsLocallySurjective J f.hom]
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    Presheaf.IsLocallySurjective J (unitsMap f).hom where
  imageSieve_mem {U} s := by
    change Additive ((S.obj.obj (op U))ˣ) at s
    let s0 : (S.obj.obj (op U))ˣ := s.toMul
    let a : S.obj.obj (op U) := s0.val
    let b : S.obj.obj (op U) := (s0⁻¹).val
    let T := Presheaf.imageSieve f.hom a ⊓ Presheaf.imageSieve f.hom b
    have hT : T ∈ J U := J.intersection_covering
      (Presheaf.imageSieve_mem J f.hom a) (Presheaf.imageSieve_mem J f.hom b)
    refine J.superset_covering ?_ hT
    intro V g hg
    obtain ⟨x, hx⟩ := hg.1
    obtain ⟨y, hy⟩ := hg.2
    let sV : (S.obj.obj (op V))ˣ :=
      Units.map ((S.obj.map g.op).hom : S.obj.obj (op U) →* S.obj.obj (op V)) s0
    have hx' : (f.hom.app (op V)).hom x = (sV : S.obj.obj (op V)) := hx
    have hy' : (f.hom.app (op V)).hom y = (sV⁻¹ : (S.obj.obj (op V))ˣ) := hy
    have hxunit : IsUnit x := (f.hom.app (op V)).hom.isUnit_of_unit_and_inv_lift
      (hf (op V)) sV hx' hy'
    refine ⟨Additive.ofMul hxunit.unit, ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    change (f.hom.app (op V)).hom (hxunit.unit : R.obj.obj (op V)) =
      (S.obj.map g.op).hom s0.val
    rw [hxunit.unit_spec]
    exact hx

end CategoryTheory.Sheaf
