/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Descent.Ideal

/-! Focused consumer of faithfully flat descent of ideals (the affine case
of Nitsure, arXiv:math/0504590v1, Lemma 6.7(2)). The hypotheses are Mathlib's `Module.Flat`,
`Module.FaithfullyFlat` and `RingHom.FaithfullyFlat`; the descent condition is equality of the two
extensions of `J` along `Algebra.TensorProduct.includeLeft` and `includeRight`. -/

@[expose] public section

open TensorProduct CategoryTheory

universe u

section

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

example [Module.Flat A B] (J : Ideal B) :
    (J.comap (algebraMap A B)).map (algebraMap A B) =
      (J.map (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).comap
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) :=
  Ideal.map_comap_algebraMap_eq_comap_includeLeft_map_includeRight J

example [Module.FaithfullyFlat A B] (J : Ideal B)
    (hJ : J.map (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) =
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)) :
    ∃! I : Ideal A, I.map (algebraMap A B) = J :=
  Ideal.existsUnique_map_algebraMap_eq_of_faithfullyFlat J hJ

/-- The descent condition characterizes the extended ideals. -/
example [Module.FaithfullyFlat A B] (J : Ideal B) :
    (∃ I : Ideal A, I.map (algebraMap A B) = J) ↔
      J.map (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) =
        J.map (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) :=
  Ideal.exists_map_algebraMap_eq_iff_map_includeLeft_eq_map_includeRight J

end

/-- The pushout form, as consumed by the global sections of a fibre product of affine schemes. -/
example {A B C : CommRingCat.{u}} {φ : A ⟶ B} {i₁ i₂ : B ⟶ C} (hφ : φ.hom.FaithfullyFlat)
    (h : IsPushout φ φ i₁ i₂) (J : Ideal B) (hJ : J.map i₁.hom = J.map i₂.hom) :
    (J.comap φ.hom).map φ.hom = J :=
  Ideal.map_comap_eq_self_of_isPushout hφ h J hJ

/-- info: 'Ideal.map_comap_algebraMap_eq_comap_includeLeft_map_includeRight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.map_comap_algebraMap_eq_comap_includeLeft_map_includeRight

/-- info: 'Ideal.map_comap_algebraMap_eq_self_of_faithfullyFlat' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.map_comap_algebraMap_eq_self_of_faithfullyFlat

/-- info: 'Ideal.existsUnique_map_algebraMap_eq_of_faithfullyFlat' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.existsUnique_map_algebraMap_eq_of_faithfullyFlat

/-- info: 'Ideal.map_includeLeft_map_algebraMap_eq_map_includeRight' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.map_includeLeft_map_algebraMap_eq_map_includeRight

/-- info: 'Ideal.exists_map_algebraMap_eq_iff_map_includeLeft_eq_map_includeRight' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.exists_map_algebraMap_eq_iff_map_includeLeft_eq_map_includeRight

/-- info: 'Ideal.map_comap_eq_self_of_isPushout' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.map_comap_eq_self_of_isPushout
