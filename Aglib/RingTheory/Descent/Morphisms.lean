/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Descent.Basic

/-! Morphisms and finite-etale properties of the constructed descent algebra.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.AlgebraDescentMorphisms` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`fc81a1cc3773e3d0219cd6f71fd0c7537f8a5b581c92cea9e87f1382f5b7f41e`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.TensorProduct

namespace Algebra.Descent

universe u v w w'
variable {R : Type u} {S : Type v} {B : Type w} {B' : Type w'}
variable [CommRing R] [CommRing S] [CommRing B] [CommRing B']
variable [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
variable [Algebra R B'] [Algebra S B'] [IsScalarTower R S B']

namespace Datum
variable (D : Datum R S B) (E : Datum R S B')

/-- A map of descent data is an actual algebra homomorphism commuting with the
coactions. -/
structure Hom where
  /-- The `S`-algebra homomorphism underlying a morphism of descent data. -/
  hom : B →ₐ[S] B'
  comm : E.coaction.comp hom =
    (Algebra.TensorProduct.map (AlgHom.id S S) (hom.restrictScalars R)).comp D.coaction

variable {D E}

namespace Hom
variable (f : D.Hom E)

lemma map_mem_invariants (a : D.invariants) : f.hom a ∈ E.invariants := by
  rw [E.mem_invariants]
  have h := congrArg (fun g : B →ₐ[S] S ⊗[R] B' => g a) f.comm
  change E.coaction (f.hom a) =
    Algebra.TensorProduct.map (AlgHom.id S S) (f.hom.restrictScalars R) (D.coaction a) at h
  rw [(D.mem_invariants a).1 a.property] at h
  simpa using h

/-- Restriction to the actual equalizer constructs the descended morphism. -/
def invariantsMap : D.invariants →ₐ[R] E.invariants :=
  ((f.hom.restrictScalars R).comp D.invariants.val).codRestrict E.invariants
    f.map_mem_invariants

@[simp] lemma invariantsMap_apply (a : D.invariants) :
    (f.invariantsMap a : B') = f.hom a := rfl

/-- The descended map pulls back to the original compatible morphism. -/
lemma baseChange_naturality :
    f.hom.comp D.baseChange = E.baseChange.comp
      (Algebra.TensorProduct.map (AlgHom.id S S) f.invariantsMap) := by
  ext a
  simp

/-- The explicit inclusion characterizes the descended morphism uniquely. -/
lemma invariantsMap_unique (g : D.invariants →ₐ[R] E.invariants)
    (hg : E.invariants.val.comp g = (f.hom.restrictScalars R).comp D.invariants.val) :
    g = f.invariantsMap := by
  ext a
  exact congrArg (fun h : D.invariants →ₐ[R] B' => h a) hg

end Hom

/-- Finite generation descends after the object has been explicitly constructed. -/
theorem invariants_finite [Module.FaithfullyFlat R S] [Module.Finite S B] :
    Module.Finite R D.invariants := by
  have : Module.Finite S (S ⊗[R] D.invariants) :=
    Module.Finite.equiv D.baseChangeEquiv.symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

/-- Etaleness descends for the explicit equalizer algebra. -/
theorem invariants_etale [Module.FaithfullyFlat R S] [Algebra.Etale S B] :
    Algebra.Etale R D.invariants := by
  have : Algebra.Etale S (S ⊗[R] D.invariants) :=
    Algebra.Etale.of_equiv D.baseChangeEquiv.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat S

end Datum
end Algebra.Descent
