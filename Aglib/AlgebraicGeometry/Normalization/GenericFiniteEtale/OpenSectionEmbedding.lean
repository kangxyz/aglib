/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericPullback

/-! # Original function-field embeddings from an actual open lift

An actual map from the original open to the unchanged covering scheme gives
an original generic-fibre point. The native generic-fibre isomorphism and
Spec fullness construct the field embedding with its original coefficient
action. No dominance of the supplied lift or normalization base change is
assumed; no replacement field is selected.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X X' U : Scheme.{u}} [IsIntegral X] [IsIntegral X'] [IsIntegral U]
  (j : U ⟶ X') [IsOpenImmersion j] (g : U ⟶ X) [IsDominant g]
  (Y : Scheme.FiniteEtale X) [IsIntegral Y.obj.left]

/-- A genuine lift on the original open constructs an embedding of the
original covering field into the original ambient function field, with the
actual coefficient action. No generic comparison or dominant lift is input. -/
theorem exists_generic_embedding_of_open_lift
    (a : U ⟶ Y.obj.left) (ha : a ≫ Y.obj.hom = g) :
    letI := baseChangeFieldAlgebra j g
    letI := GenericGalois.algebra Y
    Nonempty (Y.obj.left.functionField →ₐ[X.functionField] X'.functionField) := by
  let := baseChangeFieldAlgebra j g
  let := GenericGalois.algebra Y
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  let K := X.functionField
  let F := X'.functionField
  let L := Y.obj.left.functionField
  let e := originalGenericFibreIso Y
  have h : (openGenericMap j ≫ a) ≫ Y.obj.hom =
      Spec.algebraMap K F ≫ X.fromSpecStalk (genericPoint X) := by
    rw [Category.assoc, ha]
    exact openGenericMap_generic j g
  let t := pullback.lift (openGenericMap j ≫ a) (Spec.algebraMap K F) h
  let v : Spec F ⟶ Spec L := t ≫ e.inv
  have he : e.inv ≫ Spec.algebraMap K L =
      pullback.snd Y.obj.hom (X.fromSpecStalk (genericPoint X)) := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (originalGenericFibreIso_hom_snd Y).symm
  have hv : v ≫ Spec.algebraMap K L = Spec.algebraMap K F := by
    dsimp only [v]
    rw [Category.assoc, he]
    exact pullback.lift_snd _ _ _
  obtain ⟨φ, hφ⟩ := Spec.map_surjective v
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap K L) ≫ φ) =
      Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    rw [Spec.map_comp, hφ]
    exact hv
  have hc := Spec.map_injective hmap
  refine ⟨{ φ.hom with commutes' := ?_ }⟩
  intro k
  exact congrArg (fun q : K ⟶ F => q k) hc

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
