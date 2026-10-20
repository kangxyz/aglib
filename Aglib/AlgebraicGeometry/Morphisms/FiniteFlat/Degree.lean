/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.FieldMaps
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Basic

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Degree` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9f69df5ff4bebf382915949780f8be4c05deea63e6283dfad1529b205f635343`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Hom
universe u
theorem fieldPicard_eq_zero (K : Type u) [Field K] (a :
    Scheme.Modules.Invertible.PicardGroup (Spec (.of K))) : a = 0 := by
  induction a using Quotient.inductionOn with
  | h L =>
    obtain ⟨e⟩ := Scheme.Modules.Invertible.fieldLineBundle_trivial K L
    apply Quotient.sound
    exact ⟨e ≪≫ (coproductUniqueIso (fun _ : PUnit.{u + 1} ↦
      SheafOfModules.unit (Spec (.of K)).ringCatSheaf)).symm⟩

def finiteSchemeDegree (K : Type u) [Field K] {D : Scheme.{u}} (q : D ⟶ Spec (.of K)) : ℕ :=
  letI : Algebra K Γ(D, ⊤) := coordinateAlgebra K (Over.mk q)
  Module.finrank K Γ(D, ⊤)

@[simp] theorem finiteSchemeDegree_id (K : Type u) [Field K] : finiteSchemeDegree K (𝟙 (Spec
    (.of K))) = 1 := by
  let : Algebra K Γ(Spec (.of K), ⊤) := coordinateAlgebra K (Over.mk (𝟙 (Spec (.of K))))
  change Module.finrank K Γ(Spec (.of K), ⊤) = 1
  apply Module.finrank_of_bijective_algebraMap
  change Function.Bijective (((Scheme.ΓSpecIso (.of K)).inv ≫ (𝟙 (Spec (.of K)) : Scheme.Hom _
      _).appTop).hom)
  simpa using ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv

end AlgebraicGeometry.Scheme.Hom
