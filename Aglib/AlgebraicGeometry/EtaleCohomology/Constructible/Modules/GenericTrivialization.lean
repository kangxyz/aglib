/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteGaloisCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant

/-! # Actual finite Galois trivializations of finite-type module coefficients

A finite-type locally constant native module sheaf on a field spectrum is
constant after a produced finite Galois extension. Its value is the original
finitely generated module from its actual etale chart. No finiteness of the
underlying additive group, resizing, or coefficient-ring finiteness is used.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- An actual finite Galois field trivialization with the original finitely
generated module value and the original native module inverse image. -/
structure FiniteGaloisConstantTrivialization (K : Type u) [Field K]
    (F : ModuleSheaf R (Spec (.of K))) where
  /-- The finite Galois intermediate field of the separable closure. -/
  extension : FiniteGaloisIntermediateField K (SeparableClosure K)
  /-- The original constant module value, with its original universe. -/
  value : ModuleCat.{u + 1} R
  /-- Finite generation over the original coefficient ring. -/
  finite_value : Module.Finite R value
  /-- The actual module-valued constant trivialization. -/
  iso : (moduleInverseImage R (Spec.algebraMap K extension)).obj F ≅
    (constantSheaf (Spec (.of extension)).smallEtaleTopology
      (ModuleCat.{u + 1} R)).obj value

/-- The actual chart of a finite-type locally constant module coefficient
produces a finite Galois trivialization, without forgetting its scalars. -/
def finiteGaloisConstantTrivialization (K : Type u) [Field K]
    (F : ModuleSheaf R (Spec (.of K))) (hF : IsFiniteTypeLocallyConstant F) :
    FiniteGaloisConstantTrivialization K F := by
  apply Classical.choice
  obtain ⟨t⟩ := hF
  obtain ⟨i, y, _⟩ := t.covers (default : Spec (.of K))
  have : Etale (t.chart i).hom := (t.chart i).prop
  obtain ⟨L, s, hs⟩ := Fields.exists_finiteGalois_point K (t.chart i).hom y
  refine ⟨{ extension := L
            value := t.value i
            finite_value := t.finite_value i
            iso := ?_ }⟩
  exact eqToIso (congrArg (fun q => (moduleInverseImage R q).obj F) hs.symm) ≪≫
    (moduleInverseImageComp R (t.chart i).hom s).app F ≪≫
      (moduleInverseImage R s).mapIso (t.trivialization i) ≪≫
      (moduleInverseImageConstantIso R s).app (t.value i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
