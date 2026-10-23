/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Native affine algebra coordinates for a finite scheme over an affine base -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

variable (B : Type u) [CommRing B] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of B)) [IsFinite p]

/-- The actual structural algebra on the global sections of a finite source. -/
@[instance_reducible]
def finiteSourceAlgebra : Algebra B Γ(Y, ⊤) := by
  let : IsAffine Y := isAffine_of_isAffineHom p
  exact (Spec.preimage (Y.isoSpec.inv ≫ p)).hom.toAlgebra

/-- The coordinate map is the original structural map under the native affine
isomorphism, not a new finite-presentation model. -/
lemma finiteSource_spec_algebraMap :
    let : IsAffine Y := isAffine_of_isAffineHom p
    let := finiteSourceAlgebra B p
    Spec.algebraMap B Γ(Y, ⊤) = Y.isoSpec.inv ≫ p := by
  let : IsAffine Y := isAffine_of_isAffineHom p
  change Spec.map (Spec.preimage (Y.isoSpec.inv ≫ p)) = _
  exact Spec.map_preimage _

/-- The actual global-section algebra is finite over the original affine base. -/
theorem finiteSource_moduleFinite :
    let := finiteSourceAlgebra B p
    Module.Finite B Γ(Y, ⊤) := by
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  apply RingHom.finite_algebraMap.mp
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap B Γ(Y, ⊤)))).mp
  change IsFinite (Spec.algebraMap B Γ(Y, ⊤))
  rw [finiteSource_spec_algebraMap B p]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
