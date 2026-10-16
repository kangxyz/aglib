/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The generic point and its function-field inclusion

The canonical map is `X.fromSpecStalk (genericPoint X)`. Its image point, nonempty-open
inverse images, quasi-compactness and actual section comparison use only integrality of X.
The function field, germ map and fraction-ring interface are reused from Mathlib.

## Extraction basis

Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/GenericFullFaithfulness.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`56316f6517043fcd7e709e55d04765986ce74140b7d0d4e98e59a4648ec25c47`.
The source statements, binder universes, hypotheses and chosen maps are retained.
Direct Mathlib carriers/maps replace the recorded source wrappers; source-token correspondence
and those definitional substitutions are separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- Every point of the function-field spectrum maps to the generic point. -/
theorem fromSpecStalk_genericPoint_apply (p : Spec X.functionField) :
    (X.fromSpecStalk (genericPoint X)) p = genericPoint X := by
  letI : Subsingleton (Spec X.functionField) := inferInstanceAs (Subsingleton (PrimeSpectrum
      X.functionField))
  have hp : p = closedPoint X.functionField := Subsingleton.elim _ _
  rw [hp]
  exact Scheme.fromSpecStalk_closedPoint

/-- The inverse image of every nonempty open is the entire function-field spectrum. -/
theorem fromSpecStalk_genericPoint_preimage (U : X.Opens) [Nonempty U] :
    (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U = ⊤ := by
  apply top_le_iff.mp
  intro p _
  change (X.fromSpecStalk (genericPoint X)) p ∈ U
  rw [fromSpecStalk_genericPoint_apply]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- The canonical map from the function-field spectrum is quasi-compact. -/
instance instQuasiCompactFromSpecStalkGenericPoint : QuasiCompact (X.fromSpecStalk (genericPoint X))
    where
  isCompact_preimage U _ _ := by
    letI : Subsingleton (Spec X.functionField) := inferInstanceAs (Subsingleton (PrimeSpectrum
        X.functionField))
    exact (Set.toFinite _).isCompact

/-- The actual sections of a nonempty generic inverse image retain the
original field and its literal germ map. -/
def functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) ≅ X.functionField :=
  (Spec X.functionField).presheaf.mapIso
    (eqToIso (fromSpecStalk_genericPoint_preimage X U).symm).op ≪≫ Scheme.ΓSpecIso _

/-- The canonical section comparison identifies the generic-inclusion map with the germ map. -/
theorem fromSpecStalk_genericPoint_app_functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    (X.fromSpecStalk (genericPoint X)).app U ≫ (functionFieldSectionsIso X U).hom =
      X.germToFunctionField U := by
  dsimp [functionFieldSectionsIso]
  rw [Scheme.fromSpecStalk_app
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))]
  simp only [Category.assoc]
  rw [← (Spec X.functionField).presheaf.map_comp_assoc]
  have he : (homOfLE le_top).op ≫
      (eqToHom (fromSpecStalk_genericPoint_preimage X U).symm).op = 𝟙 (op ⊤) := by
    apply Subsingleton.elim
  rw [he]
  simp

end AlgebraicGeometry.Scheme
