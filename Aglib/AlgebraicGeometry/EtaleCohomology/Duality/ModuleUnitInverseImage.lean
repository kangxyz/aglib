/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ModuleUnitUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsOfUnityInverseImage

/-!
# Inverse image of the rank-one module sheaf `ℤ/n`

For `Λ = ULift (ZMod n)` and any morphism `j : U ⟶ X`, the native module inverse image of the
rank-one module sheaf `Λ_X` is `Λ_U` (`moduleUnitInverseImageIso`). Since forgetting scalars is
full for `ℤ/n`-modules (`moduleSheaf_uLiftZMod_toSheaf_full`), the isomorphism is the lift of the
composite of the original underlying comparison `moduleInverseImageUnderlyingIso`, the inverse
image of `moduleUnitUnderlyingIso` on `X`, the original constant-sheaf comparison
`inverseImageConstantIso`, and `moduleUnitUnderlyingIso` on `U`
(`moduleUnitInverseImageIso_underlying`). For an open `V ⊆ U` it identifies the first term
`jV_! jV^* (ℤ/n)` of the localization sequence on `U` with `jV_! (ℤ/n)`, as in Milne, *Lectures on
Étale Cohomology* v2.21, Thm. 14.7, proof, Step 2, p. 94. Every `n` is allowed.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ)

/-- The native module inverse image of the rank-one module sheaf `ℤ/n` is `ℤ/n`. -/
def moduleUnitInverseImageIso :
    (moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit X (ULift.{u + 1} (ZMod n))) ≅
      moduleUnit U (ULift.{u + 1} (ZMod n)) :=
  letI := moduleSheaf_uLiftZMod_toSheaf_full U n
  (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).preimageIso
    ((moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) j).app
        (moduleUnit X (ULift.{u + 1} (ZMod n))) ≪≫
      (inverseImage j).mapIso (moduleUnitUnderlyingIso X (ULift.{u + 1} (ZMod n))).symm ≪≫
        (inverseImageConstantIso j).app (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ≪≫
          moduleUnitUnderlyingIso U (ULift.{u + 1} (ZMod n)))

/-- The underlying isomorphism of `moduleUnitInverseImageIso` is the original underlying
comparison, the inverse image of `moduleUnitUnderlyingIso` on `X`, the constant-sheaf comparison
`inverseImageConstantIso`, and `moduleUnitUnderlyingIso` on `U`. -/
theorem moduleUnitInverseImageIso_underlying :
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).map
        (moduleUnitInverseImageIso j n).hom =
      (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) j).hom.app
          (moduleUnit X (ULift.{u + 1} (ZMod n))) ≫
        (inverseImage j).map (moduleUnitUnderlyingIso X (ULift.{u + 1} (ZMod n))).inv ≫
          (inverseImageConstantIso j).hom.app (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ≫
            (moduleUnitUnderlyingIso U (ULift.{u + 1} (ZMod n))).hom := by
  let := moduleSheaf_uLiftZMod_toSheaf_full U n
  rw [moduleUnitInverseImageIso, Functor.preimageIso_hom, Functor.map_preimage]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]

end AlgebraicGeometry.Scheme.EtaleCohomology
