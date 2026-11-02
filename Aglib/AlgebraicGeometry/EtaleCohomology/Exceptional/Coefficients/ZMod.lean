/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.ZMod

/-!
# Full scalar forgetting for small-etale lifted ZMod coefficients

These are native specializations of `ModuleCat.Sheaf.ConstantRing.ZMod` on the
actual small-etale site, for every modulus. The original coefficient equivalence
supplies the comparison. Unit and root inverse-image adapters share this provider.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules moduleForget_preservesSheafification

/-- Every additive map between `ULift (ZMod n)`-modules is linear: forgetting scalars is full. -/
theorem moduleCat_uLiftZMod_forget₂_full (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}).Full :=
  ModuleCat.uLiftZMod_forget₂_full n

/-- Forgetting scalars from sheaves of modules over the constant ring sheaf `ℤ/n` is full. -/
theorem moduleSheaf_uLiftZMod_toSheaf_full (X : Scheme.{u}) (n : ℕ) :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X (ULift.{u + 1} (ZMod n)))).Full :=
  ModuleCat.Sheaf.ConstantRing.uLiftZMod_toSheaf_full.{u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) n

end AlgebraicGeometry.Scheme.EtaleCohomology
