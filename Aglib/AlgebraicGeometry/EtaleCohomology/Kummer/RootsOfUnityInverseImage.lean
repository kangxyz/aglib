/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsOfUnity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ZMod
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CoefficientBaseChange

/-!
# Inverse image of the module sheaf of roots of unity

For `Λ = ULift (ZMod n)`, every additive map between `Λ`-modules is `Λ`-linear, so forgetting
scalars from sheaves of modules over the constant ring sheaf `Λ_X` to abelian sheaves is full
(`moduleSheaf_uLiftZMod_toSheaf_full`; it is faithful in general). An isomorphism of underlying
abelian sheaves therefore lifts uniquely to an isomorphism of module sheaves.

For a morphism `j : U ⟶ X` (an open immersion, or any étale morphism, in the application) and
`0 < n` invertible on `X`, the native module inverse image of the module sheaf `μ_n` on `X` is the
module sheaf `μ_n` on `U` (`moduleRootsOfUnityInverseImageIso`): its underlying isomorphism is the
original underlying comparison `moduleInverseImageUnderlyingIso`, then the inverse image of
`moduleRootsOfUnityUnderlyingIso`, then the canonical roots comparison
`GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso : j^* μ_{n,X} ≅ μ_{n,U}`
(`moduleRootsOfUnityInverseImageIso_underlying`). This is `j^* μ_n ≅ μ_n` in `Sh(U_et, n)`, used
for the localization sequence of `μ_n` in the proof of Milne, *Lectures on Étale Cohomology*
v2.21, Thm. 14.7, Step 2, p. 94. The level hypotheses `0 < n` and `IsUnit (n : Γ(X, ⊤))` are those
of `rootsPullbackIso`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

attribute [local instance] hasSheafifyLarge hasSheafifyModules moduleForget_preservesSheafification

variable {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The native module inverse image of the module sheaf `μ_n` on `X` is the module sheaf `μ_n` on
`U`, lifting the composite of the original underlying comparison and the canonical roots
comparison `rootsPullbackIso`. -/
def moduleRootsOfUnityInverseImageIso :
    (moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity X n) ≅
      moduleRootsOfUnity U n :=
  letI := moduleSheaf_uLiftZMod_toSheaf_full U n
  (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).preimageIso
    ((moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) j).app (moduleRootsOfUnity X n) ≪≫
      (inverseImage j).mapIso (moduleRootsOfUnityUnderlyingIso X n) ≪≫
        rootsPullbackIso j n hn hinv ≪≫ (moduleRootsOfUnityUnderlyingIso U n).symm)

/-- The underlying isomorphism of `moduleRootsOfUnityInverseImageIso`, followed by the underlying
isomorphism to `μ_n` on `U`, is the original underlying comparison, the inverse image of the
underlying isomorphism to `μ_n` on `X`, and `rootsPullbackIso`. -/
theorem moduleRootsOfUnityInverseImageIso_underlying :
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).map
        (moduleRootsOfUnityInverseImageIso j n hn hinv).hom ≫
      (moduleRootsOfUnityUnderlyingIso U n).hom =
    (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) j).hom.app (moduleRootsOfUnity X n) ≫
      (inverseImage j).map (moduleRootsOfUnityUnderlyingIso X n).hom ≫
        (rootsPullbackIso j n hn hinv).hom := by
  let := moduleSheaf_uLiftZMod_toSheaf_full U n
  rw [moduleRootsOfUnityInverseImageIso, Functor.preimageIso_hom, Functor.map_preimage]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.EtaleCohomology
