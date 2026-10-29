/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsOfUnity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
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

/-- Every additive map between `ULift (ZMod n)`-modules is linear: forgetting scalars is full. -/
theorem moduleCat_uLiftZMod_forget₂_full (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}).Full where
  map_surjective {M N} f := by
    let g : M →+ N := f.hom
    refine ⟨ModuleCat.ofHom { toFun := g, map_add' := g.map_add, map_smul' := fun r m => ?_ },
      rfl⟩
    obtain ⟨z, rfl⟩ : ∃ z : ℤ, (z : ULift.{u + 1} (ZMod n)) = r :=
      ⟨ZMod.cast r.down, ULift.ext _ _
        ((ULift.down_intCast _).trans (ZMod.intCast_zmod_cast r.down))⟩
    simpa using map_intCast_smul g (ULift.{u + 1} (ZMod n)) (ULift.{u + 1} (ZMod n)) z m

/-- Forgetting scalars from sheaves of modules over the constant ring sheaf `ℤ/n` is full. -/
theorem moduleSheaf_uLiftZMod_toSheaf_full (X : Scheme.{u}) (n : ℕ) :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X (ULift.{u + 1} (ZMod n)))).Full := by
  let := moduleCat_uLiftZMod_forget₂_full.{u} n
  exact Functor.Full.of_iso (moduleSheafInverseUnderlyingIso X (ULift.{u + 1} (ZMod n)))

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
