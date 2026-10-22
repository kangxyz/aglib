/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Enlargement
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Subobjects.Preimage
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Subobjects.Gluing
public import Aglib.AlgebraicGeometry.Modules.Coherent.Gluing

/-!
# Affine extension and enlargement of coherent subobjects

A finite-type open subobject extends inside a quasicoherent sheaf on a Noetherian affine scheme.
One additional Noetherian affine chart enlarges an existing finite-type region while preserving
the given restriction isomorphism.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/AffineExtension.lean`.
SHA-256: `f3123846564192b4dd5bfc1e9fb14e7320fe197db62e2aa0f411e4b547a3f5a6`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/AffineEnlargement.lean`.
SHA-256: `1c66fc512c3d458b75d6297240bf629f19f1a3df85c2240579d5c7d8f4c97986`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- A coherent subobject on an arbitrary open of a noetherian affine
scheme extends to a coherent subobject of its actual quasicoherent ambient. -/
theorem affineLocallyFiniteType_subobject_extension_affine
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    {U : Scheme.{u}} [IsLocallyNoetherian U]
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (A : FiniteTypeSheaves U) (a : A.obj ⟶ M.restrict j) [Mono a] :
    ∃ (B : FiniteTypeSheaves (Spec R)) (b : B.obj ⟶ M), Mono b ∧
      ∃ (e : B.obj.restrict j ≅ A.obj),
        (Scheme.Modules.restrictFunctor j).map b = e.hom ≫ a := by
  exact affineLocallyFiniteType_subobject_extension_affine_of_quasiCompact R j M A a

/-- A global quasicoherent sheaf coherent on `W` has a quasicoherent
subsheaf equal to it on `W` and coherent on the union of `W` with one affine
chart. This is the actual finite-cover induction step. -/
theorem affineLocallyFiniteType_affine_enlargement
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (N : X.Modules) [N.IsQuasicoherent] (W : X.Opens)
    (hW : affineLocallyFiniteType W.toScheme (N.restrict W.ι))
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (a : Spec R ⟶ X) [IsOpenImmersion a] :
    ∃ (N' : X.Modules) (s : N' ⟶ N), N'.IsQuasicoherent ∧ Mono s ∧
      IsIso ((Scheme.Modules.restrictFunctor W.ι).map s) ∧
      affineLocallyFiniteType (W ⊔ a.opensRange).toScheme (N'.restrict (W ⊔ a.opensRange).ι) := by
  exact affineLocallyFiniteType_affine_enlargement_of_quasiCompact N W hW R a

end AlgebraicGeometry.Scheme.Modules.Coherent
