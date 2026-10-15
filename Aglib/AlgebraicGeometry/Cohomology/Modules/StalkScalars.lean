/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Support.Finite
public import Mathlib.Algebra.Category.ModuleCat.Stalk
/-!
# Canonical native-stalk scalars for finite-support cohomology

The native module stalk and `moduleAdditiveStalk` have the same underlying
abelian group. Their base-field module structures are proved equal: the
endomorphism induced by `moduleScalar` acts on each germ by the structural
constant germ, which is the native stalk-module action. Every element is a
germ, so this computes the action on the entire stalk.

The identity linear equivalence records both module structures explicitly.
It preserves actual germs and coefficient maps. Equality of module structures
also preserves finiteness and finrank. These statements hold for every module
sheaf and point on an arbitrary scheme over a field.

The structure-stalk action is Mathlib's native presheaf-of-modules action,
instantiated explicitly at `M.val`, at revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The load-bearing native results are
`PresheafOfModules.germ_smul`, `TopCat.Presheaf.exists_germ_eq`, and naturality
of the actual additive stalk map. The constants formula is the structural map
followed by the actual top germ and agrees definitionally with the reported
common-field scalar formula. The source owner remains generic cohomology.

The existing `FiniteSupport` and `Skyscraper` leaves are unchanged. Applying
this bridge to singular quotient modules still needs their actual support and
native quotient-stalk dictionary. Proper H1 finiteness is a separate obligation.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.FiniteSupportScalars` at R5Lab
  revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {k : Type u} [Field k]

/-- The native action of the structure-sheaf stalk on the module-sheaf stalk. -/
abbrev nativeModuleStalkStructure (X : Scheme.{u}) (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  inferInstanceAs (Module (X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.carrier) M.val.presheaf x))

/-- The structural base-field map to a local ring, obtained by taking germs. -/
def moduleStalkConstants (X : FScheme k) (x : X.left) : k →+* X.left.presheaf.stalk x :=
  (X.left.presheaf.germ ⊤ x trivial).hom.comp (constants X)

theorem moduleStalkConstants_eq_structural (X : FScheme k) (x : X.left) :
    moduleStalkConstants X x = (X.left.presheaf.germ ⊤ x trivial).hom.comp
      (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) := rfl

/-- The structural base-field action on the native module-sheaf stalk. -/
abbrev nativeModuleStalkModule (X : FScheme k) (M : X.left.Modules) (x : X.left) :
    Module k (M.presheaf.stalk x) :=
  letI := nativeModuleStalkStructure X.left M x
  Module.compHom _ (moduleStalkConstants X x)

theorem moduleStalkConstants_germ (X : FScheme k) (x : X.left)
    (U : X.left.Opens) (hx : x ∈ U) (a : k) :
    X.left.presheaf.germ U x hx (constantSection X U a) = moduleStalkConstants X x a := by
  exact X.left.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) x hx _

theorem moduleAdditiveStalk_smul_germ (X : FScheme k) (M : X.left.Modules) (x : X.left)
    (U : X.left.Opens) (hx : x ∈ U) (a : k) (s : M.val.obj (op U)) :
    a • (show moduleAdditiveStalk X M x from M.presheaf.germ U x hx s) =
      M.presheaf.germ U x hx (constantSection X U a • s) := by
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (moduleScalar X M a).hom) (M.presheaf.germ U x hx s) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

theorem moduleAdditiveStalk_smul_eq_native (X : FScheme k) (M : X.left.Modules)
    (x : X.left) (a : k) (s : moduleAdditiveStalk X M x) :
    a • s = @SMul.smul k (M.presheaf.stalk x)
      (nativeModuleStalkModule X M x).toSMul a s := by
  obtain ⟨U, hx, t, rfl⟩ := M.presheaf.exists_germ_eq s
  rw [moduleAdditiveStalk_smul_germ]
  change M.presheaf.germ U x hx (constantSection X U a • t) =
    @SMul.smul (X.left.presheaf.stalk x) (M.presheaf.stalk x)
      (nativeModuleStalkStructure X.left M x).toSMul
      (moduleStalkConstants X x a) (M.presheaf.germ U x hx t)
  erw [_root_.PresheafOfModules.germ_smul M.val x U hx]
  congr 1
  exact moduleStalkConstants_germ X x U hx a

theorem nativeModuleStalk_germ_smul (X : FScheme k) (M : X.left.Modules) (x : X.left)
    (U : X.left.Opens) (hx : x ∈ U) (a : k) (s : M.val.obj (op U)) :
    @SMul.smul k (M.presheaf.stalk x) (nativeModuleStalkModule X M x).toSMul a
        (M.presheaf.germ U x hx s) =
      M.presheaf.germ U x hx (constantSection X U a • s) :=
  (moduleAdditiveStalk_smul_eq_native X M x a _).symm.trans
    (moduleAdditiveStalk_smul_germ X M x U hx a s)

theorem moduleAdditiveStalkModule_eq_native (X : FScheme k) (M : X.left.Modules) (x : X.left) :
    moduleAdditiveStalkModule X M x = nativeModuleStalkModule X M x := by
  apply Module.ext
  funext a s
  exact moduleAdditiveStalk_smul_eq_native X M x a s

/-- The identity comparison between the native and additive-functor stalk actions. -/
def nativeModuleStalkLinearEquiv (X : FScheme k) (M : X.left.Modules) (x : X.left) :
    @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _
      (M.presheaf.stalk x) (moduleAdditiveStalk X M x) _ _
      (nativeModuleStalkModule X M x) (moduleAdditiveStalkModule X M x) := by
  letI := nativeModuleStalkModule X M x
  exact {
    toFun := fun s => s
    invFun := fun s => s
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a s => (moduleAdditiveStalk_smul_eq_native X M x a s).symm }

theorem nativeModuleStalkLinearEquiv_apply (X : FScheme k)
    (M : X.left.Modules) (x : X.left) (s : M.presheaf.stalk x) :
    nativeModuleStalkLinearEquiv X M x s = s := rfl

theorem nativeModuleStalkLinearEquiv_naturality (X : FScheme k)
    {M N : X.left.Modules} (f : M ⟶ N) (x : X.left) (s : M.presheaf.stalk x) :
    nativeModuleStalkLinearEquiv X N x
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.mapPresheaf) s) =
      moduleAdditiveStalkMap X f x (nativeModuleStalkLinearEquiv X M x s) := rfl

theorem nativeModuleStalkLinearEquiv_germ (X : FScheme k)
    (M : X.left.Modules) (x : X.left) (U : X.left.Opens) (hx : x ∈ U)
    (s : M.val.obj (op U)) :
    nativeModuleStalkLinearEquiv X M x (M.presheaf.germ U x hx s) =
      M.presheaf.germ U x hx s := rfl

theorem moduleAdditiveStalk_finrank_eq_native (X : FScheme k) (M : X.left.Modules) (x : X.left) :
    Module.finrank k (moduleAdditiveStalk X M x) =
      @Module.finrank k (M.presheaf.stalk x) _ _ (nativeModuleStalkModule X M x) := by
  change @Module.finrank k (M.presheaf.stalk x) _ _ (moduleAdditiveStalkModule X M x) = _
  rw [moduleAdditiveStalkModule_eq_native]

theorem moduleAdditiveStalk_finite_iff_native (X : FScheme k) (M : X.left.Modules) (x : X.left) :
    Module.Finite k (moduleAdditiveStalk X M x) ↔
      @Module.Finite k (M.presheaf.stalk x) _ _ (nativeModuleStalkModule X M x) := by
  change @Module.Finite k (M.presheaf.stalk x) _ _ (moduleAdditiveStalkModule X M x) ↔ _
  rw [moduleAdditiveStalkModule_eq_native]

end AlgebraicGeometry.Scheme.Cohomology

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {K : Type u} [Field K] (X : FScheme K)

-- Use the original native stalk-ring action through its explicit wrapper.
attribute [local instance] nativeModuleStalkStructure

/-- The action on the additive stalk is multiplication by the actual constant germ. -/
theorem moduleAdditiveStalk_smul_eq_constantGerm (M : X.left.Modules)
    (x : X.left) (a : K) (m : moduleAdditiveStalk X M x) :
    a • m = X.left.presheaf.germ ⊤ x trivial (constants X a) •
      (show M.presheaf.stalk x from m) := by
  obtain ⟨U, hx, s, rfl⟩ := M.presheaf.exists_germ_eq m
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (moduleScalar X M a).hom) (M.presheaf.germ U x hx s) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change M.presheaf.germ U x hx (constantSection X U a • s) = _
  have hconst : X.left.presheaf.germ U x hx (constantSection X U a) =
      X.left.presheaf.germ ⊤ x trivial (constants X a) := by
    exact X.left.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) x hx _
  erw [_root_.PresheafOfModules.germ_smul M.val x U hx]
  exact congrArg (fun r : X.left.presheaf.stalk x => r • M.presheaf.germ U x hx s) hconst

/-- Equality of the two actual field-module structures on a module-sheaf stalk. -/
theorem moduleAdditiveStalkModule_eq (M : X.left.Modules) (x : X.left) :
    moduleAdditiveStalkModule X M x =
      Module.compHom (M.presheaf.stalk x)
        ((X.left.presheaf.germ ⊤ x trivial).hom.comp (constants X)) := by
  apply Module.ext'
  intro a m
  exact moduleAdditiveStalk_smul_eq_constantGerm X M x a m

end AlgebraicGeometry.Scheme.Cohomology
