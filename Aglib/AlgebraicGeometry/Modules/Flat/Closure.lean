/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Pullback
public import Aglib.CategoryTheory.ExactCategory.KernelClosed
public import Mathlib.CategoryTheory.Retract

/-!
# Closure properties of stalkwise-flat module sheaves

Actual module stalks detect flatness under isomorphisms, the specified short-exact
kernels, small coproducts, binary biproducts, zero objects and actual retracts.
The kernel statement requires both the middle and quotient objects to be flat.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/BoundedFlatPullback.lean`.
SHA-256: `c33516f3f4e3e10cf8b8d63ef66d116c44544348f1643314099e0d41a8f782c6`.
Selected source lines: 38–48, 67–85.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/FlatCochainResolution.lean`.
SHA-256: `9cfb49d5e5dae48f3aa71d7aa8e3708e0668b89a6e9a37eaee9a402da4e85dad`.
Selected source lines: 39–46.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/FlatRetracts.lean`.
SHA-256: `beb669dddca0e2762dd82ece74ef602a1b4585957fc586dfea58623ccc5cb80f`.
Selected source lines: 33–40.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules

instance stalkwiseFlat_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    (stalkwiseFlat X).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    intro x
    let : Module.Flat (X.presheaf.stalk x) ((moduleStalk X x).obj M) := hM x
    exact Module.Flat.of_linearEquiv ((moduleStalk X x).mapIso e.symm).toLinearEquiv

instance stalkwiseFlat_kernelClosed (X : Scheme.{u}) :
    (sheafExactStructure X).IsKernelClosed (stalkwiseFlat X) where
  prop_kernel hS h₂ h₃ := stalkwiseFlat_of_shortExact hS h₂ h₃

/-- Small-universe coproducts also preserve the actual flat stalk property. -/
theorem stalkwiseFlat_smallCoproduct (X : Scheme.{u}) {I : Type} (M : I → X.Modules)
    (hM : ∀ i, stalkwiseFlat X (M i)) : stalkwiseFlat X (∐ M) := by
  classical
  intro x
  let (i : I) : Module.Flat (X.presheaf.stalk x) ((moduleStalk X x).obj (M i)) := hM i x
  exact Module.Flat.of_linearEquiv
    ((PreservesCoproduct.iso (moduleStalk X x) M) ≪≫
      ModuleCat.coprodIsoDirectSum (fun i => (moduleStalk X x).obj (M i))).toLinearEquiv

/-- Binary coproducts preserve actual stalkwise flatness. -/
theorem stalkwiseFlat_biprod (X : Scheme.{u}) {M N : X.Modules}
    (hM : stalkwiseFlat X M) (hN : stalkwiseFlat X N) : stalkwiseFlat X (M ⊞ N) := by
  let F : WalkingPair → X.Modules := fun i => i.casesOn M N
  let e : (∐ F) ≅ (M ⨿ N) := HasColimit.isoOfNatIso
    (Discrete.natIso (fun i => by cases i; exact Iso.refl _))
  exact (stalkwiseFlat X).prop_of_iso (e ≪≫ (biprod.isoCoprod M N).symm)
    (stalkwiseFlat_smallCoproduct X F (fun i => i.casesOn hM hN))

/-- A zero module sheaf has flat actual module stalks. -/
theorem stalkwiseFlat_of_isZero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M) :
    stalkwiseFlat X M := by
  intro x
  let : Subsingleton ((moduleStalk X x).obj M) :=
    ModuleCat.subsingleton_of_isZero ((moduleStalk X x).map_isZero hM)
  infer_instance

/-- Genuine sheaf retracts preserve flatness of all actual module stalks. -/
theorem stalkwiseFlat_of_retract {X : Scheme.{u}} {M N : X.Modules}
    (h : Retract M N) (hN : stalkwiseFlat X N) : stalkwiseFlat X M := by
  intro x
  let : Module.Flat (X.presheaf.stalk x) ((moduleStalk X x).obj N) := hN x
  let hx := h.map (moduleStalk X x)
  apply Module.Flat.of_retract hx.i.hom hx.r.hom
  exact congrArg (fun p : (moduleStalk X x).obj M ⟶ (moduleStalk X x).obj M => p.hom) hx.retract

end AlgebraicGeometry.Scheme.Modules
