/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FieldConservative
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients

/-! # A chosen geometric stalk detects original module sheaf isomorphisms

Native scalar forgetting commutes with the actual point fibre. Reflection
through that functor and the original abelian chosen-point detector preserves
an independently sized ring, without a Galois representation or finiteness
hypothesis on its modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u r

variable (R : Type r) [Ring R] (K : Type u) [Field K]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ Spec (.of K))

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Any chosen separably closed geometric point detects isomorphisms of native
module-valued sheaves over a field, with arbitrary independent ring universe. -/
theorem isIso_of_field_moduleGeometricStalk
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} R)} (a : F ⟶ G)
    [IsIso ((pointSmallEtale η).sheafFiber.map a)] : IsIso a := by
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let : PreservesColimitsOfSize.{u, u} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, r, u, u} R
  let : PreservesFilteredColimitsOfSize.{u, u} U := ⟨fun _ _ _ => inferInstance⟩
  let V := ModuleCat.Sheaf.underlying R (Spec (.of K)).smallEtaleTopology
  let : IsIso (((pointSmallEtale η).sheafFiber ⋙ U).map a) :=
    show IsIso (U.map ((pointSmallEtale η).sheafFiber.map a)) from inferInstance
  have h : IsIso ((pointSmallEtale η).sheafFiber.map (V.map a)) :=
    (NatIso.isIso_map_iff ((pointSmallEtale η).sheafFiberCompIso U) a).mpr inferInstance
  let := h
  let := isIso_of_field_geometricStalk K η (V.map a)
  exact isIso_of_reflects_iso a V

end AlgebraicGeometry.Scheme.EtaleCohomology
