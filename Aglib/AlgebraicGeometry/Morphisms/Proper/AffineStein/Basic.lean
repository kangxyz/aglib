/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # The original affine factor and its structure-sheaf comparison

The factorization and qcqs affinization construction are independent of proper
coherent finiteness. The actual second map is named `finiteMap` for compatibility;
its finiteness is supplied only by the downstream geometric hypotheses.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- Canonical affinization preserves the actual structure sheaf for every qcqs scheme. -/
theorem isIso_c_toSpecΓ_of_qcqs (W : Scheme.{u})
    [CompactSpace W] [QuasiSeparatedSpace W] : IsIso W.toSpecΓ.c := by
  let F : (Spec Γ(W, ⊤)).sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} W.toSpecΓ.base).obj W.sheaf :=
    ⟨W.toSpecΓ.c⟩
  have : IsIso F := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun a : Γ(W, ⊤) => PrimeSpectrum.basicOpen a)
      PrimeSpectrum.isBasis_basic_opens ?_
    intro a
    change IsIso (W.toSpecΓ.app (PrimeSpectrum.basicOpen a))
    infer_instance
  exact (inferInstance : IsIso ((sheafToPresheaf _ _).map F))

/-- The actual open's affinization retains its original ring of ambient sections. -/
theorem isIso_c_opens_toSpecΓ_of_qcqs {X : Scheme.{u}} (U : X.Opens)
    [CompactSpace U.toScheme] [QuasiSeparatedSpace U.toScheme] : IsIso U.toSpecΓ.c := by
  let : IsIso U.toScheme.toSpecΓ.c := isIso_c_toSpecΓ_of_qcqs U.toScheme
  have : IsIso (Spec.map U.topIso.inv).c :=
    PresheafedSpace.c_isIso_of_iso (Spec.map U.topIso.inv).toPshHom
  change IsIso ((Spec.map U.topIso.inv).c ≫
    (TopCat.Presheaf.pushforward _ (Spec.map U.topIso.inv).base).map U.toScheme.toSpecΓ.c)
  infer_instance

namespace AffineStein

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)

/-- The first morphism uses the original ring `Γ(X, f⁻¹V)`, without a replacement ring. -/
def first : (f ⁻¹ᵁ V).toScheme ⟶ Spec Γ(X, f ⁻¹ᵁ V) :=
  (f ⁻¹ᵁ V).toSpecΓ

/-- The second morphism uses exactly the original restriction `f.app V`. -/
def finiteMap : Spec Γ(X, f ⁻¹ᵁ V) ⟶ V.toScheme :=
  Spec.map (f.app V) ≫ hV.isoSpec.inv

/-- The two actual maps factor the original restricted morphism. -/
@[reassoc]
theorem factorization : first f V ≫ finiteMap f V hV = f ∣_ V := by
  rw [first, finiteMap, ← Category.assoc, Scheme.Opens.toSpecΓ_naturality]
  rw [Category.assoc, hV.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- The coefficient square keeps the literal original ring map on the affine open. -/
theorem structuralCoefficient_square :
    (Scheme.ΓSpecIso Γ(Y, V)).inv ≫ ((f ∣_ V) ≫ V.toSpecΓ).appTop =
      f.app V ≫ (f ⁻¹ᵁ V).topIso.inv := by
  rw [← Scheme.Opens.toSpecΓ_naturality, Scheme.Hom.comp_appTop,
    Scheme.Opens.toSpecΓ_appTop]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc]

include hV in
/-- The canonical first map identifies the actual structure sheaf with its pushforward. -/
theorem first_c_isIso [IsProper f] : IsIso (first f V).c := by
  let : IsAffine V.toScheme := hV
  let : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ V)
  let : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)
  exact isIso_c_opens_toSpecΓ_of_qcqs (f ⁻¹ᵁ V)

end AffineStein

end AlgebraicGeometry.Scheme
