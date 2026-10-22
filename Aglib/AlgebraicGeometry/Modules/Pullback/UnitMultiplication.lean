/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections

/-!
# Actual scalar multiplication under scheme pullback

The original multiplication endomorphism by a global section commutes with
the canonical pullback-unit comparison. Extracted unchanged from the affine
blowup frame consumer; no affine or reducedness hypothesis is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual pullback-unit comparison intertwines multiplication by the
original global section with multiplication by its original pullback. -/
theorem unitMul_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (unitMul Y s) ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso f).hom ≫ unitMul X (f.appTop s) := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackUnitIso_homEquiv]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(Y, U) at x
  change f.app U (x * Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) =
    f.app U x * X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U ⟶ ⊤).op (f.appTop s)
  rw [map_mul]
  congr 1
  exact ConcreteCategory.congr_hom
    (f.toLRSHom.c.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) s

end AlgebraicGeometry.Scheme.Modules
