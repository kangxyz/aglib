/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Linear
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Structural linearity of original geometric pullback

The ordinary pushforward and its native pullback adjunction preserve the
specified global scalar action. The actual pullback is linear for every
compatible structural scalar square. Scalar and scheme universes are
independent; no flatness, quasicoherence or finiteness hypothesis is needed.
The higher differential-coefficient consumer delegates to this construction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Modules

/-- Ordinary pushforward preserves the actual structural scalar action. -/
theorem pushforward_linearOfHom {S : Type v} [CommRing S]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (α : S →+* Γ(Y, ⊤)) :
    letI := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom Y α
    (Scheme.Modules.pushforward p).Linear S := by
  let := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom Y α
  refine { map_smul := ?_ }
  intro M N φ r
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (r • φ).val.app (Opposite.op (p ⁻¹ᵁ U)) x =
    (r • (Scheme.Modules.pushforward p).map φ).val.app (Opposite.op U) x
  rw [moduleCategoryLinearOfHom_smul_app X (p.appTop.hom.comp α),
    moduleCategoryLinearOfHom_smul_app Y α]
  change X.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op
      (p.appTop (α r)) • φ.val.app (Opposite.op (p ⁻¹ᵁ U)) x =
    p.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (α r)) •
      φ.val.app (Opposite.op (p ⁻¹ᵁ U)) x
  have h := congrArg
    (fun q : Γ(Y, ⊤) ⟶ Γ(X, p ⁻¹ᵁ U) => q.hom (α r))
    (p.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change p.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (α r)) =
    X.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op (p.appTop (α r)) at h
  rw [h]

private theorem leftAdjointLinearOfRight {S : Type*} [CommRing S]
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [Linear S C] [Linear S D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [G.Linear S] : F.Linear S := by
  apply (Functor.linear_iff S F).mpr
  intro M r
  apply (adj.homEquiv M (F.obj M)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu := adj.unit.naturality (r • 𝟙 M)
  change (r • 𝟙 M) ≫ adj.unit.app M = adj.unit.app M ≫ G.map (F.map (r • 𝟙 M)) at hu
  rw [← hu]
  rw [G.map_smul]
  erw [G.map_id]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  erw [Category.comp_id]

/-- Original geometric pullback is linear for the pulled-back original
structural scalar action, through its native adjunction. -/
theorem pullback_linearOfHom {S : Type v} [CommRing S]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (α : S →+* Γ(Y, ⊤)) :
    letI := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom Y α
    (Scheme.Modules.pullback p).Linear S := by
  let := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom Y α
  let := pushforward_linearOfHom p α
  exact leftAdjointLinearOfRight (Scheme.Modules.pullbackPushforwardAdjunction p)

/-- A proved equality of the actual structural ring maps gives the same
native pullback linearity, without transporting a category realization. -/
theorem pullback_linearOfCompatibleHom {S : Type v} [CommRing S]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (α : S →+* Γ(Y, ⊤))
    (β : S →+* Γ(X, ⊤)) (h : p.appTop.hom.comp α = β) :
    letI := moduleCategoryLinearOfHom X β
    letI := moduleCategoryLinearOfHom Y α
    (Scheme.Modules.pullback p).Linear S := by
  subst β
  exact pullback_linearOfHom p α

end AlgebraicGeometry.Scheme.Modules
