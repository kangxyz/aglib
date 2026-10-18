/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace
public import Aglib.AlgebraicGeometry.Modules.Tensor.Linear

/-!
# Structural scalars on actual differential coefficients

The ordinary pushforward and its native pullback adjunction preserve the
specified structural scalar action. Tensoring with the actual top differential
sheaf then gives structural linearity of the original coefficient functor.
No geometric finiteness or flatness condition is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Cohomology

private theorem pushforwardLinearOfHom {S : Type u} [CommRing S]
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

/-- The actual differential-coefficient functor preserves every specified structural
scalar, through the native pullback adjunction and original tensor functor. -/
theorem relativeTopDifferentialCoefficientsFunctor_linearOfHom {S : Type u} [CommRing S]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (α : S →+* Γ(Y, ⊤)) (n : ℕ) :
    letI := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom Y α
    (relativeTopDifferentialCoefficientsFunctor p n).Linear S := by
  let := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom Y α
  let := pushforwardLinearOfHom p α
  let : (Scheme.Modules.pullback p).Linear S :=
    leftAdjointLinearOfRight (Scheme.Modules.pullbackPushforwardAdjunction p)
  change (Scheme.Modules.pullback p ⋙ moduleTensorLeftFunctor X _).Linear S
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology
