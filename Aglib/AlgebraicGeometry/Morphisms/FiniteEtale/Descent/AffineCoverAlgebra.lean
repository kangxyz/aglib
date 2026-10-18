/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineEffectiveDescent
public import Mathlib.AlgebraicGeometry.Group.Affine

/-! Coordinates for arbitrary finite-etale covers of an affine scheme. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

universe u
variable {S : Type u} [CommRing S]

/-- An actual algebra and a structural isomorphism for the given affine cover. -/
structure AlgebraModel (Y : Scheme.FiniteEtale (Spec (.of S))) where
  /-- The finite étale commutative `S`-algebra presenting the cover `Y`. -/
  algebra : CommAlgCat.{u} S
  finite : Module.Finite S algebra
  etale : Algebra.Etale S algebra
  /-- The isomorphism over `Spec S` from the spectrum of `algebra` to `Y.obj`. -/
  iso : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap S algebra))) ≅ Y.obj

attribute [instance] AlgebraModel.finite AlgebraModel.etale

theorem exists_algebraModel (Y : Scheme.FiniteEtale (Spec (.of S))) : Nonempty
    (AlgebraModel Y) := by
  have : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := .of S) (G := Y.obj)).2 inferInstance
  have hfin : IsFinite ((algSpec (.of S)).obj A).hom := by
    rw [← Over.w e.hom]
    infer_instance
  have het : Etale ((algSpec (.of S)).obj A).hom := by
    rw [← Over.w e.hom]
    infer_instance
  have hfin' : Module.Finite S A.unop :=
    (RingHom.finite_algebraMap).1 ((IsFinite.SpecMap_iff _).1 hfin)
  have het' : Algebra.Etale S A.unop :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 het)
  exact ⟨⟨A.unop, hfin', het', e⟩⟩

/-- Choose the coordinates supplied by the actual affine Spec equivalence. -/
def algebraModel (Y : Scheme.FiniteEtale (Spec (.of S))) : AlgebraModel Y :=
  Classical.choice (exists_algebraModel Y)

/-- The isomorphism of finite étale covers induced by the algebra model isomorphism
`M.iso` over `Spec S`. -/
def AlgebraModel.coverIso {Y : Scheme.FiniteEtale (Spec (.of S))} (M : AlgebraModel Y) :
    specCover S M.algebra ≅ Y :=
  ObjectProperty.isoMk _ M.iso

end AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 c41d65f2f172869f9f33b533fa7a79a68abc792fe83aa681a0b0e0b464f2400e.
Definitions, hypotheses and universes are retained modulo native names. -/
