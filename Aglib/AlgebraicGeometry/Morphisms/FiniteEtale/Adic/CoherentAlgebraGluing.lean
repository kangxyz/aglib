/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.AffineRestriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.GoodAffineNeighborhood

/-!
# Original coherent section algebras and their finite-etale gluing

The commutative ring presheaf below uses the original module sections and
restriction maps. Its cartesian spectrum squares are proved from the canonical
affine restriction algebra equivalence, whose right unit is original restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonObj AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.Modules.Algebra

universe u
variable {X : Scheme.{u}} (M : X.Modules) [MonObj M] [IsCommMonObj M]

/-- The commutative-ring presheaf on the original module sections. -/
def sectionRingPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := .of Γ(M, U.unop)
  map f := CommRingCat.ofHom (sectionRestriction M f.unop)
  map_id U := by
    apply CommRingCat.hom_ext
    exact sectionRestriction_id M U.unop
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact sectionRestriction_comp M f.unop g.unop

/-- The original internal unit gives the scalar map of the section-ring presheaf. -/
def sectionRingUnit : X.presheaf ⟶ sectionRingPresheaf M where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop) Γ(M, U.unop))
  naturality U V f := by
    apply CommRingCat.hom_ext
    ext r
    exact (sectionRestriction_algebraMap M f.unop r).symm

@[simp]
theorem sectionRingPresheaf_map_apply {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    (sectionRingPresheaf M).map i.op m = M.val.map i.op m := rfl

@[simp]
theorem sectionRingUnit_app_apply (U : X.Opens) (r : Γ(X, U)) :
    (sectionRingUnit M).app (op U) r = (η[M]).app U r := rfl

section
variable [M.IsQuasicoherent]

/-- The original section restriction spectrum square is cartesian. The
proof uses the canonical tensor algebra map, not a selected linear equivalence. -/
theorem sectionRing_restriction_isPullback (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    IsPullback (Spec.map ((sectionRingPresheaf M).map (homOfLE h).op))
      (Spec.map ((sectionRingUnit M).app (op U)))
      (Spec.map ((sectionRingUnit M).app (op V)))
      (Spec.map (X.presheaf.map (homOfLE h).op)) := by
  let : Algebra Γ(X, V) Γ(X, U) :=
    affineRestrictionBaseAlgebra ⟨V, hV⟩ ⟨U, hU⟩ (homOfLE h)
  exact Spec.isPullback_of_tensorEquiv
    (affineRestrictionAlgEquiv ⟨V, hV⟩ ⟨U, hU⟩ (homOfLE h) M)
    (sectionRestriction M (homOfLE h))
    (affineRestrictionAlgEquiv_comp_includeRight ⟨V, hV⟩ ⟨U, hU⟩ (homOfLE h) M)

end

variable (hM : QuasiCoherent.affineLocallyFiniteType X M)

include hM in
/-- Coherence supplies finite original section algebras on every affine open. -/
theorem sectionRingUnit_finite (U : X.Opens) (hU : IsAffineOpen U) :
    ((sectionRingUnit M).app (op U)).hom.Finite := by
  have : Module.Finite Γ(X, U) Γ(M, U) := finite_sectionAlgebra M hM ⟨U, hU⟩
  change (algebraMap Γ(X, U) Γ(M, U)).Finite
  exact (RingHom.finite_algebraMap (A := Γ(X, U)) (B := Γ(M, U))).mpr
    (finite_sectionAlgebra M hM ⟨U, hU⟩)

include hM in
/-- The original spectrum-to-chart map of a coherent algebra is finite. -/
theorem sectionToOpen_finite (U : X.Opens) (hU : IsAffineOpen U) :
    IsFinite (FiniteEtale.AffineAlgebraGluing.toOpen
      (sectionRingPresheaf M) (sectionRingUnit M) U hU) := by
  have : IsFinite (Spec.map ((sectionRingUnit M).app (op U))) :=
    (IsFinite.SpecMap_iff _).mpr (sectionRingUnit_finite M hM U hU)
  change IsFinite (Spec.map ((sectionRingUnit M).app (op U)) ≫ hU.isoSpec.inv)
  infer_instance

include hM in
/-- Over a locally Noetherian scheme, finite original section maps are
locally finitely presented, without any flatness premise. -/
theorem sectionToOpen_locallyOfFinitePresentation [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) :
    LocallyOfFinitePresentation (FiniteEtale.AffineAlgebraGluing.toOpen
      (sectionRingPresheaf M) (sectionRingUnit M) U hU) := by
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have := sectionToOpen_finite M hM U hU
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Algebra
