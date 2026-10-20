/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericFiber
public import Aglib.AlgebraicGeometry.RationalPoint.Basic
public import Aglib.AlgebraicGeometry.Stalk.DedekindBase

/-!
# The actual generic origin of an arithmetic model

Source application: `K2-018#sec:k2018-splitting`, mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
The inputs are an actual model morphism and its actual section, plus curve
properties of the actual generic fibre. No regular-model existence theorem,
arbitrary stalk isomorphism, supplied residue equivalence or K-theoretic square
is assumed. Local geometry is transported through the generic-fibre projection.
Implementation: Lean 4.34.1/mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.LocalRing.GenericFiber (baseMap projection stalkEquiv scheme)



noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.LocalRing.GenericFiber

variable (A F : Type u) [CommRing A] [IsDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F]

/-- The actual fraction-field point lies over the affine generic point. -/
theorem baseMap_closedPoint_eq_genericPoint :
    baseMap A F (IsLocalRing.closedPoint F) = genericPoint (Spec (.of A)) := by
  rw [genericPoint_eq_bot_of_affine]
  have he : IsLocalRing.closedPoint F = (⊥ : PrimeSpectrum F) := Subsingleton.elim _ _
  rw [he]
  apply PrimeSpectrum.ext
  change RingHom.ker (algebraMap A F) = ⊥
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap A F)).mp (IsFractionRing.injective A F)

end AlgebraicGeometry.Scheme.LocalRing.GenericFiber

namespace AlgebraicGeometry.Scheme.GenericSection

variable (A F : Type u) [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) (σ : Spec (.of A) ⟶ Y)
  (hσ : σ ≫ p = 𝟙 _)

/-- The section of the generic fibre obtained by base-changing the given section of the model. -/
def genericSection : Spec (.of F) ⟶ scheme A F p :=
  pullback.lift (baseMap A F ≫ σ) (𝟙 _)
    (by simp only [Category.assoc, hσ, Category.comp_id, Category.id_comp])

omit [IsFractionRing A F] in
@[simp, reassoc] theorem genericSection_projection :
    genericSection A F p σ hσ ≫ projection A F p = baseMap A F ≫ σ :=
  pullback.lift_fst _ _ _

omit [IsFractionRing A F] in
@[simp, reassoc] theorem genericSection_structure :
    genericSection A F p σ hσ ≫ pullback.snd p (baseMap A F) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The rational point of the generic fibre defined by the base-changed section. -/
def genericOrigin : RationalPoint F (scheme A F p) where
  structureMap := pullback.snd p (baseMap A F)
  sectionMap := genericSection A F p σ hσ
  section_comp := genericSection_structure A F p σ hσ

/-- The point of the model obtained by projecting the generic-fibre rational origin. -/
def origin : Y := projection A F p (genericOrigin A F p σ hσ).point

omit [IsFractionRing A F] in
theorem origin_eq_section_generic_image :
    origin A F p σ hσ = (baseMap A F ≫ σ) (IsLocalRing.closedPoint F) := by
  change (genericSection A F p σ hσ ≫ projection A F p) (IsLocalRing.closedPoint F) = _
  rw [genericSection_projection]

/-- The stalk equivalence between the model at the projected origin and the local ring of the
generic-fibre rational origin. -/
def originStalkEquiv :
    Y.presheaf.stalk (origin A F p σ hσ) ≃+*
      (genericOrigin A F p σ hσ).localRing :=
  stalkEquiv A F p (genericOrigin A F p σ hσ).point

/-- The residue-field equivalence at the model origin induced by the generic-fibre stalk
equivalence and its rational point. -/
def originResidueEquiv : Y.residueField (origin A F p σ hσ) ≃+* F :=
  (IsLocalRing.ResidueField.mapEquiv (originStalkEquiv A F p σ hσ)).trans
    (genericOrigin A F p σ hσ).residueEquiv

@[simp] theorem originResidueEquiv_residue
    (r : Y.presheaf.stalk (origin A F p σ hσ)) :
    originResidueEquiv A F p σ hσ (Y.residue (origin A F p σ hσ) r) =
      (genericOrigin A F p σ hσ).evaluation (originStalkEquiv A F p σ hσ r) := by
  exact (genericOrigin A F p σ hσ).residueEquiv_residue _

theorem origin_closed_triangle :
    Spec.map (CommRingCat.ofHom ((originResidueEquiv A F p σ hσ).toRingHom.comp
      (Y.residue (origin A F p σ hσ)).hom)) ≫
      Y.fromSpecStalk (origin A F p σ hσ) = baseMap A F ≫ σ := by
  have hm : CommRingCat.ofHom ((originResidueEquiv A F p σ hσ).toRingHom.comp
      (Y.residue (origin A F p σ hσ)).hom) =
      Scheme.stalkClosedPointTo (genericSection A F p σ hσ ≫ projection A F p) := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  rw [hm]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk
      (genericSection A F p σ hσ ≫ projection A F p)).trans
    (genericSection_projection A F p σ hσ)

section Integral
variable [IsIntegral Y]

omit [IsFractionRing A F] in
theorem origin_generic_triangle :
    Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (origin A F p σ hσ))
      Y.functionField)) ≫
      Y.fromSpecStalk (origin A F p σ hσ) = Y.fromSpecStalk (genericPoint Y) := by
  change Spec.map (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial)) ≫
    Y.fromSpecStalk (origin A F p σ hσ) = _
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y).specializes trivial)

end Integral

section Domain
variable [IsDomain A]

theorem origin_eq_section_genericPoint :
    origin A F p σ hσ = σ (genericPoint (Spec (.of A))) := by
  rw [origin_eq_section_generic_image, Scheme.Hom.comp_apply,
    Scheme.LocalRing.GenericFiber.baseMap_closedPoint_eq_genericPoint]

theorem origin_over_genericPoint :
    p (origin A F p σ hσ) = genericPoint (Spec (.of A)) := by
  rw [origin_eq_section_genericPoint]
  change (σ ≫ p) (genericPoint (Spec (.of A))) = _
  rw [hσ]
  rfl

end Domain

section Dedekind
variable [IsDedekindDomain A] [IsIntegral Y] [IsDominant p]

/-- The canonical model constant-field embedding gives the actual structural generic triangle. -/
theorem generic_base_triangle :
    Y.fromSpecStalk (genericPoint Y) ≫ p =
      Spec.map (CommRingCat.ofHom (DedekindBase.constantToFunctionField F p)) ≫ baseMap A F := by
  let : Algebra A (Spec (.of A)).functionField :=
    (StructureSheaf.toStalk A (genericPoint (Spec (.of A)))).hom.toAlgebra
  have he : Spec.map (CommRingCat.ofHom
      (DedekindBase.fractionFieldEquiv (A := A) F).toRingHom) ≫ baseMap A F =
      (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) := by
    rw [baseMap, Spec.fromSpecStalk_eq, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    exact (DedekindBase.fractionFieldEquiv (A := A) F).commutes a
  have hm : CommRingCat.ofHom (DedekindBase.constantToFunctionField F p) =
      CommRingCat.ofHom (DedekindBase.fractionFieldEquiv (A := A) F).toRingHom ≫
      CommRingCat.ofHom (Scheme.functionFieldMap p) := rfl
  rw [hm, Spec.map_comp, Category.assoc, he]
  change Y.fromSpecStalk (genericPoint Y) ≫ p =
    Spec.map ((Spec (.of A)).presheaf.stalkSpecializes _ ≫ p.stalkMap (genericPoint Y)) ≫
      (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.SpecMap_stalkMap_fromSpecStalk p).symm

end Dedekind

end AlgebraicGeometry.Scheme.GenericSection

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Stalk/GenericSection.lean.
SHA-256 fab41654e14cda045f50e27671ddde02a250029019ee95c8e574cb95d196fcb4. -/
