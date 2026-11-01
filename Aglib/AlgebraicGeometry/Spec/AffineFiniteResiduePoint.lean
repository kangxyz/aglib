/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AffineSectionAlgebra
public import Aglib.RingTheory.Smooth.FiniteResiduePointLocalSection
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The original finite residue point on an affine chart

The coefficient action is the preimage of the original composite point map.
Its factorization through the local residue field is the native residue lift,
not a chosen field isomorphism. The chart map is the original section-ring
retraction, with its original spectrum triangle. Closed points of the native
closed fibre supply the point hypotheses without changing the fibre model.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme.AffineFiniteResiduePoint

universe u

variable {A L : Type u} [CommRing A] [Field L] {X : Scheme.{u}}

/-- The original base action at the given field-valued point. -/
def baseScalar (p : X ⟶ Spec (.of A)) (c : Spec (.of L) ⟶ X) : A →+* L :=
  (Spec.preimage (c ≫ p)).hom

/-- This scalar map retains the literal original point composite. -/
theorem baseScalar_spec (p : X ⟶ Spec (.of A)) (c : Spec (.of L) ⟶ X) :
    Spec.map (CommRingCat.ofHom (baseScalar p c)) = c ≫ p :=
  Spec.map_preimage _

/-- The original chart retraction respects precisely the original base action. -/
theorem retraction_comp_coefficient (p : X ⟶ Spec (.of A))
    (c : Spec (.of L) ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (hc : c (closedPoint L) ∈ V) :
    (affineLocalSectionRetraction c V hc).comp (affineSectionCoefficientMap p V) =
      baseScalar p c := by
  have h : CommRingCat.ofHom
      ((affineLocalSectionRetraction c V hc).comp (affineSectionCoefficientMap p V)) =
        CommRingCat.ofHom (baseScalar p c) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, affineSectionCoefficientMap_spec p hV,
      ← Category.assoc, affineLocalSectionRetraction_spec c hV hc, baseScalar_spec]
  exact congrArg CommRingCat.Hom.hom h

/-- The same original point map as an algebra homomorphism on the same chart. -/
def pointAlgHom (p : X ⟶ Spec (.of A)) (c : Spec (.of L) ⟶ X)
    {V : X.Opens} (hV : IsAffineOpen V) (hc : c (closedPoint L) ∈ V) :
    letI : Algebra A Γ(X, V) := (affineSectionCoefficientMap p V).toAlgebra
    letI : Algebra A L := (baseScalar p c).toAlgebra
    Γ(X, V) →ₐ[A] L := by
  let : Algebra A Γ(X, V) := (affineSectionCoefficientMap p V).toAlgebra
  let : Algebra A L := (baseScalar p c).toAlgebra
  exact { affineLocalSectionRetraction c V hc with
    commutes' a := RingHom.congr_fun (retraction_comp_coefficient p c hV hc) a }

variable [IsLocalRing A]

/-- Locality comes from the image of the very same original point. -/
theorem baseScalar_isLocalHom (p : X ⟶ Spec (.of A)) (c : Spec (.of L) ⟶ X)
    (hclosed : (c ≫ p) (closedPoint L) = closedPoint A) :
    IsLocalHom (baseScalar p c) := by
  have h : (maximalIdeal L).comap (baseScalar p c) = maximalIdeal A := by
    have h' : Spec.map (CommRingCat.ofHom (baseScalar p c)) (closedPoint L) =
        closedPoint A := by rw [baseScalar_spec]; exact hclosed
    exact congrArg PrimeSpectrum.asIdeal h'
  exact ((local_hom_TFAE (baseScalar p c)).out 5 1 rfl rfl).mp h

/-- A smooth chart through an actual closed field-valued point supplies the
original finite-residue local section, including the original residue equation.
The total local base map is not asserted etale. -/
theorem exists_local_section (p : X ⟶ Spec (.of A)) [Smooth p]
    (c : Spec (.of L) ⟶ X) [IsClosedImmersion c]
    (hclosed : (c ≫ p) (closedPoint L) = closedPoint A)
    {V : X.Opens} (hV : IsAffineOpen V) (hc : c (closedPoint L) ∈ V) :
    letI : Algebra A Γ(X, V) := (affineSectionCoefficientMap p V).toAlgebra
    letI : Algebra A L := (baseScalar p c).toAlgebra
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T) (_ : IsLocalRing T),
      Module.Flat A T ∧ Algebra.EssFiniteType A T ∧ IsLocalHom (algebraMap A T) ∧
        (maximalIdeal A).map (algebraMap A T) = maximalIdeal T ∧
          ∃ (ε : Γ(X, V) →ₐ[A] T) (l : T →ₐ[A] L),
            Function.Surjective l ∧ IsLocalHom l.toRingHom ∧
              l.comp ε = pointAlgHom p c hV hc := by
  let : Algebra A Γ(X, V) := (affineSectionCoefficientMap p V).toAlgebra
  let : Algebra A L := (baseScalar p c).toAlgebra
  let : Algebra.Smooth A Γ(X, V) :=
    RingHom.smooth_algebraMap.mp (affineSectionCoefficientMap_smooth p hV)
  let : IsLocalHom (baseScalar p c) := baseScalar_isLocalHom p c hclosed
  let r : ResidueField A →+* L := ResidueField.lift (baseScalar p c)
  let : Algebra (ResidueField A) L := r.toAlgebra
  let : IsScalarTower A (ResidueField A) L :=
    IsScalarTower.of_algebraMap_eq' (ResidueField.lift_comp_residue (baseScalar p c)).symm
  have hft : (baseScalar p c).FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  have hr : r.FiniteType := RingHom.FiniteType.of_comp_finiteType
    ((ResidueField.lift_comp_residue (baseScalar p c)).symm ▸ hft)
  let : Module.Finite (ResidueField A) L := RingHom.finite_algebraMap.mp
    (RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hr)
  exact Algebra.Smooth.FiniteResiduePointLocalSection.exists_local_section
    A Γ(X, V) L (pointAlgHom p c hV hc)

/-- The original residue point of a closed point of the native closed fibre
is a closed immersion in the original total space. -/
theorem closedFiberPoint_isClosedImmersion (p : X ⟶ Spec (.of A))
    (z : p.fiber (closedPoint A)) (hz : IsClosed ({z} : Set (p.fiber (closedPoint A)))) :
    IsClosedImmersion ((p.fiber (closedPoint A)).fromSpecResidueField z ≫
      p.fiberι (closedPoint A)) := by
  let : IsClosedImmersion ((Spec (.of A)).fromSpecResidueField (closedPoint A)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_singleton_closedPoint A)
  let : IsClosedImmersion (p.fiberι (closedPoint A)) :=
    inferInstanceAs (IsClosedImmersion (Limits.pullback.fst p
      ((Spec (.of A)).fromSpecResidueField (closedPoint A))))
  let : IsClosedImmersion ((p.fiber (closedPoint A)).fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  infer_instance

/-- The same native residue point maps to the original closed base point. -/
theorem closedFiberPoint_maps_closed (p : X ⟶ Spec (.of A))
    (z : p.fiber (closedPoint A)) :
    (((p.fiber (closedPoint A)).fromSpecResidueField z ≫ p.fiberι (closedPoint A)) ≫ p)
      (closedPoint ((p.fiber (closedPoint A)).residueField z)) = closedPoint A := by
  exact (p.fiberHomeo (closedPoint A)
    ((p.fiber (closedPoint A)).fromSpecResidueField z
      (closedPoint ((p.fiber (closedPoint A)).residueField z)))).property

end AlgebraicGeometry.Scheme.AffineFiniteResiduePoint
