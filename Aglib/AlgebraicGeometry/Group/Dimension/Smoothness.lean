/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Dimension.QuasiFinite
public import Aglib.AlgebraicGeometry.Group.Translation.LocalProperty
public import Aglib.RingTheory.Smooth.GeometricRegularity
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Smoothness from regularity at the original group unit

Over a perfect field, the regular localization criterion makes the actual rational unit a
smooth point. Its native smooth-locus open then carries a smooth structure morphism. Over an
algebraically closed field, the existing actual translation cover spreads smoothness to the
whole group. Target properness, connectedness and prior target smoothness are not inputs.

The algebraically closed field hypothesis is retained here. Arbitrary-field Picard applications
can use their original representative's proved base-change triangle and fpqc smoothness descent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory IsLocalRing TopologicalSpace
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

private theorem unit_mem_smoothLocus_of_isRegularLocalRing_of_perfectField
    [PerfectField k] (G : FScheme k) [MonObj G] [LocallyOfFiniteType G.hom]
    [IsRegularLocalRing (G.left.presheaf.stalk (unitPoint G))] :
    unitPoint G ∈ G.hom.smoothLocus := by
  let q := Cotangent.pointData η[G]
  let R := q.localRing
  let := q.constants.toAlgebra
  have : IsRegularLocalRing R := by
    change IsRegularLocalRing (G.left.presheaf.stalk (unitPoint G))
    infer_instance
  have hcover : q.point ∈ ⨆ V : G.left.affineOpens, (V : G.left.Opens) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨⟨V, hV⟩, hx⟩ := Opens.mem_iSup.mp hcover
  let A := Γ(G.left, V)
  let := (q.affineConstants V).toAlgebra
  let : Nontrivial A := (G.left.presheaf.germ V q.point hx).hom.domain_nontrivial
  have hft : (q.affineConstants V).FiniteType := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ G.hom.appLE ⊤ V _).hom).FiniteType
    rw [CommRingCat.hom_comp]
    exact (G.hom.finiteType_appLE (isAffineOpen_top _) hV _).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  have : Algebra.FiniteType k A := hft
  let : Algebra A R := G.left.presheaf.algebra_section_stalk ⟨q.point, hx⟩
  let : IsScalarTower k A R :=
    IsScalarTower.of_algebraMap_eq' (q.germ_comp_affineConstants hx).symm
  let p := (hV.primeIdealOf ⟨q.point, hx⟩).asIdeal
  have : IsLocalization.AtPrime R p := hV.isLocalization_stalk ⟨q.point, hx⟩
  let e : Localization.AtPrime p ≃ₐ[A] R := IsLocalization.algEquiv p.primeCompl _ _
  have : IsRegularLocalRing (Localization.AtPrime p) :=
    IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm
  have : Algebra.IsSmoothAt k p :=
    Algebra.IsSmoothAt.of_isRegularLocalRing_of_perfectField k A p
  have hs : Algebra.FormallySmooth k R := Algebra.FormallySmooth.of_equiv (e.restrictScalars k)
  have hc : q.constants.FormallySmooth := (RingHom.formallySmooth_algebraMap).mpr hs
  change (((RationalPoint.fieldStalkIso k (q.structureMap q.point)).inv ≫
    q.structureMap.stalkMap q.point).hom).FormallySmooth at hc
  rw [CommRingCat.hom_comp, RingHom.FormallySmooth.respectsIso.cancel_left_isIso] at hc
  exact hc

/-- A group locally of finite type over an algebraically closed field is smooth if its actual
unit stalk is regular. The smooth-locus open spreads by the original translations. -/
theorem smooth_of_isRegularLocalRing_unit_of_isAlgClosed [IsAlgClosed k]
    (G : FScheme k) [GrpObj G] [LocallyOfFiniteType G.hom]
    [IsRegularLocalRing (G.left.presheaf.stalk (unitPoint G))] : Smooth G.hom := by
  have hunit := unit_mem_smoothLocus_of_isRegularLocalRing_of_perfectField G
  let W := G.hom.smoothLocus
  have hW : Nonempty W := ⟨⟨unitPoint G, hunit⟩⟩
  have hsW : Smooth (W.ι ≫ G.hom) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq W.ι G.hom]
    exact Scheme.Opens.ι_preimage_self W
  let GG : Grp (FScheme k) := Grp.mk G
  let f : GG ⟶ Grp.trivial (FScheme k) :=
    Grp.homMk'' (toUnit G) (toUnit_unique _ _) (toUnit_unique _ _)
  have hstruct : (f.hom.hom.left : G.left ⟶ Spec (.of k)) = G.hom := by
    have h := Over.w f.hom.hom
    change (f.hom.hom.left : G.left ⟶ Spec (.of k)) ≫
      (𝟙 (Spec (.of k))) = G.hom at h
    exact (Category.comp_id (f.hom.hom.left : G.left ⟶ Spec (.of k))).symm.trans h
  have : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth := inferInstance
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u}) (Q := RingHom.Smooth)
  have hs : Smooth f.hom.hom.left :=
    Translation.property_of_nonempty_open (@Smooth.{u}) GG (Grp.trivial (FScheme k)) f W hW
      (by rw [hstruct]; exact hsW)
  exact hstruct ▸ hs

end AlgebraicGeometry.Scheme.Group
