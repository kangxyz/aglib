/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesHartogsCoverRecovery
public import Aglib.AlgebraicGeometry.Spec.HartogsNestedCoverRestriction
public import Aglib.AlgebraicGeometry.Spec.HartogsFiniteEtaleAlgebra
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NativeRingSections

/-! # Original Hartogs cover algebra and its coefficient algebra

Every algebra structure below is induced by the original structural morphism.
The comparison combines actual cover restriction, the constructed geometric
recovery on the inverse-image base open, and the original flat tensor map.
The coefficient algebra is not assumed etale.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MvPowerSeries
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- A map over the original affine base gives its actual map on section
algebras, with no change of either scalar structure. -/
def originalAffineSectionAlgHom {B : Type u} [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of B)) (g : Y ⟶ Spec (.of B))
    (p : Y ⟶ X) (h : p ≫ f = g) :
    letI := (affineScalarMap f).toAlgebra
    letI := (affineScalarMap g).toAlgebra
    Γ(X, ⊤) →ₐ[B] Γ(Y, ⊤) := by
  letI := (affineScalarMap f).toAlgebra
  letI := (affineScalarMap g).toAlgebra
  refine { __ := p.appTop.hom, commutes' := ?_ }
  intro b
  have hs := affineScalarMap_comp_hom f p
  rw [h] at hs
  exact RingHom.congr_fun hs b

/-- Bijectivity upgrades precisely the original section homomorphism. -/
def originalAffineSectionAlgEquiv {B : Type u} [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of B)) (g : Y ⟶ Spec (.of B))
    (p : Y ⟶ X) (h : p ≫ f = g) (hp : Function.Bijective p.appTop) :
    letI := (affineScalarMap f).toAlgebra
    letI := (affineScalarMap g).toAlgebra
    Γ(X, ⊤) ≃ₐ[B] Γ(Y, ⊤) := by
  letI := (affineScalarMap f).toAlgebra
  letI := (affineScalarMap g).toAlgebra
  exact AlgEquiv.ofBijective (originalAffineSectionAlgHom f g p h) hp

/-- The algebra equivalence retains exactly the original ring homomorphism. -/
theorem originalAffineSectionAlgEquiv_toRingHom {B : Type u} [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of B)) (g : Y ⟶ Spec (.of B))
    (p : Y ⟶ X) (h : p ≫ f = g) (hp : Function.Bijective p.appTop) :
    letI := (affineScalarMap f).toAlgebra
    letI := (affineScalarMap g).toAlgebra
    (originalAffineSectionAlgEquiv f g p h hp).toRingHom = p.appTop.hom := rfl

/-- The complete original finite-etale isomorphism-to-section-algebra
construction is performed before specializing to a constructed cover. -/
def originalFiniteEtaleSectionAlgEquiv {B : Type u} [CommRing B]
    {X : Scheme.{u}} (j : X ⟶ Spec (.of B))
    {D E : FiniteEtale X} (e : D ≅ E) :
    letI := (affineScalarMap (E.obj.hom ≫ j)).toAlgebra
    letI := (affineScalarMap (D.obj.hom ≫ j)).toAlgebra
    Γ(E.obj.left, ⊤) ≃ₐ[B] Γ(D.obj.left, ⊤) := by
  let p := e.hom.hom.left
  let ei := (FiniteEtale.forgetToScheme X).mapIso e
  have hp : p ≫ (E.obj.hom ≫ j) = D.obj.hom ≫ j := by
    rw [← Category.assoc]
    exact congrArg (fun k => k ≫ j) e.hom.hom.w
  exact originalAffineSectionAlgEquiv (E.obj.hom ≫ j) (D.obj.hom ≫ j) p hp
    ((ConcreteCategory.isIso_iff_bijective ei.hom.appTop).mp inferInstance)

/-- The full original flat tensor construction for a cover of a base open.
Its target is the selected geometric pullback, not an alternative algebra. -/
def originalBaseOpenSectionTensorAlgEquiv
    {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B) (hflat : σ.Flat)
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (D : FiniteEtale U.toScheme) :
    let c := Spec.map (CommRingCat.ofHom σ)
    letI := σ.toAlgebra
    letI := (affineScalarMap (D.obj.hom ≫ U.ι)).toAlgebra
    letI := (affineScalarMap
      (pullback.snd D.obj.hom (c ∣_ U) ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    B ⊗[A] Γ(D.obj.left, ⊤) ≃ₐ[B] Γ(pullback D.obj.hom (c ∣_ U), ⊤) := by
  let c := Spec.map (CommRingCat.ofHom σ)
  let r := pullback.fst D.obj.hom (c ∣_ U)
  let q := pullback.snd D.obj.hom (c ∣_ U) ≫ (c ⁻¹ᵁ U).ι
  have H : IsPullback r q (D.obj.hom ≫ U.ι) c :=
    (IsPullback.of_hasPullback D.obj.hom (c ∣_ U)).paste_vert
      (isPullback_morphismRestrict c U)
  exact Cohomology.ringSectionsTensorAlgEquiv_of_flat_of_isPullback r σ q
    (D.obj.hom ≫ U.ι) H hflat

/-- One original algebra recovery construction, including both original
map laws. The three supplied equivalences are unchanged. -/
structure OriginalAlgebraRecoveryData
    {B T P R C : Type u} [CommRing B] [CommRing T] [CommRing P]
    [CommRing R] [CommRing C] [Algebra B T] [Algebra B P]
    [Algebra B R] [Algebra B C]
    (tensor : T ≃ₐ[B] P) (recovery : P ≃ₐ[B] R) (restriction : C ≃ₐ[B] R)
    (restrictionMap : C →+* R) where
  /-- The actual composite of the original three equivalences. -/
  comparison : T ≃ₐ[B] C
  /-- The actual forward restriction equation. -/
  restriction_apply (x : T) : restrictionMap (comparison x) = recovery (tensor x)
  /-- The inverse uses the same original maps in reverse order. -/
  symm_apply (a : C) : comparison.symm a = tensor.symm (recovery.symm (restrictionMap a))

/-- Construct the original recovery equivalence and both laws together,
before native covers or section scalar structures are specialized. -/
def originalAlgebraRecoveryData
    {B T P R C : Type u} [CommRing B] [CommRing T] [CommRing P]
    [CommRing R] [CommRing C] [Algebra B T] [Algebra B P]
    [Algebra B R] [Algebra B C]
    (tensor : T ≃ₐ[B] P) (recovery : P ≃ₐ[B] R) (restriction : C ≃ₐ[B] R)
    (restrictionMap : C →+* R) (hmap : restriction.toRingHom = restrictionMap) :
    OriginalAlgebraRecoveryData tensor recovery restriction restrictionMap where
  comparison := tensor.trans (recovery.trans restriction.symm)
  restriction_apply x := by
    rw [← hmap]
    exact restriction.apply_symm_apply (recovery (tensor x))
  symm_apply a := by
    rw [← hmap]
    rfl

variable {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "B" => MvPowerSeries σ A
local notation "c" => Spec.map (CommRingCat.ofHom (C : A →+* B))
local notation "z" => Spec.map (CommRingCat.ofHom (constantCoeff : B →+* A))

/-- The original section cover, using the constructed actual zero section. -/
abbrev powerSeriesHartogsSectionCover (U : (Spec (.of A)).Opens)
    (V : (Spec (.of B)).Opens) (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme) :=
  (FiniteEtale.baseChange (powerSeriesAmbientOpenSection U V hzero)).obj D

/-- The original cover over the original inverse-image base open. -/
abbrev powerSeriesHartogsRestrictedCover (U : (Spec (.of A)).Opens)
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V) (D : FiniteEtale V.toScheme) :=
  (FiniteEtale.baseChange ((Spec (.of B)).homOfLE hUV)).obj D

/-- Actual restriction of section algebras to the base-open inverse image. -/
def powerSeriesHartogsRestrictionAlgEquiv
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V) (D : FiniteEtale V.toScheme) :
    letI := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
    letI := (affineScalarMap
      ((powerSeriesHartogsRestrictedCover U V hUV D).obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    Γ(D.obj.left, ⊤) ≃ₐ[B]
      Γ((powerSeriesHartogsRestrictedCover U V hUV D).obj.left, ⊤) := by
  let D₁ := powerSeriesHartogsRestrictedCover U V hUV D
  let j := (Spec (.of B)).homOfLE hUV
  let r := pullback.fst D.obj.hom j
  have hflat : (C : A →+* B).Flat := by
    change (algebraMap A B).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact MvPowerSeries.flat_of_isNoetherian σ A
  have hs := Cohomology.scalarSections_bijective_of_flat_of_isPullback
    (c ∣_ U) (C : A →+* B) (c ⁻¹ᵁ U).ι U.ι
    (isPullback_morphismRestrict c U) hflat hU
  have hr : r ≫ (D.obj.hom ≫ V.ι) = D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
    congr 1
    exact homOfLE_ι (Spec (.of B)) hUV
  exact originalAffineSectionAlgEquiv (D.obj.hom ≫ V.ι)
    (D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι) r hr
    (cover_homOfLE_pullback_fst_appTop_bijective B (c ⁻¹ᵁ U) V hUV hs D.obj.hom)

/-- The actual restriction equivalence retains the literal pullback
first projection on rings, before it is applied to a constructed comparison. -/
theorem powerSeriesHartogsRestrictionAlgEquiv_toRingHom
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V) (D : FiniteEtale V.toScheme) :
    let D₁ := powerSeriesHartogsRestrictedCover U V hUV D
    letI := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
    letI := (affineScalarMap (D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    (powerSeriesHartogsRestrictionAlgEquiv U hU V hUV D).toRingHom =
      (pullback.fst D.obj.hom ((Spec (.of B)).homOfLE hUV)).appTop.hom := by
  dsimp only [powerSeriesHartogsRestrictionAlgEquiv]
  exact originalAffineSectionAlgEquiv_toRingHom _ _ _ _ _

/-- Actual geometric cover recovery induces its original map of section
algebras over the unchanged power-series ring. -/
def powerSeriesHartogsRecoveryAlgEquiv
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme) :
    let D₀ := powerSeriesHartogsSectionCover U V hzero D
    let P := (FiniteEtale.baseChange (c ∣_ U)).obj D₀
    let D₁ := powerSeriesHartogsRestrictedCover U V hUV D
    letI := (affineScalarMap (P.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    letI := (affineScalarMap (D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    Γ(P.obj.left, ⊤) ≃ₐ[B] Γ(D₁.obj.left, ⊤) :=
  originalFiniteEtaleSectionAlgEquiv (c ⁻¹ᵁ U).ι
    (powerSeriesHartogsCoverRecovery U hU V hUV hzero D)

/-- The original flat tensor comparison for the actual section cover and
its actual geometric pullback. -/
def powerSeriesHartogsSectionTensorAlgEquiv
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (V : (Spec (.of B)).Opens) (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme) :
    let D₀ := powerSeriesHartogsSectionCover U V hzero D
    let P := (FiniteEtale.baseChange (c ∣_ U)).obj D₀
    letI := (C : A →+* B).toAlgebra
    letI : Module A B := Algebra.toModule
    letI := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
    letI := (affineScalarMap (P.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    B ⊗[A] Γ(D₀.obj.left, ⊤) ≃ₐ[B] Γ(P.obj.left, ⊤) := by
  have hflat : (C : A →+* B).Flat := by
    change (algebraMap A B).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact MvPowerSeries.flat_of_isNoetherian σ A
  exact originalBaseOpenSectionTensorAlgEquiv (C : A →+* B) hflat U
    (powerSeriesHartogsSectionCover U V hzero D)

/-- Specialize the complete original construction and both map laws once
at the unchanged native tensor, recovery, and restriction equivalences. -/
def powerSeriesHartogsAlgebraRecoveryData
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme) :
    let D₀ := powerSeriesHartogsSectionCover U V hzero D
    let P := (FiniteEtale.baseChange (c ∣_ U)).obj D₀
    let D₁ := powerSeriesHartogsRestrictedCover U V hUV D
    letI := (C : A →+* B).toAlgebra
    letI : Module A B := Algebra.toModule
    letI := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
    letI := (affineScalarMap (P.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    letI := (affineScalarMap (D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    letI := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
    OriginalAlgebraRecoveryData
      (powerSeriesHartogsSectionTensorAlgEquiv U V hzero D)
      (powerSeriesHartogsRecoveryAlgEquiv U hU V hUV hzero D)
      (powerSeriesHartogsRestrictionAlgEquiv U hU V hUV D)
      (pullback.fst D.obj.hom ((Spec (.of B)).homOfLE hUV)).appTop.hom := by
  let D₀ := powerSeriesHartogsSectionCover U V hzero D
  let P := (FiniteEtale.baseChange (c ∣_ U)).obj D₀
  let D₁ := powerSeriesHartogsRestrictedCover U V hUV D
  letI := (C : A →+* B).toAlgebra
  letI : Module A B := Algebra.toModule
  letI := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
  letI := (affineScalarMap (P.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
  letI := (affineScalarMap (D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
  letI := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
  exact originalAlgebraRecoveryData
    (powerSeriesHartogsSectionTensorAlgEquiv U V hzero D)
    (powerSeriesHartogsRecoveryAlgEquiv U hU V hUV hzero D)
    (powerSeriesHartogsRestrictionAlgEquiv U hU V hUV D)
    (pullback.fst D.obj.hom ((Spec (.of B)).homOfLE hUV)).appTop.hom
    (powerSeriesHartogsRestrictionAlgEquiv_toRingHom U hU V hUV D)

/-- The original global algebra C is the scalar extension of its actual
section algebra C₀. This is the comparison of the single recovery factory. -/
def powerSeriesHartogsAlgebraComparison
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme) :
    let D₀ := powerSeriesHartogsSectionCover U V hzero D
    letI := (C : A →+* B).toAlgebra
    letI : Module A B := Algebra.toModule
    letI := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
    letI := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
    B ⊗[A] Γ(D₀.obj.left, ⊤) ≃ₐ[B] Γ(D.obj.left, ⊤) := by
  let D₀ := powerSeriesHartogsSectionCover U V hzero D
  let P := (FiniteEtale.baseChange (c ∣_ U)).obj D₀
  let D₁ := powerSeriesHartogsRestrictedCover U V hUV D
  letI := (C : A →+* B).toAlgebra
  letI : Module A B := Algebra.toModule
  letI := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
  letI := (affineScalarMap (P.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
  letI := (affineScalarMap (D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
  letI := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
  exact (powerSeriesHartogsAlgebraRecoveryData U hU V hUV hzero D).comparison

/-- Restricting the original comparison to the actual base-open pullback
recovers exactly the native tensor map followed by the geometric cover map.
The equation's type is inferred from the complete original construction;
its comparison is definitionally `powerSeriesHartogsAlgebraComparison`. -/
abbrev powerSeriesHartogsAlgebraComparison_restriction
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme) :=
  let D₀ := powerSeriesHartogsSectionCover U V hzero D
  let P := (FiniteEtale.baseChange (c ∣_ U)).obj D₀
  let D₁ := powerSeriesHartogsRestrictedCover U V hUV D
  letI := (C : A →+* B).toAlgebra
  letI : Module A B := Algebra.toModule
  letI := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
  letI := (affineScalarMap (P.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
  letI := (affineScalarMap (D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
  letI := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
  (powerSeriesHartogsAlgebraRecoveryData U hU V hUV hzero D).restriction_apply

/-- The inverse comparison uses the original restriction map, followed by
the inverses of the same actual geometric and tensor comparisons. -/
theorem powerSeriesHartogsAlgebraComparison_symm_apply
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme)
    (a : Γ(D.obj.left, ⊤)) :
    let D₀ := powerSeriesHartogsSectionCover U V hzero D
    let P := (FiniteEtale.baseChange (c ∣_ U)).obj D₀
    let D₁ := powerSeriesHartogsRestrictedCover U V hUV D
    letI := (C : A →+* B).toAlgebra
    letI : Module A B := Algebra.toModule
    letI := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
    letI := (affineScalarMap (P.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    letI := (affineScalarMap (D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
    letI := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
    (powerSeriesHartogsAlgebraComparison U hU V hUV hzero D).symm a =
      (powerSeriesHartogsSectionTensorAlgEquiv U V hzero D).symm
        ((powerSeriesHartogsRecoveryAlgEquiv U hU V hUV hzero D).symm
          ((pullback.fst D.obj.hom ((Spec (.of B)).homOfLE hUV)).appTop a)) := by
  let D₀ := powerSeriesHartogsSectionCover U V hzero D
  let P := (FiniteEtale.baseChange (c ∣_ U)).obj D₀
  let D₁ := powerSeriesHartogsRestrictedCover U V hUV D
  let := (C : A →+* B).toAlgebra
  let : Module A B := Algebra.toModule
  let := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
  let := (affineScalarMap (P.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
  let := (affineScalarMap (D₁.obj.hom ≫ (c ⁻¹ᵁ U).ι)).toAlgebra
  let := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
  dsimp only
  exact (powerSeriesHartogsAlgebraRecoveryData U hU V hUV hzero D).symm_apply a

end AlgebraicGeometry.Scheme
