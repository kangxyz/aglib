/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.EtalePullback
public import Aglib.AlgebraicGeometry.Modules.Differentials.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSheafification
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free
public import Aglib.RingTheory.Kaehler.StandardSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth rank of the actual differential sheaf

Canonical affine localization maps identify the actual differential sheaf with
the tilde of the Kahler module. Standard-smooth presentations supply the basis,
and the existing canonical etale differential pullback glues these free charts.
The actual differential sheaf has the stated rank in every relative dimension
over every field in the original universe, including on the empty scheme.

Source: `R5Lab/AlgebraicGeometry/Curves/Differentials/SmoothRank.lean` at frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`,
SHA-256 `bab90251fd10024bc7477d90539648aa6b08e4047f6d288f0e755b0b852443b5`.
The source free-cover and tilde-basis prerequisites have separate general owners.
-/

@[expose] public section
open AlgebraicGeometry.Scheme (constantSection constants)
open AlgebraicGeometry.Scheme.Modules.Differentials
  (constantsPresheafMap differentialPresheaf differentialPullbackMap differentialSheaf)
open AlgebraicGeometry.Scheme.OverField (FScheme)

noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

-- Compatibility names for the sole generic affine-localization implementation.
export AlgebraicGeometry.Scheme.Modules
  (affinePresheafModules presheafModule presheafModuleTower affineBasicComparison
    affineComparisonR affineComparison affineComparison_basic_bijective
    affineComparison_locallyInjective affineComparison_locallySurjective
    affineSheafificationTildeIso affineSheafificationTildeIso_homEquiv
    affineSheafificationTildeIso_seed)

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

-- Compatibility names for the sole arbitrary-ring affine differential implementation.
export AlgebraicGeometry.Scheme.Modules.Differentials
  (affineRelativeConstants affineRelativeDifferentials affineRelativeSeedApp
    affineRelativeSeedApp_d affineRelativeSeed affineRelativeSeed_localizing
    affineRelativeDifferentialIso)

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank
universe u v

/-- A standard smooth presentation of relative dimension `n` supplies a basis of its
differential module. -/
def standardSmoothDifferentialBasis
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    Module.Basis (Fin n) S Ω[S⁄R] :=
  KaehlerDifferential.standardSmoothBasis R S n

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank
universe u
variable (F S : Type u) [Field F] [CommRing S] [Algebra F S]

/-- The spectrum of an algebra with its structural morphism to the field spectrum. -/
def affineFScheme : FScheme F :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F S)))

/-- Constants on the affine field scheme are restrictions of the original algebra map. -/
theorem affineConstantSection (U : (Spec (CommRingCat.of S)).Opens) :
    constantSection (affineFScheme F S) U =
      ((Scheme.ΓSpecIso (.of S)).inv ≫ (Spec (.of S)).presheaf.map U.leTop.op).hom.comp
        (algebraMap F S) := by
  ext a
  dsimp [constantSection, constants, affineFScheme]
  change ((Scheme.ΓSpecIso (.of F)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap F S))).appTop ≫
      (Spec (.of S)).presheaf.map U.leTop.op) a = _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- The affine field scheme has precisely the constants presheaf of its algebra map. -/
theorem constantsPresheafMap_affineFScheme :
    constantsPresheafMap (affineFScheme F S) =
      affineRelativeConstants (CommRingCat.ofHom (algebraMap F S)) := by
  ext U a
  change constantSection (affineFScheme F S) U.unop a = _
  rw [affineConstantSection]
  rfl

/-- Actual differential/tilde identification on an affine scheme over the field. -/
def differentialSheafAffineIso :
    differentialSheaf (affineFScheme F S) ≅
      tilde (CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap F S))) := by
  dsimp only [differentialSheaf, differentialPresheaf]
  rw [constantsPresheafMap_affineFScheme]
  exact affineRelativeDifferentialIso _

/-- The actual affine differential sheaf is free with the standard-smooth basis. -/
def standardSmoothAffineFreeIso (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n F S] :
    SheafOfModules.free (R := (Spec (.of S)).ringCatSheaf) (ULift.{u} (Fin n)) ≅
      differentialSheaf (affineFScheme F S) := by
  let b : Module.Basis (ULift.{u} (Fin n)) (CommRingCat.of S)
      (CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap F S))) := by
    let f : CommRingCat.of F ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap F S)
    have hf : RingHom.IsStandardSmoothOfRelativeDimension n f.hom := by
      change RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap F S)
      exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mpr inferInstance
    letI : Algebra (CommRingCat.of F) (CommRingCat.of S) := f.hom.toAlgebra
    letI : Algebra.IsStandardSmoothOfRelativeDimension n (CommRingCat.of F) (CommRingCat.of S) :=
      hf.toAlgebra
    change Module.Basis (ULift.{u} (Fin n)) (CommRingCat.of S)
      Ω[(CommRingCat.of S)⁄(CommRingCat.of F)]
    exact (standardSmoothDifferentialBasis (CommRingCat.of F) (CommRingCat.of S) n).reindex
      Equiv.ulift.symm
  exact (Scheme.Modules.tildeBasisIso _ b).symm ≪≫
    (differentialSheafAffineIso F S).symm

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank
universe u
variable {F : Type u} [Field F] (X : FScheme F)

/-- A constant section is the structural map on sections after the canonical
field-spectrum comparison. -/
lemma constantSection_eq_appLE (V : X.left.Opens) :
    CommRingCat.ofHom (constantSection X V) =
      (Scheme.ΓSpecIso (.of F)).inv ≫ X.hom.appLE ⊤ V (by simp) := by
  rfl

/-- The canonical spectrum chart commutes with the structural morphism to the field. -/
lemma fromSpec_overField (V : X.left.Opens) (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (constantSection X V)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
    (isAffineOpen_top _) hV (show V ≤ X.hom ⁻¹ᵁ ⊤ by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h, ← constantSection_eq_appLE]

/-- A smooth field scheme of relative dimension `n` has standard smooth affine charts
of dimension `n`. -/
lemma exists_standardSmoothChart (n : ℕ) [SmoothOfRelativeDimension n X.hom] (x : X.left) :
    ∃ (V : X.left.Opens), IsAffineOpen V ∧ x ∈ V ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (constantSection X V) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := X.hom) x
  have hxU : X.hom x ∈ U := e hx
  have htop : U = ⊤ := by
    ext y
    constructor
    · intro; trivial
    · intro
      have hy : y = X.hom x := Subsingleton.elim _ _
      subst y
      exact hxU
  subst U
  refine ⟨V, hV, hx, ?_⟩
  have h := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).2
    (X.hom.appLE ⊤ V e).hom
    (Scheme.ΓSpecIso (.of F)).symm.commRingCatIsoToRingEquiv hf
  change RingHom.IsStandardSmoothOfRelativeDimension n
    ((Scheme.ΓSpecIso (.of F)).inv ≫ X.hom.appLE ⊤ V e).hom at h
  simpa only [← constantSection_eq_appLE, CommRingCat.hom_ofHom] using h

/-- Actual free differential presentation on a standard-smooth affine chart. -/
def standardSmoothChartFreeIso (n : ℕ) (V : X.left.Opens) (hV : IsAffineOpen V)
    (hstd : RingHom.IsStandardSmoothOfRelativeDimension n (constantSection X V)) :
    SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) ≅
      (differentialSheaf X).restrict V.ι := by
  letI : Algebra F Γ(X.left, V) := (constantSection X V).toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension n F Γ(X.left, V) := hstd.toAlgebra
  let a : affineFScheme F Γ(X.left, V) ⟶ X :=
    Over.homMk hV.fromSpec (fromSpec_overField X V hV)
  letI : Etale a.left := inferInstanceAs (Etale hV.fromSpec)
  letI := EtalePullback.isIso_differentialPullbackMap a
  let c : SheafOfModules.free (R := (Spec Γ(X.left, V)).ringCatSheaf)
      (ULift.{u} (Fin n)) ≅ (differentialSheaf X).restrict hV.fromSpec :=
    standardSmoothAffineFreeIso F Γ(X.left, V) n ≪≫
      (asIso (differentialPullbackMap a)).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).app (differentialSheaf X)).symm
  exact Scheme.Modules.freeIsoOfRestrictIso hV.isoSpec.symm
    ((differentialSheaf X).restrict V.ι)
    (c ≪≫ (Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι).app (differentialSheaf X))

end AlgebraicGeometry.Scheme.Modules.Differentials.SmoothRank

namespace AlgebraicGeometry.Scheme.Modules.Differentials

universe u

/-- Smooth differentials have actual local bases of the specified relative rank. -/
theorem differentialSheaf_hasRank_of_smooth (K : Type u) [Field K] (X : FScheme K) (n : ℕ)
    (hX : SmoothOfRelativeDimension n X.hom) :
    Scheme.Modules.SheafHasRank (differentialSheaf X) n := by
  letI := hX
  classical
  choose V hV hx hstd using SmoothRank.exists_standardSmoothChart X n
  have hcov : IsOpenCover V := by
    change (⨆ x : X.left, V x) = ⊤
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  exact Scheme.Modules.sheafHasRank_of_coverFreeIso V hcov
    (fun x ↦ SmoothRank.standardSmoothChartFreeIso X n (V x) (hV x) (hstd x))

variable {F : Type u} [Field F]

/-- Smooth relative differentials are finite locally free, with the basis supplied by their rank. -/
theorem smoothDifferential_finiteLocallyFree (X : FScheme F) (n : ℕ)
    (hX : SmoothOfRelativeDimension n X.hom) :
    Scheme.Modules.SheafFiniteLocallyFree (differentialSheaf X) := by
  exact (differentialSheaf_hasRank_of_smooth F X n hX).isFiniteLocallyFree

end AlgebraicGeometry.Scheme.Modules.Differentials
