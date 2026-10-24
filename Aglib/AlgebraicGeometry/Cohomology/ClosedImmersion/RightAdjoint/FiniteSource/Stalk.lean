/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FiniteSource
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.RingTheory.RegularLocalRing.NormalQuotientExt
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The original affine closed-adjoint homology at a source stalk

For the actual closed immersion `Spec (R/I) → Spec R`, localization of the
original affine Ext map identifies the actual homology stalk with Ext over
the actual ambient stalk. Both the localized quotient source and the
coefficient are identified by their original germ maps. The forward law
retains inverse source transport and forward coefficient transport around
the same exact-functor Ext map.

The finite-source tilde comparison is a lower dependency. No concentration,
dualizing-complex or trace assertion is assumed. The final local vanishing
application uses the actual normal quotient, arbitrary finite ambient
dimension, and a genuine frame of the ambient coefficient stalk.

Module Ext has the explicit native size `u`; the scheme-derived category
size remains independent. The current consumer is chosen-embedding
concentration for normal integral surfaces.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open scoped ModuleCat.Algebra TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules.FiniteSourceStalk

public instance globalSections_additive (A : CommRingCat.{u}) : (moduleSpecΓFunctor (R :=
  A)).Additive :=
  moduleSpecΓFunctor_additive A

public instance specStalkAlgebra (R : CommRingCat.{u}) (x : PrimeSpectrum R) :
    Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x

public instance specStalkLocalization (R : CommRingCat.{u}) (x : PrimeSpectrum R) :
    IsLocalization x.asIdeal.primeCompl ((Spec R).presheaf.stalk x) :=
  StructureSheaf.IsLocalization.to_stalk R x

public instance restrictedAlgebraTower {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (M : ModuleCat.{u} A) :
    IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The actual stalk map induced by a tilde comparison, with the original
structure-stalk scalar action. -/
public def tildeIsoToModuleStalk {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {N : (Spec R).Modules} (e : tilde M ≅ N) (x : PrimeSpectrum R) :
    M ⟶ (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).obj
      ((moduleStalk (Spec R) x).obj N) :=
  tilde.toStalk M x ≫
    (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).map
      ((moduleStalk (Spec R) x).map e.hom)

public theorem tildeIsoToModuleStalk_isLocalized {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) {N : (Spec R).Modules} (e : tilde M ≅ N)
    (x : PrimeSpectrum R) :
    IsLocalizedModule x.asIdeal.primeCompl (tildeIsoToModuleStalk M e x).hom :=
  IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl (tilde.toStalk M x).hom
    (((ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).mapIso
      ((moduleStalk (Spec R) x).mapIso e)).toLinearEquiv)

/-- Ambient coefficient sections map to their actual stalk by the
tilde counit and the original germ. -/
public def affineCoefficientToModuleStalk {R : CommRingCat.{u}} (N : (Spec R).Modules)
    (x : PrimeSpectrum R) :
    (moduleSpecΓFunctor (R := R)).obj N ⟶
      (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).obj
        ((moduleStalk (Spec R) x).obj N) :=
  tilde.toStalk ((moduleSpecΓFunctor (R := R)).obj N) x ≫
    (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).map
      ((moduleStalk (Spec R) x).map (fromTildeΓ (R := R) N))

public theorem affineCoefficientToModuleStalk_isLocalized {R : CommRingCat.{u}}
    (N : (Spec R).Modules) [N.IsQuasicoherent] (x : PrimeSpectrum R) :
    IsLocalizedModule x.asIdeal.primeCompl (affineCoefficientToModuleStalk N x).hom := by
  let e : tilde ((moduleSpecΓFunctor (R := R)).obj N) ≅ N :=
    @asIso _ _ _ _ (fromTildeΓ (R := R) N)
      (isIso_fromTildeΓ_of_isQuasicoherent (R := R) N)
  exact tildeIsoToModuleStalk_isLocalized (R := R) _ e x

@[simp]
public theorem affineCoefficientToModuleStalk_apply {R : CommRingCat.{u}}
    (N : (Spec R).Modules) (x : PrimeSpectrum R)
    (s : (moduleSpecΓFunctor (R := R)).obj N) :
    affineCoefficientToModuleStalk N x s = N.presheaf.germ ⊤ x trivial s := by
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
    (X := (Spec R : TopCat.{u})) x).map
    (fromTildeΓ (R := R) N).mapPresheaf
    ((tilde ((moduleSpecΓFunctor (R := R)).obj N)).presheaf.germ ⊤ x trivial
      (tilde.toOpen (R := R) ((moduleSpecΓFunctor (R := R)).obj N) ⊤ s)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  congr 1
  let G := (modulesSpecToSheaf (R := R)).obj N
  have hi : (homOfLE (show (⊤ : (Spec R).Opens) ≤ ⊤ from le_rfl)).op =
      𝟙 (Opposite.op (⊤ : (Spec R).Opens)) := Subsingleton.elim _ _
  have h₀ := (toOpen_fromTildeΓ_app (R := R) N ⊤).trans
    ((congrArg G.obj.map hi).trans (G.obj.map_id _))
  have h := ConcreteCategory.congr_hom h₀ s
  change ((fromTildeΓ (R := R) N).mapPresheaf.app (Opposite.op ⊤))
    (tilde.toOpen (R := R) ((moduleSpecΓFunctor (R := R)).obj N) ⊤ s) = s at h
  exact h

/-- The unique target-ring linear isomorphism between two actual
localizations of the same source module, with their original maps. -/
public def localizedModuleIso {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (T : Submonoid R) [IsLocalization T A]
    (M : ModuleCat.{u} R) (N N' : ModuleCat.{u} A)
    (f : M ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj N)
    (g : M ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj N')
    [IsLocalizedModule T f.hom] [IsLocalizedModule T g.hom] : N ≅ N' :=
  ((IsLocalizedModule.linearEquiv T f.hom g.hom).extendScalarsOfIsLocalization T A).toModuleIso

public theorem localizedModuleIso_apply {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (T : Submonoid R) [IsLocalization T A]
    (M : ModuleCat.{u} R) (N N' : ModuleCat.{u} A)
    (f : M ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj N)
    (g : M ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj N')
    [IsLocalizedModule T f.hom] [IsLocalizedModule T g.hom] (m : M) :
    (localizedModuleIso T M N N' f g).hom (f m) = g m := by
  change (IsLocalizedModule.linearEquiv T f.hom g.hom) (f.hom m) = g.hom m
  exact IsLocalizedModule.linearEquiv_apply T f.hom g.hom m

/-- The same localization isomorphism with the two localization proofs
supplied explicitly, retaining the exact module dictionaries of the arrows. -/
public def localizedModuleIsoOf {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (T : Submonoid R) [IsLocalization T A]
    (M : ModuleCat.{u} R) (N N' : ModuleCat.{u} A)
    (f : M ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj N)
    (g : M ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj N')
    (hf : IsLocalizedModule T f.hom) (hg : IsLocalizedModule T g.hom) : N ≅ N' :=
  @localizedModuleIso R A _ _ _ T _ M N N' f g hf hg

public theorem localizedModuleIsoOf_apply {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (T : Submonoid R) [IsLocalization T A]
    (M : ModuleCat.{u} R) (N N' : ModuleCat.{u} A)
    (f : M ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj N)
    (g : M ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj N')
    (hf : IsLocalizedModule T f.hom) (hg : IsLocalizedModule T g.hom) (m : M) :
    (localizedModuleIsoOf T M N N' f g hf hg).hom (f m) = g m :=
  @localizedModuleIso_apply R A _ _ _ T _ M N N' f g hf hg m

/-- Tensor extension of actual coefficient sections is its actual module
stalk. The forward map sends the scalar-extension unit to the original germ. -/
public def affineCoefficientModuleStalkIso {R : CommRingCat.{u}}
    (N : (Spec R).Modules) [N.IsQuasicoherent] (x : PrimeSpectrum R) :
    (ModuleCat.extendScalars (StructureSheaf.toStalk R x).hom).obj
      ((moduleSpecΓFunctor (R := R)).obj N) ≅ (moduleStalk (Spec R) x).obj N := by
  let A := (Spec R).presheaf.stalk x
  let T := x.asIdeal.primeCompl
  letI : Algebra R A := specStalkAlgebra R x
  letI : IsLocalization T A := specStalkLocalization R x
  let P := (moduleSpecΓFunctor (R := R)).obj N
  let η : P ⟶ (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).obj
      ((ModuleCat.extendScalars (StructureSheaf.toStalk R x).hom).obj P) :=
    (ModuleCat.extendRestrictScalarsAdj (StructureSheaf.toStalk R x).hom).unit.app P
  let hη : IsLocalizedModule T η.hom :=
    ModuleCat.extendRestrictScalarsAdj_unit_isLocalizedModule T
      (StructureSheaf.toStalk R x).hom
      (specStalkLocalization R x) ((moduleSpecΓFunctor (R := R)).obj N)
  let hκ : IsLocalizedModule T (affineCoefficientToModuleStalk N x).hom :=
    affineCoefficientToModuleStalk_isLocalized N x
  exact localizedModuleIsoOf (R := R) (A := A) T P
    ((ModuleCat.extendScalars (StructureSheaf.toStalk R x).hom).obj P)
    ((moduleStalk (Spec R) x).obj N) η (affineCoefficientToModuleStalk N x) hη hκ

@[simp]
public theorem affineCoefficientModuleStalkIso_unit {R : CommRingCat.{u}}
    (N : (Spec R).Modules) [N.IsQuasicoherent] (x : PrimeSpectrum R)
    (s : (moduleSpecΓFunctor (R := R)).obj N) :
    (affineCoefficientModuleStalkIso N x).hom.hom
      ((1 : (Spec R).presheaf.stalk x) ⊗ₜ[R,(StructureSheaf.toStalk R x).hom] s) =
        N.presheaf.germ ⊤ x trivial s := by
  let A := (Spec R).presheaf.stalk x
  let T := x.asIdeal.primeCompl
  let : Algebra R A := specStalkAlgebra R x
  let : IsLocalization T A := specStalkLocalization R x
  let P := (moduleSpecΓFunctor (R := R)).obj N
  let η : P ⟶ (ModuleCat.restrictScalars (StructureSheaf.toStalk R x).hom).obj
      ((ModuleCat.extendScalars (StructureSheaf.toStalk R x).hom).obj P) :=
    (ModuleCat.extendRestrictScalarsAdj (StructureSheaf.toStalk R x).hom).unit.app P
  let hη : IsLocalizedModule T η.hom :=
    ModuleCat.extendRestrictScalarsAdj_unit_isLocalizedModule T
      (StructureSheaf.toStalk R x).hom (specStalkLocalization R x) P
  let hκ : IsLocalizedModule T (affineCoefficientToModuleStalk N x).hom :=
    affineCoefficientToModuleStalk_isLocalized N x
  change (localizedModuleIsoOf (R := R) (A := A) T P _ _ η
    (affineCoefficientToModuleStalk N x) hη hκ).hom.hom (η.hom s) = _
  exact (localizedModuleIsoOf_apply (R := R) (A := A) T P _ _ η
    (affineCoefficientToModuleStalk N x) hη hκ s).trans
      (affineCoefficientToModuleStalk_apply N x s)

public theorem restrictScalars_isLocalized_of_surjective
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (hf : Function.Surjective f) (p : PrimeSpectrum A)
    (M N : ModuleCat.{u} A) (g : M ⟶ N)
    [IsLocalizedModule p.asIdeal.primeCompl g.hom] :
    IsLocalizedModule (p.comap f).asIdeal.primeCompl
      ((ModuleCat.restrictScalars f).map g).hom := by
  constructor
  · intro s
    have hs := IsLocalizedModule.map_units g.hom
      (⟨f s, s.property⟩ : p.asIdeal.primeCompl)
    rw [Module.End.isUnit_iff] at hs ⊢
    change Function.Bijective (fun m : N => f (s : R) • m)
    exact hs
  · intro m
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalizedModule.surj p.asIdeal.primeCompl g.hom m
    obtain ⟨r, hr⟩ := hf s
    refine ⟨⟨n, ⟨r, ?_⟩⟩, ?_⟩
    · change f r ∉ p.asIdeal
      rw [hr]
      exact s.property
    · change f r • (show N from m) = g.hom n
      change (s : A) • (show N from m) = g.hom n at hs
      rw [hr]
      exact hs
  · intro m n h
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
      (S := p.asIdeal.primeCompl) (f := g.hom) h
    obtain ⟨r, hr⟩ := hf s
    refine ⟨⟨r, ?_⟩, ?_⟩
    · change f r ∉ p.asIdeal
      rw [hr]
      exact s.property
    · change f r • (show M from m) = f r • (show M from n)
      change (s : A) • (show M from m) = (s : A) • (show M from n) at hs
      rw [hr]
      exact hs

public theorem ringGerm_isLocalized {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (T : Submonoid R) [IsLocalization T A] :
    IsLocalizedModule T (Algebra.linearMap R A) := by
  apply IsLocalizedModule.mkOfAlgebra T (Algebra.ofId R A)
  · intro s hs
    exact IsLocalization.map_units A ⟨s, hs⟩
  · intro y
    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj T y
    exact ⟨⟨r, s⟩, by
      simpa only [Submonoid.smul_def, Algebra.smul_def, Algebra.ofId_apply, mul_comm] using hs⟩
  · intro r hr
    obtain ⟨s, hs⟩ := IsLocalization.exists_of_eq (M := T)
      (show algebraMap R A r = algebraMap R A 0 by simpa using hr)
    exact ⟨s, by simpa only [Submonoid.smul_def, smul_eq_mul, mul_zero] using hs⟩

/-- Native Ext at size `u`, bundled with its original coefficient-ring
module structure. -/
public abbrev nativeExtModule (A : Type u) [CommRing A]
    (M N : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (Ext.{u} M N n)

/-- Transport Ext contravariantly along the source isomorphism and
covariantly along the coefficient isomorphism using the original Ext products. -/
public def extIsoTransport {R : Type u} [CommRing R]
    {X X' Y Y' : ModuleCat.{u} R} (eX : X' ≅ X) (eY : Y ≅ Y') (n : ℕ) :
    Ext.{u} X Y n ≃ₗ[R] Ext.{u} X' Y' n where
  toFun x := ((Ext.mk₀ eX.hom).comp x (zero_add n)).comp (Ext.mk₀ eY.hom) (add_zero n)
  invFun y := ((Ext.mk₀ eX.inv).comp y (zero_add n)).comp (Ext.mk₀ eY.inv) (add_zero n)
  left_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc,
      Iso.inv_hom_id, Ext.mk₀_id_comp]
  right_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc,
      Iso.hom_inv_id, Ext.mk₀_id_comp]
  map_add' x y := by simp only [Ext.comp_add, Ext.add_comp]
  map_smul' a x := by
    simp only [Ext.comp_smul, Ext.smul_comp]
    rfl

/-- The identity on native Ext, made linear for the original restricted
coefficient-scalar action. -/
public def extScalarRestrictionEquiv {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (M N : ModuleCat.{u} A) (n : ℕ) :
    Ext.{u} M N n ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R A)).obj
        (ModuleCat.of A (Ext.{u} M N n)) where
  __ := AddEquiv.refl _
  map_smul' r x := by
    change r • x = (algebraMap R A r) • x
    have hi : r • 𝟙 N = (algebraMap R A r) • 𝟙 N := by
      ext m
      rfl
    exact (Ext.smul_eq_comp_mk₀ (R := R) x r).trans
      ((congrArg (fun f => x.comp (Ext.mk₀ f) (add_zero n)) hi).trans
        (Ext.smul_eq_comp_mk₀ (R := A) x (algebraMap R A r)).symm)

section ScalarExtensionExt

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (T : Submonoid R) [IsLocalization T A]

/-- The original scalar-extension Ext arrow, bundled over variable rings
before specialization to an actual stalk. -/
public def scalarExtensionExtMap (M N : ModuleCat.{u} R) (n : ℕ) :
    nativeExtModule R M N n ⟶
      (ModuleCat.restrictScalars (algebraMap R A)).obj
        (nativeExtModule A ((ModuleCat.extendScalars (algebraMap R A)).obj M)
          ((ModuleCat.extendScalars (algebraMap R A)).obj N) n) := by
  letI : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
  letI : PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
  let β : Ext.{u} M N n →ₗ[R]
      Ext.{u} ((ModuleCat.extendScalars (algebraMap R A)).obj M)
        ((ModuleCat.extendScalars (algebraMap R A)).obj N) n :=
    (ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R M N n
  exact ModuleCat.ofHom
    ((extScalarRestrictionEquiv (R := R) (A := A)
      ((ModuleCat.extendScalars (algebraMap R A)).obj M)
      ((ModuleCat.extendScalars (algebraMap R A)).obj N) n).toLinearMap.comp
        β)

public theorem scalarExtensionExtMap_isLocalized [IsNoetherianRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    IsLocalizedModule T (scalarExtensionExtMap (A := A) T M N n).hom := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
  let : PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
  let β : Ext.{u} M N n →ₗ[R]
      Ext.{u} ((ModuleCat.extendScalars (algebraMap R A)).obj M)
        ((ModuleCat.extendScalars (algebraMap R A)).obj N) n :=
    (ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R M N n
  let e := extScalarRestrictionEquiv (R := R) (A := A)
    ((ModuleCat.extendScalars (algebraMap R A)).obj M)
    ((ModuleCat.extendScalars (algebraMap R A)).obj N) n
  change IsLocalizedModule T (e.toLinearMap.comp β)
  exact (IsLocalizedModule.comp_iff_of_bijective_left T (f := β)
    e.toLinearMap e.bijective).mpr
      (ModuleCat.extScalarExtension_isLocalized_of_finite T M N n)

end ScalarExtensionExt

section QuotientStalk

variable {R : CommRingCat.{u}} (I : Ideal R) (x : PrimeSpectrum (R ⧸ I))

/-- The actual quotient coefficient ring defining the closed source. -/
public abbrev quotientRing : CommRingCat.{u} := .of (R ⧸ I)

/-- The original quotient homomorphism, bundled in commutative rings. -/
public abbrev quotientMap : R ⟶ quotientRing I := CommRingCat.ofHom (Ideal.Quotient.mk I)

/-- The ambient point under the original quotient closed immersion. -/
public abbrev imagePoint : PrimeSpectrum R := (Spec.map (quotientMap I)) x

/-- The actual structure stalk at the ambient image point. -/
public abbrev ambientRing : CommRingCat.{u} := (Spec R).presheaf.stalk (imagePoint I x)

/-- The actual structure stalk at the chosen source point. -/
public abbrev sourceRing : CommRingCat.{u} := (Spec (quotientRing I)).presheaf.stalk x

/-- The structure-stalk homomorphism of the original quotient closed immersion. -/
public abbrev stalkMap : ambientRing I x ⟶ sourceRing I x :=
  (Spec.map (quotientMap I)).stalkMap x

/-- The multiplicative complement of the ambient image prime. -/
public abbrev primeComplement : Submonoid R := (imagePoint I x).asIdeal.primeCompl

/-- Native extension of scalars along the original ambient ring germ. -/
public abbrev scalarExtension :=
  ModuleCat.extendScalars (StructureSheaf.toStalk R (imagePoint I x)).hom

/-- The original quotient module with scalars restricted along the quotient map. -/
public abbrev sourceModule : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (quotientMap I).hom).obj (ModuleCat.of (quotientRing I) (quotientRing
    I))

public instance quotientClosedImmersion : IsClosedImmersion (Spec.map (quotientMap I)) :=
  inferInstanceAs (IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))

public instance quotientSections_additive :
    (moduleSpecΓFunctor (R := quotientRing I)).Additive :=
  moduleSpecΓFunctor_additive (quotientRing I)

public instance quotientSections_preservesZero :
    (moduleSpecΓFunctor (R := quotientRing I)).PreservesZeroMorphisms := by
  infer_instance

public instance ambientStalkAlgebra : Algebra R (ambientRing I x) :=
  specStalkAlgebra R (imagePoint I x)

public instance ambientStalkLocalization :
    IsLocalization (primeComplement I x) (ambientRing I x) :=
  specStalkLocalization R (imagePoint I x)

public instance scalarExtension_linear : (scalarExtension I x).Linear R :=
  ModuleCat.Algebra.extendScalars_linear R (ambientRing I x)

public instance sourceStalkAlgebra : Algebra (quotientRing I) (sourceRing I x) :=
  specStalkAlgebra (quotientRing I) x

public instance sourceStalkLocalization :
    IsLocalization x.asIdeal.primeCompl (sourceRing I x) :=
  specStalkLocalization (quotientRing I) x

public instance sourceStalkLocalRing : IsLocalRing (sourceRing I x) :=
  (Spec (quotientRing I)).toLocallyRingedSpace.isLocalRing x

public instance stalkMap_isLocalHom : IsLocalHom (stalkMap I x).hom :=
  (Spec.map (quotientMap I)).prop x

/-- The original quotient-ring germ, bundled as a quotient-linear module map. -/
public def sourceChartGerm : ModuleCat.of (quotientRing I) (quotientRing I) ⟶
    (ModuleCat.restrictScalars (StructureSheaf.toStalk (quotientRing I) x).hom).obj
      (ModuleCat.of (sourceRing I x) (sourceRing I x)) := ModuleCat.ofHom
  { toFun := StructureSheaf.toStalk (quotientRing I) x
    map_add' := map_add _
    map_smul' a b := by
      change (StructureSheaf.toStalk (quotientRing I) x) (a * b) =
        (StructureSheaf.toStalk (quotientRing I) x) a *
          (StructureSheaf.toStalk (quotientRing I) x) b
      exact map_mul _ a b }

/-- The actual stalk scalar square identifies the two iterated restrictions
of a source-stalk module to the ambient affine ring. -/
public def stalkScalarIso (N : ModuleCat.{u} (sourceRing I x)) :
    (ModuleCat.restrictScalars (quotientMap I).hom).obj
        ((ModuleCat.restrictScalars (StructureSheaf.toStalk (quotientRing I) x).hom).obj N) ≅
      (ModuleCat.restrictScalars (StructureSheaf.toStalk R (imagePoint I x)).hom).obj
        ((ModuleCat.restrictScalars (stalkMap I x).hom).obj N) := by
  have he : (stalkMap I x).hom.comp (StructureSheaf.toStalk R (imagePoint I x)).hom =
      (StructureSheaf.toStalk (quotientRing I) x).hom.comp (quotientMap I).hom :=
    congrArg CommRingCat.Hom.hom (AlgebraicGeometry.stalkMap_toStalk (quotientMap I) x)
  exact ((ModuleCat.restrictScalarsComp (quotientMap I).hom
      (StructureSheaf.toStalk (quotientRing I) x).hom).app N).symm ≪≫
    (ModuleCat.restrictScalarsCongr he.symm).app N ≪≫
    (ModuleCat.restrictScalarsComp (StructureSheaf.toStalk R (imagePoint I x)).hom
      (stalkMap I x).hom).app N

/-- The original source germ with ambient scalars transported through the
actual closed-immersion stalk square. -/
public def sourceGerm : sourceModule I ⟶
    (ModuleCat.restrictScalars (StructureSheaf.toStalk R (imagePoint I x)).hom).obj
      ((ModuleCat.restrictScalars (stalkMap I x).hom).obj
        (ModuleCat.of (sourceRing I x) (sourceRing I x))) :=
  (ModuleCat.restrictScalars (quotientMap I).hom).map
      (sourceChartGerm I x) ≫
    (stalkScalarIso I x (ModuleCat.of (sourceRing I x) (sourceRing I x))).hom

public theorem sourceGerm_isLocalized :
    IsLocalizedModule (primeComplement I x) (sourceGerm I x).hom := by
  let g := sourceChartGerm I x
  let : IsLocalizedModule x.asIdeal.primeCompl g.hom := by
    change IsLocalizedModule x.asIdeal.primeCompl
      (Algebra.linearMap (quotientRing I) (sourceRing I x))
    exact ringGerm_isLocalized _
  let : IsLocalizedModule (primeComplement I x)
      ((ModuleCat.restrictScalars (quotientMap I).hom).map g).hom :=
    restrictScalars_isLocalized_of_surjective (quotientMap I).hom
      Ideal.Quotient.mk_surjective x _ _ g
  exact IsLocalizedModule.of_linearEquiv (primeComplement I x) _ (stalkScalarIso I x
    _).toLinearEquiv

/-- Localization of the original quotient module is the actual source stalk
with its scalar action through the original closed-immersion stalk map. -/
public def closedImmersionQuotientStalkSourceIso :
    (scalarExtension I x).obj (sourceModule I) ≅
      (ModuleCat.restrictScalars (stalkMap I x).hom).obj (ModuleCat.of (sourceRing I x)
        (sourceRing I x)) := by
  let η : sourceModule I ⟶
      (ModuleCat.restrictScalars (StructureSheaf.toStalk R (imagePoint I x)).hom).obj
        ((scalarExtension I x).obj (sourceModule I)) :=
    (ModuleCat.extendRestrictScalarsAdj
      (StructureSheaf.toStalk R (imagePoint I x)).hom).unit.app (sourceModule I)
  let hη : IsLocalizedModule (primeComplement I x) η.hom :=
    ModuleCat.extendRestrictScalarsAdj_unit_isLocalizedModule (primeComplement I x)
      (StructureSheaf.toStalk R (imagePoint I x)).hom
      (specStalkLocalization R (imagePoint I x)) (sourceModule I)
  let hκ : IsLocalizedModule (primeComplement I x) (sourceGerm I x).hom :=
    sourceGerm_isLocalized I x
  exact localizedModuleIsoOf (R := R) (A := ambientRing I x) (primeComplement I x)
    (sourceModule I) ((scalarExtension I x).obj (sourceModule I))
    ((ModuleCat.restrictScalars (stalkMap I x).hom).obj
      (ModuleCat.of (sourceRing I x) (sourceRing I x))) η (sourceGerm I x) hη hκ

variable [IsNoetherianRing R] {L : (Spec R).Modules} [L.IsQuasicoherent]
    (J : InjectiveResolution L)

/-- Homology of original quotient-chart sections of the closed-adjoint
resolution complex. -/
public abbrev sectionHomology (J : InjectiveResolution L) (n : ℕ) : ModuleCat.{u}
    (quotientRing I) := by
  letI : (moduleSpecΓFunctor (R := quotientRing I)).Additive :=
    moduleSpecΓFunctor_additive (quotientRing I)
  exact ((((moduleSpecΓFunctor (R := quotientRing I)).mapHomologicalComplex (.up ℤ)).obj
    (closedImmersionRightAdjointQuotientResolutionComplex I J)).homology (n : ℤ))

/-- The actual source stalk of homology of the closed-adjoint resolution complex. -/
public abbrev stalkHomology (J : InjectiveResolution L) (n : ℕ) : ModuleCat.{u}
  (sourceRing I x) :=
  (moduleStalk (Spec (quotientRing I)) x).obj
    ((closedImmersionRightAdjointQuotientResolutionComplex I J).homology (n : ℤ))

/-- Original section homology maps to the actual source stalk through the
homology map of the original tilde counit. -/
public def closedImmersionQuotientHomologyToStalk (n : ℕ) :
    (ModuleCat.restrictScalars (quotientMap I).hom).obj (sectionHomology I J n) ⟶
      (ModuleCat.restrictScalars (StructureSheaf.toStalk R (imagePoint I x)).hom).obj
        ((ModuleCat.restrictScalars (stalkMap I x).hom).obj (stalkHomology I x J n)) :=
  (ModuleCat.restrictScalars (quotientMap I).hom).map
      (tildeIsoToModuleStalk (R := quotientRing I) (sectionHomology I J n)
        (closedImmersionRightAdjointQuotientResolutionHomologyIso I J (n : ℤ)) x) ≫
    (stalkScalarIso I x (stalkHomology I x J n)).hom

public theorem homologyToStalk_isLocalized (n : ℕ) :
    IsLocalizedModule (primeComplement I x) (closedImmersionQuotientHomologyToStalk I x J n).hom
      := by
  let g := tildeIsoToModuleStalk (R := quotientRing I) (sectionHomology I J n)
    (closedImmersionRightAdjointQuotientResolutionHomologyIso I J (n : ℤ)) x
  let : IsLocalizedModule x.asIdeal.primeCompl g.hom :=
    tildeIsoToModuleStalk_isLocalized (R := quotientRing I) (sectionHomology I J n)
      (closedImmersionRightAdjointQuotientResolutionHomologyIso I J (n : ℤ)) x
  let : IsLocalizedModule (primeComplement I x)
      ((ModuleCat.restrictScalars (quotientMap I).hom).map g).hom :=
    restrictScalars_isLocalized_of_surjective (quotientMap I).hom
      Ideal.Quotient.mk_surjective x _ _ g
  exact IsLocalizedModule.of_linearEquiv (primeComplement I x) _ (stalkScalarIso I x
    _).toLinearEquiv

public instance : PreservesFiniteLimits (scalarExtension I x) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (ambientRing I x) (primeComplement I x)))
public instance : PreservesFiniteColimits (scalarExtension I x) :=
  ModuleCat.extendScalars_preservesFiniteColimits_of_flat _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (ambientRing I x) (primeComplement I x)))

/-- Native Ext over the actual ambient stalk of the scalar-extended
quotient source and original coefficient sections. -/
public abbrev localExt (n : ℕ) :=
  Ext.{u} ((scalarExtension I x).obj (sourceModule I))
    ((scalarExtension I x).obj ((moduleSpecΓFunctor (R := R)).obj L)) n

/-- Original section homology maps to ambient-stalk Ext by the affine Ext
comparison followed by its native exact scalar-extension map. -/
public def sectionHomologyToLocalExt (n : ℕ) :
    (ModuleCat.restrictScalars (quotientMap I).hom).obj (sectionHomology I J n) ⟶
      (ModuleCat.restrictScalars (StructureSheaf.toStalk R (imagePoint I x)).hom).obj
        (nativeExtModule (ambientRing I x) ((scalarExtension I x).obj (sourceModule I))
          ((scalarExtension I x).obj ((moduleSpecΓFunctor (R := R)).obj L)) n) := by
  let α : (ModuleCat.restrictScalars (quotientMap I).hom).obj (sectionHomology I J n) ≅
      nativeExtModule R (sourceModule I) ((moduleSpecΓFunctor (R := R)).obj L) n :=
    (affineClosedRightAdjointResolutionExtLinearEquiv.{u, u} (quotientMap I) J n).toModuleIso
  exact α.hom ≫ scalarExtensionExtMap (R := R) (A := ambientRing I x)
    (primeComplement I x) (sourceModule I) ((moduleSpecΓFunctor (R := R)).obj L) n

public theorem sectionHomologyToLocalExt_isLocalized (n : ℕ) :
    IsLocalizedModule (primeComplement I x) (sectionHomologyToLocalExt I x J n).hom := by
  let g : R →ₗ[R] sourceModule I :=
    { toFun := Ideal.Quotient.mk I
      map_add' := map_add _
      map_smul' r s := by
        change Ideal.Quotient.mk I (r * s) =
          Ideal.Quotient.mk I r * Ideal.Quotient.mk I s
        exact map_mul (Ideal.Quotient.mk I) r s }
  let : Module.Finite R (sourceModule I) :=
    Module.Finite.of_surjective g Ideal.Quotient.mk_surjective
  let α : (ModuleCat.restrictScalars (quotientMap I).hom).obj (sectionHomology I J n) ≅
      nativeExtModule R (sourceModule I) ((moduleSpecΓFunctor (R := R)).obj L) n :=
    (affineClosedRightAdjointResolutionExtLinearEquiv.{u, u} (quotientMap I) J n).toModuleIso
  let β := scalarExtensionExtMap (R := R) (A := ambientRing I x)
    (primeComplement I x) (sourceModule I) ((moduleSpecΓFunctor (R := R)).obj L) n
  change IsLocalizedModule (primeComplement I x) (β.hom.comp α.hom.hom)
  exact (IsLocalizedModule.comp_iff_of_bijective_right (primeComplement I x)
    (f := β.hom) α.hom.hom (ConcreteCategory.bijective_of_isIso α.hom)).mpr
      (scalarExtensionExtMap_isLocalized (R := R) (A := ambientRing I x)
        (primeComplement I x) (sourceModule I) ((moduleSpecΓFunctor (R := R)).obj L) n)

/-- Homology of the original closed-adjoint complex at the actual source
point is Ext over the actual ambient stalk, for the original coefficient stalk. -/
public def closedImmersionQuotientHomologyStalkExtLinearEquiv (n : ℕ) :
    (ModuleCat.restrictScalars (stalkMap I x).hom).obj (stalkHomology I x J n) ≃ₗ[ambientRing I x]
      Ext.{u} ((ModuleCat.restrictScalars (stalkMap I x).hom).obj
        (ModuleCat.of (sourceRing I x) (sourceRing I x))) ((moduleStalk (Spec R) (imagePoint I
          x)).obj L) n := by
  let P := (ModuleCat.restrictScalars (quotientMap I).hom).obj (sectionHomology I J n)
  let U := (ModuleCat.restrictScalars (stalkMap I x).hom).obj (stalkHomology I x J n)
  let V := nativeExtModule (ambientRing I x) ((scalarExtension I x).obj (sourceModule I))
    ((scalarExtension I x).obj ((moduleSpecΓFunctor (R := R)).obj L)) n
  letI : AddCommGroup V := V.isAddCommGroup
  letI : Module (ambientRing I x) V := V.isModule
  let κ : P ⟶ (ModuleCat.restrictScalars
      (StructureSheaf.toStalk R (imagePoint I x)).hom).obj U :=
    closedImmersionQuotientHomologyToStalk I x J n
  let g : P ⟶ (ModuleCat.restrictScalars
      (StructureSheaf.toStalk R (imagePoint I x)).hom).obj V :=
    sectionHomologyToLocalExt I x J n
  let hκ : IsLocalizedModule (primeComplement I x) κ.hom := homologyToStalk_isLocalized I x J n
  let hg : IsLocalizedModule (primeComplement I x) g.hom := sectionHomologyToLocalExt_isLocalized
    I x
    J n
  let e : U ≅ V := localizedModuleIsoOf (R := R) (A := ambientRing I x)
    (primeComplement I x) P U V κ g hκ hg
  let t : V ≃ₗ[ambientRing I x]
      Ext.{u} ((ModuleCat.restrictScalars (stalkMap I x).hom).obj
        (ModuleCat.of (sourceRing I x) (sourceRing I x)))
        ((moduleStalk (Spec R) (imagePoint I x)).obj L) n :=
    extIsoTransport (closedImmersionQuotientStalkSourceIso I x).symm
      (affineCoefficientModuleStalkIso L (imagePoint I x)) n
  exact e.toLinearEquiv.trans t

/-- On original section-homology germs, the stalk comparison is the same
exact-functor Ext map, with inverse source and forward coefficient transport. -/
public theorem closedImmersionQuotientHomologyStalkExtLinearEquiv_germ (n : ℕ)
    (s : sectionHomology I J n) :
    closedImmersionQuotientHomologyStalkExtLinearEquiv I x J n
        (closedImmersionQuotientHomologyToStalk I x J n s) =
      ((Ext.mk₀ (closedImmersionQuotientStalkSourceIso I x).inv).comp
        ((affineClosedRightAdjointResolutionExtLinearEquiv.{u, u} (quotientMap I) J n
          s).mapExactFunctor
          (scalarExtension I x)) (zero_add n)).comp
        (Ext.mk₀ (affineCoefficientModuleStalkIso L (imagePoint I x)).hom) (add_zero n) := by
  let P := (ModuleCat.restrictScalars (quotientMap I).hom).obj (sectionHomology I J n)
  let U := (ModuleCat.restrictScalars (stalkMap I x).hom).obj (stalkHomology I x J n)
  let V := nativeExtModule (ambientRing I x) ((scalarExtension I x).obj (sourceModule I))
    ((scalarExtension I x).obj ((moduleSpecΓFunctor (R := R)).obj L)) n
  let : AddCommGroup V := V.isAddCommGroup
  let : Module (ambientRing I x) V := V.isModule
  let κ : P ⟶ (ModuleCat.restrictScalars
      (StructureSheaf.toStalk R (imagePoint I x)).hom).obj U :=
    closedImmersionQuotientHomologyToStalk I x J n
  let g : P ⟶ (ModuleCat.restrictScalars
      (StructureSheaf.toStalk R (imagePoint I x)).hom).obj V :=
    sectionHomologyToLocalExt I x J n
  let hκ : IsLocalizedModule (primeComplement I x) κ.hom := homologyToStalk_isLocalized I x J n
  let hg : IsLocalizedModule (primeComplement I x) g.hom :=
    sectionHomologyToLocalExt_isLocalized I x J n
  change extIsoTransport _ _ n
    ((localizedModuleIsoOf (R := R) (A := ambientRing I x)
      (primeComplement I x) P U V κ g hκ hg).hom.hom (κ.hom s)) = _
  have h := localizedModuleIsoOf_apply (R := R) (A := ambientRing I x)
    (primeComplement I x) P U V κ g hκ hg s
  exact (congrArg (extIsoTransport (closedImmersionQuotientStalkSourceIso I x).symm
    (affineCoefficientModuleStalkIso L (imagePoint I x)) n) h).trans (by rfl)

/-- A genuine frame of the original ambient coefficient stalk reduces the
local vanishing calculation to the proved arbitrary-dimensional normal quotient theorem. -/
public theorem closedImmersionQuotientHomologyStalk_subsingleton_of_coefficientFrame
    [IsRegularLocalRing (ambientRing I x)] [IsNoetherianRing (sourceRing I x)]
    [IsDomain (sourceRing I x)] [IsIntegrallyClosed (sourceRing I x)]
    (eL : (moduleStalk (Spec R) (imagePoint I x)).obj L ≅ ModuleCat.of (ambientRing I x)
      (ambientRing I x))
    (d r : ℕ) (hd : ringKrullDim (ambientRing I x) = (d : ℕ))
    (hr : ringKrullDim (sourceRing I x) = (r : ℕ)) (hr2 : r ≤ 2)
    (n : ℕ) (hn : n + r ≠ d) : Subsingleton (stalkHomology I x J n) := by
  let := (stalkMap I x).hom.toAlgebra
  let eB : ModuleCat.of (ambientRing I x) (sourceRing I x) ≅
      (ModuleCat.restrictScalars (stalkMap I x).hom).obj (ModuleCat.of (sourceRing I x)
        (sourceRing I x)) :=
    (LinearEquiv.refl (ambientRing I x) (sourceRing I x)).toModuleIso
  let e := (closedImmersionQuotientHomologyStalkExtLinearEquiv I x J n).trans
    (extIsoTransport eB eL n)
  let : Subsingleton (Ext.{u} (ModuleCat.of (ambientRing I x) (sourceRing I x))
      (ModuleCat.of (ambientRing I x) (ambientRing I x)) n) :=
    (stalkMap I x).hom.subsingleton_ext_of_surjective_normal_dimension_le_two
      ((Spec.map (quotientMap I)).stalkMap_surjective x) d r hd hr hr2 n hn
  exact e.toEquiv.subsingleton

end QuotientStalk

end AlgebraicGeometry.Scheme.Modules.FiniteSourceStalk
