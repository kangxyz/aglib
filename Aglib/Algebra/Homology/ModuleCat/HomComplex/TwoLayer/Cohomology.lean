/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Cohomology.Derived
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.NormalCoefficient
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthExtDuality
public import Aglib.CategoryTheory.Triangulated.Yoneda.Exact
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Unit
public import Mathlib.Algebra.Exact.Basic

/-!
# The original two-layer dual obstruction

Native derived-Hom comparisons and the original unsigned Yoneda row give
amplitude [0,1] and finite-length H1 for the actual coinduced dual of a
two-layer triangle over a regular local surface base. The unit and H1
maps are homology of the original contravariant dual maps. The boundary
is composition with the actual third triangle arrow, with native shifts.
The proof uses no triangulated-dual, splitting or biduality premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated CategoryTheory.Abelian Opposite HomologicalComplex

universe u w

namespace CochainComplex.HomComplex.TwoLayerDual

/-- The literal coinduced coefficient of the supplied original base resolution. -/
abbrev resolutionCoefficient {R A : Type u} [CommRing R] [CommRing A]
    (σ : R →+* A) (I : InjectiveResolution (ModuleCat.of R R)) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  coinducedCoefficientComplex σ I.cochainComplex

private theorem normalized_linear_comparison
    {A : Type*} [CommRing A] {L M N : ModuleCat.{u} A}
    {P : Type*} [AddCommGroup P] [Module A P]
    (e : M ≅ N) (d : M ≃ₗ[A] P) (f : L →ₗ[A] M) (x : L) :
    (e.symm.toLinearEquiv.trans d) (e.hom.hom.comp f x) = d (f x) := by
  change d (e.toLinearEquiv.symm (e.toLinearEquiv (f x))) = d (f x)
  rw [LinearEquiv.symm_apply_apply]

/-- Finite R-length descends to the intrinsic A-action along the actual restriction. -/
private theorem finiteLength_of_restriction
    {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (M : ModuleCat.{u} A)
    (hM : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj M)) : IsFiniteLength A M := by
  let : Algebra R A := σ.toAlgebra
  let : Module R M := Module.compHom M σ
  let : IsScalarTower R A M := ⟨fun r a m => by
    change (σ r * a) • m = σ r • (a • m)
    exact mul_smul _ _ _⟩
  have hM' : IsFiniteLength R M := hM
  have h := isFiniteLength_iff_isNoetherian_isArtinian.mp hM'
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower R (S := A) (M := M) h.1,
      isArtinian_of_tower R (S := A) (M := M) h.2⟩


section Comparisons

variable {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The original regular module in native derived degree zero. -/
abbrev regularSource (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] : DerivedCategory (ModuleCat.{u} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)

/-- The original first cohomology module in native derived degree one. -/
abbrev firstLayer (H : ModuleCat.{u} A) : DerivedCategory (ModuleCat.{u} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj H

/-- Native module homology of the actual derived dual. -/
abbrev homology (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective]
    (n : ℤ) (X : DerivedCategory (ModuleCat.{u} A)) : ModuleCat.{u} A :=
  (derivedDualHomologyFunctor.{u, u, w} J n).obj (op X)

/-- The original model comparison for the native degree-zero single. -/
def singleHomologyIso (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective]
    (M : ModuleCat.{u} A) (n : ℤ) :
    homology J n ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      (moduleComplex A ((singleFunctor (ModuleCat.{u} A) 0).obj M) J).homology n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
      ((derivedDual J).mapIso
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M).symm.op)) ≪≫
    (derivedDualHomologyModelNatIso.{u, u, w} J n).app
      (op ((singleFunctor (ModuleCat.{u} A) 0).obj M))

/-- The native single and shift comparisons move the source degree one
into a target shift by one, without introducing a dual shift structure. -/
def singleOneHomEquiv (M : ModuleCat.{u} A)
    (V : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj M) ⟶ V⟦n⟧) ≃ₗ[A]
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶ V⟦n + 1⟧) := by
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  let τ : S⟦(-1 : ℤ)⟧ ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj M :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-1) 1 0 (by omega)).app M
  let F := CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)
  let e : (S⟦(-1 : ℤ)⟧ ⟶ V⟦n⟧) ≃ₗ[A]
      (F.obj (S⟦(-1 : ℤ)⟧) ⟶ F.obj (V⟦n⟧)) :=
    LinearEquiv.ofBijective (F.mapLinearMap A)
      ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective _ _)
  exact (Linear.homCongr A τ (Iso.refl (V⟦n⟧))).symm.trans (e.trans
    (Linear.homCongr A
      ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} A))
        (-1 : ℤ) 1 (by omega)).app S)
      (((CategoryTheory.shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A))
        n 1 (n + 1) rfl).app V).symm)))

/-- The original derived-Hom comparison transports the actual single-one dual homology. -/
def singleOneHomologyEquiv (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective]
    (M : ModuleCat.{u} A) (n : ℤ) :
    homology J n ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj M) ≃ₗ[A]
      homology J (n + 1) ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) :=
  (derivedDualHomologyLinearEquiv.{u, u, w} J n _).trans
    ((singleOneHomEquiv M (DerivedCategory.Q.obj J) n).trans
      (derivedDualHomologyLinearEquiv.{u, u, w} J (n + 1) _).symm)

/-- The actual unsigned degree-zero Yoneda boundary, retaining its native shift composition. -/
def unsignedBoundary {X Y V : DerivedCategory (ModuleCat.{u} A)}
    (δ : Y ⟶ X⟦(1 : ℤ)⟧) : (X ⟶ V⟦(0 : ℤ)⟧) →ₗ[A] (Y ⟶ V⟦(1 : ℤ)⟧) where
  toFun f := ShiftedHom.comp δ f (show (0 : ℤ) + 1 = 1 from rfl)
  map_add' f g := ShiftedHom.comp_add δ f g _
  map_smul' a f := ShiftedHom.comp_smul a δ f _

private theorem yoneda_first_injective
    (T : Triangle (DerivedCategory (ModuleCat.{u} A))) (hT : T ∈ distTriang _)
    (V : DerivedCategory (ModuleCat.{u} A))
    [Subsingleton (T.obj₃ ⟶ V⟦(0 : ℤ)⟧)] :
    Function.Injective (fun f : T.obj₂ ⟶ V⟦(0 : ℤ)⟧ => T.mor₁ ≫ f) := by
  intro f g hfg
  change T.mor₁ ≫ f = T.mor₁ ≫ g at hfg
  have hz : T.mor₁ ≫ (f - g) = 0 := by rw [comp_sub, hfg, sub_self]
  obtain ⟨q, hq⟩ := T.yoneda_exact₂ hT (f - g) hz
  apply sub_eq_zero.mp
  rw [hq, Subsingleton.elim q 0, comp_zero]

private theorem yoneda_last_surjective
    (T : Triangle (DerivedCategory (ModuleCat.{u} A))) (hT : T ∈ distTriang _)
    (V : DerivedCategory (ModuleCat.{u} A))
    [Subsingleton (T.obj₁ ⟶ V⟦(1 : ℤ)⟧)] :
    Function.Surjective (fun f : T.obj₃ ⟶ V⟦(1 : ℤ)⟧ => T.mor₂ ≫ f) := by
  intro f
  obtain ⟨q, hq⟩ := T.yoneda_exact₂ hT f (Subsingleton.elim _ _)
  exact ⟨q, hq.symm⟩

end Comparisons

section Coefficient

variable {R A : Type u} [CommRing R] [CommRing A]
  (σ : R →+* A) (I : InjectiveResolution (ModuleCat.of R R))
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]


local instance : I.cochainComplex.IsKInjective :=
  CochainComplex.isKInjective_of_injective I.cochainComplex 0
local instance : (resolutionCoefficient σ I).IsKInjective :=
  (ModuleCat.restrictCoextendScalarsAdj σ).isKInjective_map_of_injectiveComplex
    I.cochainComplex 0

variable [Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))]

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] in
/-- Exact native coinduction preserves the supplied resolution augmentation. -/
theorem coefficientAugmentation_quasiIso :
    QuasiIso (coinducedCoefficientAugmentation σ I.cochainComplex I.ι') := by
  let : (ModuleCat.coextendScalars.{u, u, u} σ).PreservesHomology :=
    ModuleCat.coextendScalars_preservesHomology_of_projective σ
  let : QuasiIso
      (((ModuleCat.coextendScalars.{u, u, u} σ).mapHomologicalComplex (.up ℤ)).map I.ι') :=
    HomologicalComplex.quasiIso_map_of_preservesHomology I.ι' (ModuleCat.coextendScalars σ)
  let e := (HomologicalComplex.singleMapHomologicalComplex
    (ModuleCat.coextendScalars.{u, u, u} σ) (.up ℤ) 0).app (ModuleCat.of R R)
  let a := e.inv
  let : IsIso a := e.symm.isIso_hom
  let : QuasiIso a := quasiIso_of_isIso a
  change QuasiIso (a ≫
    (((ModuleCat.coextendScalars.{u, u, u} σ).mapHomologicalComplex (.up ℤ)).map I.ι'))
  exact quasiIso_comp a
    (((ModuleCat.coextendScalars.{u, u, u} σ).mapHomologicalComplex (.up ℤ)).map I.ι')

/-- The original regular-source comparison and coefficient augmentation compute every degree. -/
def regularHomologyIso (n : ℤ) :
    homology (resolutionCoefficient σ I) n (regularSource A) ≅
      (((singleFunctor (ModuleCat.{u} A) 0).obj (coinducedCoefficient σ)).homology n) := by
  let : QuasiIso (coinducedCoefficientAugmentation σ I.cochainComplex I.ι') :=
    coefficientAugmentation_quasiIso σ I
  exact singleHomologyIso (resolutionCoefficient σ I) (ModuleCat.of A A) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n).mapIso
      (regularSingleComplexIso (resolutionCoefficient σ I)) ≪≫
    (isoOfQuasiIsoAt (coinducedCoefficientAugmentation σ I.cochainComplex I.ι') n).symm

/-- Degree-zero normalization uses the original augmentation and evaluation at one. -/
def unitNormalization :
    homology (resolutionCoefficient σ I) 0 (regularSource A) ≅ coinducedCoefficient σ :=
  regularHomologyIso σ I 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (coinducedCoefficient σ)

private theorem regularHom_subsingleton (n : ℤ) (hn : n ≠ 0) :
    Subsingleton ((regularSource A) ⟶ (DerivedCategory.Q.obj (resolutionCoefficient σ I))⟦n⟧) := by
  have hz : IsZero (homology (resolutionCoefficient σ I) n (regularSource A)) :=
    (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
      (coinducedCoefficient σ) n hn).of_iso (regularHomologyIso σ I n)
  have h₀ : Subsingleton (homology (resolutionCoefficient σ I) n (regularSource A)) :=
    ModuleCat.subsingleton_of_isZero hz
  let e := derivedDualHomologyLinearEquiv.{u, u, w}
    (resolutionCoefficient σ I) n (regularSource A)
  exact ⟨fun f g => e.symm.injective (h₀.elim _ _)⟩

variable [IsRegularLocalRing R] (hd : ringKrullDim R = (2 : ℕ))
  (H : ModuleCat.{u} A) (hH : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj H))

include hd hH

omit [Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))] in
private theorem finiteSingleZero_isZero (n : ℤ) (hn : n ≠ 2) :
    IsZero (homology (resolutionCoefficient σ I) n
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj H)) := by
  let e := singleHomologyIso (resolutionCoefficient σ I) H n
  cases n with
  | ofNat n =>
    have hn' : n ≠ 2 := fun h => hn (congrArg (fun k : ℕ => (k : ℤ)) h)
    let : HasDerivedCategory.{u+1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
    let E := coinducedSingleHomologyExtLinearEquiv.{u, u, u, u+1, u}
      σ H (ModuleCat.of R R) I.cochainComplex I.ι' n
    let : Subsingleton (Ext ((ModuleCat.restrictScalars σ).obj H) (ModuleCat.of R R) n) :=
      IsRegularLocalRing.subsingleton_ext_of_isFiniteLength_ne_two R hd
        ((ModuleCat.restrictScalars σ).obj H) hH n hn'
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun x y => e.toLinearEquiv.injective (E.injective (Subsingleton.elim _ _))⟩
  | negSucc n =>
    let : (resolutionCoefficient σ I).IsStrictlyGE 0 := by
      change CochainComplex.IsStrictlyGE
        (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) 0
      infer_instance
    let K := moduleComplex A ((singleFunctor (ModuleCat.{u} A) 0).obj H)
      (resolutionCoefficient σ I)
    let : K.IsStrictlyGE 0 :=
      moduleComplex_single_isStrictlyGE_zero.{u, u} H (resolutionCoefficient σ I)
    exact (K.isZero_of_isGE 0 (Int.negSucc n) (by omega)).of_iso e

omit [Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))] in
/-- The original degree-one layer has dual cohomology only in degree one. -/
theorem finiteSingleOne_isZero (n : ℤ) (hn : n ≠ 1) :
    IsZero (homology (resolutionCoefficient σ I) n (firstLayer H)) :=
  (finiteSingleZero_isZero σ I hd H hH (n + 1) (by omega)).of_iso
    (singleOneHomologyEquiv (resolutionCoefficient σ I) H n).toModuleIso

omit [Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))] in
private theorem finiteSingleOneHom_subsingleton (n : ℤ) (hn : n ≠ 1) :
    Subsingleton (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj H) ⟶
      (DerivedCategory.Q.obj (resolutionCoefficient σ I))⟦n⟧) := by
  have h₀ : Subsingleton (homology (resolutionCoefficient σ I) n (firstLayer H)) :=
    ModuleCat.subsingleton_of_isZero (finiteSingleOne_isZero σ I hd H hH n hn)
  let e := derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) n
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj H)
  exact ⟨fun f g => e.symm.injective (h₀.elim _ _)⟩

omit [Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))] in
/-- Only scalar restriction is used to compare intrinsic A-homology with native R-Ext-two. -/
theorem finiteSingleOne_finiteLength_restrict :
    IsFiniteLength R ((ModuleCat.restrictScalars σ).obj
      (homology (resolutionCoefficient σ I) 1 (firstLayer H))) := by
  let : HasDerivedCategory.{u+1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let eA := (singleOneHomologyEquiv (resolutionCoefficient σ I) H 1).toModuleIso ≪≫
    singleHomologyIso (resolutionCoefficient σ I) H 2
  let eR := ((ModuleCat.restrictScalars σ).mapIso eA).toLinearEquiv.trans
    (coinducedSingleHomologyExtLinearEquiv.{u, u, u, u+1, u}
      σ H (ModuleCat.of R R) I.cochainComplex I.ι' 2)
  exact eR.symm.isFiniteLength
    (IsRegularLocalRing.isFiniteLength_extDualTwo R hd
      ((ModuleCat.restrictScalars σ).obj H) hH)

end Coefficient

section Row

variable {R A : Type u} [CommRing R] [CommRing A]
  (σ : R →+* A) (I : InjectiveResolution (ModuleCat.of R R))
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))]


local instance : (resolutionCoefficient σ I).IsKInjective :=
  (ModuleCat.restrictCoextendScalarsAdj σ).isKInjective_map_of_injectiveComplex
    I.cochainComplex 0

variable (H : ModuleCat.{u} A) (C : DerivedCategory (ModuleCat.{u} A))

/-- The original dual unit on H0, with the fixed evaluation-at-one normalization. -/
def unitMap (η : (regularSource A) ⟶ C) :
    homology (resolutionCoefficient σ I) 0 C →ₗ[A] coinducedCoefficient σ :=
  (unitNormalization σ I).hom.hom.comp
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((derivedDual (resolutionCoefficient σ I)).map η.op)).hom

/-- The original H1 dual map, without a transported replacement action. -/
def projectionMap (κ : C ⟶ (firstLayer H)) :
    homology (resolutionCoefficient σ I) 1 (firstLayer H) →ₗ[A]
      homology (resolutionCoefficient σ I) 1 C :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
    ((derivedDual (resolutionCoefficient σ I)).map κ.op)).hom

/-- The normalized coefficient in the original degree-zero Yoneda coordinates. -/
def coefficientHomEquiv : coinducedCoefficient σ ≃ₗ[A]
    ((regularSource A) ⟶ (DerivedCategory.Q.obj (resolutionCoefficient σ I))⟦(0 : ℤ)⟧) :=
  (unitNormalization σ I).symm.toLinearEquiv.trans
    (derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) 0 (regularSource A))

/-- The actual unsigned Postnikov boundary transported through the fixed native comparisons. -/
def boundaryMap (δ : (firstLayer H) ⟶ (regularSource A)⟦(1 : ℤ)⟧) :
    coinducedCoefficient σ →ₗ[A] homology (resolutionCoefficient σ I) 1 (firstLayer H) :=
  (derivedDualHomologyLinearEquiv.{u, u, w}
      (resolutionCoefficient σ I) 1 (firstLayer H)).symm.toLinearMap.comp
    ((unsignedBoundary δ).comp (coefficientHomEquiv σ I).toLinearMap)

/-- Naturality identifies the coefficient-coordinate map with the original dual unit. -/
theorem unitMap_comparison (η : (regularSource A) ⟶ C)
    (z : homology (resolutionCoefficient σ I) 0 C) :
    coefficientHomEquiv σ I (unitMap σ I C η z) =
      η ≫ derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) 0 C z := by
  let f := ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    ((derivedDual (resolutionCoefficient σ I)).map η.op)).hom
  exact (normalized_linear_comparison (unitNormalization σ I)
    (derivedDualHomologyLinearEquiv.{u, u, w}
      (resolutionCoefficient σ I) 0 (regularSource A)) f z).trans
    (derivedDualHomologyLinearEquiv_naturality.{u, u, w}
      (resolutionCoefficient σ I) 0 η z)

/-- The boundary retains literally the original third arrow and native unsigned composition. -/
theorem boundaryMap_comparison (δ : (firstLayer H) ⟶ (regularSource A)⟦(1 : ℤ)⟧)
    (z : coinducedCoefficient σ) :
    derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) 1 (firstLayer H)
        (boundaryMap σ I H δ z) =
      ShiftedHom.comp δ (coefficientHomEquiv σ I z) (show (0 : ℤ) + 1 = 1 from rfl) :=
  (derivedDualHomologyLinearEquiv.{u, u, w}
    (resolutionCoefficient σ I) 1 (firstLayer H)).apply_symm_apply _

omit [Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))] in
/-- Naturality identifies the final row map with the original H1 projection. -/
theorem projectionMap_comparison (κ : C ⟶ (firstLayer H))
    (z : homology (resolutionCoefficient σ I) 1 (firstLayer H)) :
    derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) 1 C
        (projectionMap σ I H C κ z) =
      κ ≫ derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) 1 (firstLayer H) z :=
  derivedDualHomologyLinearEquiv_naturality.{u, u, w} (resolutionCoefficient σ I) 1 κ z

variable [IsRegularLocalRing R] (hd : ringKrullDim R = (2 : ℕ))
  (hH : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj H))
  (η : (regularSource A) ⟶ C) (κ : C ⟶ (firstLayer H))
  (δ : (firstLayer H) ⟶ (regularSource A)⟦(1 : ℤ)⟧)
  (hT : Triangle.mk η κ δ ∈ distTriang _)

include hd hH hT

/-- Vanishing of the actual two outer Hom groups gives every off-range dual homology vanishing. -/
theorem homology_isZero (n : ℤ) (hn₀ : n ≠ 0) (hn₁ : n ≠ 1) :
    IsZero (homology (resolutionCoefficient σ I) n C) := by
  let T := Triangle.mk η κ δ
  let V := DerivedCategory.Q.obj (resolutionCoefficient σ I)
  have h₁ : Subsingleton (T.obj₁ ⟶ V⟦n⟧) :=
    regularHom_subsingleton σ I n hn₀
  have h₃ : Subsingleton (T.obj₃ ⟶ V⟦n⟧) :=
    finiteSingleOneHom_subsingleton σ I hd H hH n hn₁
  let e := derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) n C
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hz (f : C ⟶ (DerivedCategory.Q.obj (resolutionCoefficient σ I))⟦n⟧) : f = 0 := by
    obtain ⟨q, hq⟩ := T.yoneda_exact₂ hT f (h₁.elim _ _)
    rw [hq, h₃.elim q 0, comp_zero]
  exact ⟨fun x y => e.injective ((hz (e x)).trans (hz (e y)).symm)⟩

/-- The actual coinduced dual is nonnegative, without assuming a triangulated dual. -/
theorem isGE_zero : ((derivedDual (resolutionCoefficient σ I)).obj (op C)).IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro n hn
  exact homology_isZero σ I H C hd hH η κ δ hT n (by omega) (by omega)

/-- The actual coinduced dual has no cohomology above degree one. -/
theorem isLE_one : ((derivedDual (resolutionCoefficient σ I)).obj (op C)).IsLE 1 := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  exact homology_isZero σ I H C hd hH η κ δ hT n (by omega) (by omega)

/-- Exactness and both endpoints of the actual algebraic dual-unit obstruction row. -/
theorem obstruction_exact :
    Function.Injective (unitMap σ I C η) ∧
      Function.Exact (unitMap σ I C η) (boundaryMap σ I H δ) ∧
      Function.Exact (boundaryMap σ I H δ) (projectionMap σ I H C κ) ∧
      Function.Surjective (projectionMap σ I H C κ) := by
  let T := Triangle.mk η κ δ
  let V := DerivedCategory.Q.obj (resolutionCoefficient σ I)
  let eL := derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) 0 C
  let eΩ := coefficientHomEquiv σ I
  let eE := derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) 1 (firstLayer H)
  let eN := derivedDualHomologyLinearEquiv.{u, u, w} (resolutionCoefficient σ I) 1 C
  let f : (C ⟶ V⟦(0 : ℤ)⟧) →ₗ[A] ((regularSource A) ⟶ V⟦(0 : ℤ)⟧) :=
    Linear.leftComp A _ η
  let b : ((regularSource A) ⟶ V⟦(0 : ℤ)⟧) →ₗ[A] ((firstLayer H) ⟶ V⟦(1 : ℤ)⟧) :=
    unsignedBoundary δ
  let g : ((firstLayer H) ⟶ V⟦(1 : ℤ)⟧) →ₗ[A] (C ⟶ V⟦(1 : ℤ)⟧) :=
    Linear.leftComp A _ κ
  have hf : f.comp eL.toLinearMap = eΩ.toLinearMap.comp (unitMap σ I C η) := by
    ext z
    exact (unitMap_comparison σ I C η z).symm
  have hb : b.comp eΩ.toLinearMap = eE.toLinearMap.comp (boundaryMap σ I H δ) := by
    ext z
    exact (boundaryMap_comparison σ I H δ z).symm
  have hg : g.comp eE.toLinearMap = eN.toLinearMap.comp (projectionMap σ I H C κ) := by
    ext z
    exact (projectionMap_comparison σ I H C κ z).symm
  let : Subsingleton (T.obj₃ ⟶ V⟦(0 : ℤ)⟧) :=
    finiteSingleOneHom_subsingleton σ I hd H hH 0 (by decide)
  let : Subsingleton (T.obj₁ ⟶ V⟦(1 : ℤ)⟧) :=
    regularHom_subsingleton σ I 1 (by decide)
  have hinj := yoneda_first_injective T hT V
  have hsurj := yoneda_last_surjective T hT V
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply eL.injective
    apply hinj
    exact (unitMap_comparison σ I C η x).symm.trans
      ((congrArg eΩ hxy).trans (unitMap_comparison σ I C η y))
  · exact (Function.Exact.iff_of_ladder_linearEquiv hf hb).mp
      (yoneda_exact_precomp_boundary T hT V 0 1 rfl)
  · exact (Function.Exact.iff_of_ladder_linearEquiv hb hg).mp
      (yoneda_exact_boundary_precomp T hT V 0 1 rfl)
  · intro z
    obtain ⟨y, hy⟩ := hsurj (eN z)
    refine ⟨eE.symm y, ?_⟩
    apply eN.injective
    rw [projectionMap_comparison, eE.apply_symm_apply]
    exact hy


/-- The actual H1 of the dual has finite length for its original A-action. -/
theorem homologyOne_finiteLength :
    IsFiniteLength A (homology (resolutionCoefficient σ I) 1 C) := by
  have hsurj := (obstruction_exact σ I H C hd hH η κ δ hT).2.2.2
  have hE := finiteSingleOne_finiteLength_restrict σ I hd H hH
  have hN : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj
      (homology (resolutionCoefficient σ I) 1 C)) :=
    hE.of_surjective (f := ((ModuleCat.restrictScalars σ).map
      (ModuleCat.ofHom (projectionMap σ I H C κ))).hom) hsurj
  exact finiteLength_of_restriction σ (homology (resolutionCoefficient σ I) 1 C) hN

end Row

section UnitTriangle

variable {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  (X : DerivedCategory.Plus (ModuleCat.{u} A)) [X.IsGE 0] [X.IsLE 1]
  (η : (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A A) ⟶ X)
  [IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 0).map η)]

/-- The original unit-Postnikov triangle mapped by the native inclusion.
Its single endpoints agree definitionally with the native full-derived singles. -/
def unitPostnikovTriangle : Triangle (DerivedCategory (ModuleCat.{u} A)) :=
  DerivedCategory.Plus.ι.mapTriangle.obj (DerivedCategory.Plus.unitPostnikovTriangle η)

/-- The first arrow is the original supplied unit under the native inclusion. -/
theorem unitPostnikovTriangle_mor₁ :
    (unitPostnikovTriangle X η).mor₁ = DerivedCategory.Plus.ι.map η := rfl

/-- The second arrow is the original normalized H1 projection under inclusion. -/
theorem unitPostnikovTriangle_mor₂ :
    (unitPostnikovTriangle X η).mor₂ =
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.unitPostnikovTriangle η).mor₂ := rfl

/-- The third arrow retains the original boundary and the inclusion's native shift comparison. -/
theorem unitPostnikovTriangle_mor₃ :
    (unitPostnikovTriangle X η).mor₃ =
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.unitPostnikovTriangle η).mor₃ ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A A)) := rfl

/-- Distinguishedness is inherited from the same specified unit triangle. -/
theorem unitPostnikovTriangle_distinguished : unitPostnikovTriangle X η ∈ distTriang _ :=
  DerivedCategory.Plus.ι.map_distinguished _
    (DerivedCategory.Plus.unitPostnikovTriangle_distinguished η)

end UnitTriangle

section UnitPostnikov

variable {R A : Type u} [CommRing R] [CommRing A]
  (σ : R →+* A) (I : InjectiveResolution (ModuleCat.of R R))
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))]
  [IsRegularLocalRing R] (hd : ringKrullDim R = (2 : ℕ))
  (X : DerivedCategory.Plus (ModuleCat.{u} A)) [X.IsGE 0] [X.IsLE 1]
  (η : (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A A) ⟶ X)
  [IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 0).map η)]
  (hH : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)))

include hd η hH


local instance : (resolutionCoefficient σ I).IsKInjective :=
  (ModuleCat.restrictCoextendScalarsAdj σ).isKInjective_map_of_injectiveComplex
    I.cochainComplex 0

/-- The actual unit and original H1 supply the lower dual bound directly. -/
theorem unitPostnikov_isGE_zero :
    ((derivedDual (resolutionCoefficient σ I)).obj
      (op (DerivedCategory.Plus.ι.obj X))).IsGE 0 := by
  let T := unitPostnikovTriangle X η
  exact isGE_zero σ I
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)
    (DerivedCategory.Plus.ι.obj X) hd hH T.mor₁ T.mor₂ T.mor₃
    (unitPostnikovTriangle_distinguished X η)

/-- The actual unit and original H1 supply the upper dual bound directly. -/
theorem unitPostnikov_isLE_one :
    ((derivedDual (resolutionCoefficient σ I)).obj
      (op (DerivedCategory.Plus.ι.obj X))).IsLE 1 := by
  let T := unitPostnikovTriangle X η
  exact isLE_one σ I
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)
    (DerivedCategory.Plus.ι.obj X) hd hH T.mor₁ T.mor₂ T.mor₃
    (unitPostnikovTriangle_distinguished X η)

/-- Finite restricted original H1 gives finite length for the intrinsic top dual homology. -/
theorem unitPostnikov_homologyOne_finiteLength :
    IsFiniteLength A (homology (resolutionCoefficient σ I) 1 (DerivedCategory.Plus.ι.obj X)) := by
  let T := unitPostnikovTriangle X η
  exact homologyOne_finiteLength σ I
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)
    (DerivedCategory.Plus.ι.obj X) hd hH T.mor₁ T.mor₂ T.mor₃
    (unitPostnikovTriangle_distinguished X η)

/-- The canonical unit wrapper retains the actual unsigned obstruction row for later trace use. -/
theorem unitPostnikov_obstruction_exact :
    let H := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X
    let C := DerivedCategory.Plus.ι.obj X
    let T := unitPostnikovTriangle X η
    Function.Injective (unitMap σ I C T.mor₁) ∧
      Function.Exact (unitMap σ I C T.mor₁) (boundaryMap σ I H T.mor₃) ∧
      Function.Exact (boundaryMap σ I H T.mor₃) (projectionMap σ I H C T.mor₂) ∧
      Function.Surjective (projectionMap σ I H C T.mor₂) := by
  let T := unitPostnikovTriangle X η
  exact obstruction_exact σ I
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)
    (DerivedCategory.Plus.ι.obj X) hd hH T.mor₁ T.mor₂ T.mor₃
    (unitPostnikovTriangle_distinguished X η)

end UnitPostnikov

end CochainComplex.HomComplex.TwoLayerDual
