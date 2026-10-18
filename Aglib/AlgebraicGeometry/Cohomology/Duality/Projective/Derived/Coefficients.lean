/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplex.TopHomology
public import Aglib.Algebra.Homology.Flat.ModuleTensor
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.Derived
public import Aglib.AlgebraicGeometry.Cohomology.Cech.TensorCoefficients
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology.Flat
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.Trace

/-!
# The projective residue trace with arbitrary base-module coefficients

For the existing residue twist `omega` on projective n-space, the original bounded-flat
finite Cech complex represents the installed derived global sections. Its native top
projection gives a chain trace whose derived image is exactly the existing residue trace.
Tensoring that actual chain map with an arbitrary base module remains a quasi-isomorphism:
the proof uses its bounded-above flat acyclic mapping cone, without flatness of the module.

The actual finite Cech coefficient isomorphism then gives an isomorphism
`RΓ(omega ⊗ π*tilde(J)) ≅ single_n J = J[-n]` in the full derived category of modules.
The map uses the installed bounded-below right-derived global sections and its original
full inclusion. It is natural in every coefficient morphism and respects the original
structural scalar endomorphisms, without a generic RF-linear instance.

Native homology and original additive-sheaf cohomology inherit R-linear trace equivalences.
At `J = R`, the original tilde, pullback, and tensor unitors identify this actual trace
with the unchanged original projective residue trace. Every commutative base ring and
projective dimension zero are retained; no Noetherianity or condition on `J` is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry TopologicalSpace Opposite HomologicalComplex
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- The standard derived-category model for modules on `ProjectiveSpace R ι`, used locally. -/
local instance projectiveCoefficientTraceSource :
    HasDerivedCategory.{u + 1} (ProjectiveSpace R ι).Modules :=
  HasDerivedCategory.standard _
/-- The standard derived-category model for `R`-modules, used locally. -/
local instance projectiveCoefficientTraceTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- The original good finite Cech truncation of the existing residue twist. -/
abbrev projectiveResidueFiniteCechComplex (n : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  moduleFiniteCechComplex (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (coordinateOpen R ι) (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n

/-- The original finite model represents installed derived global sections through any
resolution. -/
def projectiveResidueFiniteCechDerivedIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (I : InjectiveResolution (twistingSheaf R ι (-(Fintype.card ι : ℤ)))) :
    DerivedCategory.Q.obj (projectiveResidueFiniteCechComplex R ι n) ≅
      projectiveDerivedResidueTwist R ι :=
  moduleFiniteCechDerivedGlobalSectionsIso (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (coordinateOpen R ι) (twistingSheaf R ι (-(Fintype.card ι : ℤ))) I n e
    (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)

/-- The native top functional on the original finite model, normalized by the unchanged trace. -/
def projectiveFiniteResidueTraceHomologyIso (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (projectiveResidueFiniteCechComplex R ι n).homology (n : ℤ) ≅ ModuleCat.of R R := by
  let I := injectiveResolution (twistingSheaf R ι (-(Fintype.card ι : ℤ)))
  let K := projectiveResidueFiniteCechComplex R ι n
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R)
  letI := projectiveDerivedTrace_isIso R ι n e
  exact (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)).symm.app K ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).mapIso
      (projectiveResidueFiniteCechDerivedIso R ι n e I ≪≫
        asIso (projectiveDerivedTrace R ι n e)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)).app S ≪≫
    singleObjHomologySelfIso (.up ℤ) (n : ℤ) (ModuleCat.of R R)

/-- The top functional retains both original homology factorization isomorphisms. -/
@[reassoc]
theorem projectiveFiniteResidueTraceHomologyIso_hom (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (projectiveFiniteResidueTraceHomologyIso R ι n e).hom =
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)).inv.app
      (projectiveResidueFiniteCechComplex R ι n) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
      ((projectiveResidueFiniteCechDerivedIso R ι n e
        (injectiveResolution (twistingSheaf R ι (-(Fintype.card ι : ℤ))))).hom ≫
        projectiveDerivedTrace R ι n e) ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)).hom.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R)) ≫
    (singleObjHomologySelfIso (.up ℤ) (n : ℤ) (ModuleCat.of R R)).hom := rfl

/-- The actual chain trace is the native top projection followed by its original normalized
functional. -/
def projectiveFiniteResidueTrace (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    projectiveResidueFiniteCechComplex R ι n ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R) :=
  CochainComplex.topHomologyProjection (projectiveResidueFiniteCechComplex R ι n) (n : ℤ) ≫
    (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (projectiveFiniteResidueTraceHomologyIso R ι n e).hom

/-- The actual chain trace induces precisely its normalized top functional. -/
@[reassoc]
theorem projectiveFiniteResidueTrace_homology (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    homologyMap (projectiveFiniteResidueTrace R ι n e) (n : ℤ) ≫
      (singleObjHomologySelfIso (.up ℤ) (n : ℤ) (ModuleCat.of R R)).hom =
    (projectiveFiniteResidueTraceHomologyIso R ι n e).hom := by
  dsimp only [projectiveFiniteResidueTrace]
  rw [homologyMap_comp, Category.assoc,
    singleObjHomologySelfIso_hom_naturality, ← Category.assoc,
    CochainComplex.topHomologyProjection_homology, Category.id_comp]

/-- The derived image of the actual chain trace is exactly the original model followed by old
trace. -/
@[reassoc]
theorem projectiveFiniteResidueTrace_derived (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    DerivedCategory.Q.map (projectiveFiniteResidueTrace R ι n e) =
      (projectiveResidueFiniteCechDerivedIso R ι n e
        (injectiveResolution (twistingSheaf R ι (-(Fintype.card ι : ℤ))))).hom ≫
      projectiveDerivedTrace R ι n e := by
  let K := projectiveResidueFiniteCechComplex R ι n
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R)
  let E := projectiveResidueFiniteCechDerivedIso R ι n e
    (injectiveResolution (twistingSheaf R ι (-(Fintype.card ι : ℤ))))
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)
  let : (DerivedCategory.Q.obj K).IsGE (n : ℤ) := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact (projectiveDerivedResidueTwist_isZero_homology R ι n e i (ne_of_lt hi)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso E)
  let : (DerivedCategory.Q.obj K).IsLE (n : ℤ) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact (projectiveDerivedResidueTwist_isZero_homology R ι n e i (ne_of_gt hi)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso E)
  apply DerivedCategory.homology_map_injective_of_isGE_of_isLE
    (DerivedCategory.Q.obj K) ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (ModuleCat.of R R)) (n : ℤ)
  let c := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)).hom.app S ≫
    (singleObjHomologySelfIso (.up ℤ) (n : ℤ) (ModuleCat.of R R)).hom
  apply (cancel_mono c).mp
  have hQ := DerivedCategory.homologyFunctorFactors_hom_naturality
    (projectiveFiniteResidueTrace R ι n e) (n : ℤ)
  change H.map (DerivedCategory.Q.map (projectiveFiniteResidueTrace R ι n e)) ≫ c =
    H.map (E.hom ≫ projectiveDerivedTrace R ι n e) ≫ c
  calc
    _ = (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)).hom.app K ≫
        (homologyMap (projectiveFiniteResidueTrace R ι n e) (n : ℤ) ≫
          (singleObjHomologySelfIso (.up ℤ) (n : ℤ) (ModuleCat.of R R)).hom) := by
      dsimp only [c]
      rw [← Category.assoc, hQ, Category.assoc]
    _ = (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)).hom.app K ≫
        (projectiveFiniteResidueTraceHomologyIso R ι n e).hom := by
      rw [projectiveFiniteResidueTrace_homology]
    _ = _ := by
      rw [projectiveFiniteResidueTraceHomologyIso_hom]
      change (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)).hom.app K ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)).inv.app K ≫
          H.map (E.hom ≫ projectiveDerivedTrace R ι n e) ≫ c =
        H.map (E.hom ≫ projectiveDerivedTrace R ι n e) ≫ c
      exact Iso.hom_inv_id_app_assoc
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (n : ℤ)) K
        (H.map (E.hom ≫ projectiveDerivedTrace R ι n e) ≫ c)

/-- The actual original-model trace is a quasi-isomorphism over every commutative base ring. -/
theorem projectiveFiniteResidueTrace_quasiIso (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    QuasiIso (projectiveFiniteResidueTrace R ι n e) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).mp
  rw [projectiveFiniteResidueTrace_derived]
  let := projectiveDerivedTrace_isIso R ι n e
  infer_instance

/-- Tensoring the actual trace with any module preserves its quasi-isomorphism.
The supplier uses the actual bounded-above flat acyclic mapping cone; no flatness of `J`
is needed. -/
theorem projectiveFiniteResidueTrace_tensorRight_quasiIso (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R) :
    QuasiIso (((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (projectiveFiniteResidueTrace R ι n e)) := by
  let K := projectiveResidueFiniteCechComplex R ι n
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R)
  let (q : ℤ) : Module.Flat R (K.X q) :=
    twistingFiniteCechComplex_flat_X R ι n e (-(Fintype.card ι : ℤ)) q
  let (q : ℤ) : Module.Flat R (S.X q) := by
    by_cases hq : q = (n : ℤ)
    · subst q
      let : Module.Free R (S.X (n : ℤ)) := Module.Free.of_equiv
        (singleObjXSelf (.up ℤ) (n : ℤ) (ModuleCat.of R R)).toLinearEquiv.symm
      infer_instance
    · let := ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (.up ℤ) (n : ℤ) (ModuleCat.of R R) q hq)
      infer_instance
  let := projectiveFiniteResidueTrace_quasiIso R ι n e
  exact CochainComplex.quasiIso_tensorRight_of_flat J
    (projectiveFiniteResidueTrace R ι n e) (n : ℤ) (n : ℤ)

/-- The literal existing residue twist tensored with the actual pullback of `tilde J`. -/
abbrev projectiveResidueTwistTensorCoefficients (J : ModuleCat.{u} R) :
    (ProjectiveSpace R ι).Modules :=
  (moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).obj
      ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J))

/-- Installed bounded-below derived global sections of the literal tensor coefficient, in full
D(R). -/
abbrev projectiveDerivedResidueTwistCoefficients (J : ModuleCat.{u} R) :
    DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Plus.ι.obj
    ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj
          (projectiveResidueTwistTensorCoefficients R ι J)))

/-- The original finite Cech tensor comparison for the existing residue twist and arbitrary `J`. -/
def projectiveResidueFiniteCechTensorIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) :
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).obj
      (projectiveResidueFiniteCechComplex R ι n) ≅
    moduleFiniteCechComplex (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
      (projectiveResidueTwistTensorCoefficients R ι J) n := by
  let K := moduleCechIntComplex (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))
  let (q : ℤ) : Module.Flat R (K.X q) :=
    twistingCechIntComplex_flat_X R ι (-(Fintype.card ι : ℤ)) q
  exact moduleFiniteCechTensorTildeIso (toSpec R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ))) J (coordinateOpen R ι) n e
    (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)

/-- The tensor of the original finite model represents the actual installed derived coefficient.
Its forward map is the original tensor comparison followed by the original finite model map. -/
def projectiveResidueCoefficientsDerivedModelIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) :
    DerivedCategory.Q.obj (((tensorRight J).mapHomologicalComplex (.up ℤ)).obj
      (projectiveResidueFiniteCechComplex R ι n)) ≅
    projectiveDerivedResidueTwistCoefficients R ι J := by
  let M := projectiveResidueTwistTensorCoefficients R ι J
  letI : M.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J))
  exact DerivedCategory.Q.mapIso (projectiveResidueFiniteCechTensorIso R ι n e J) ≪≫
    moduleFiniteCechDerivedGlobalSectionsIso (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
      M (injectiveResolution M) n e (isAffineOpen_coordinateOpen R ι)
      (iSup_coordinateOpen_eq_top R ι)

/-- The actual derived trace to native `single_n J = J[-n]`, obtained by tensoring the old
chain trace. -/
def projectiveDerivedTraceCoefficients (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) :
    projectiveDerivedResidueTwistCoefficients R ι J ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj J :=
  (projectiveResidueCoefficientsDerivedModelIso R ι n e J).inv ≫
    DerivedCategory.Q.map (((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (projectiveFiniteResidueTrace R ι n e)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (tensorRight J) (.up ℤ) (n : ℤ)).hom.app
        (ModuleCat.of R R)) ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map (λ_ J).hom

/-- The actual coefficient trace is an isomorphism for every base module, including nonflat
modules. -/
theorem projectiveDerivedTraceCoefficients_isIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) : IsIso (projectiveDerivedTraceCoefficients R ι n e J) := by
  let := projectiveFiniteResidueTrace_tensorRight_quasiIso R ι n e J
  let : IsIso (DerivedCategory.Q.map (((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (projectiveFiniteResidueTrace R ι n e))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).mpr inferInstance
  dsimp only [projectiveDerivedTraceCoefficients]
  infer_instance

/-- Every original coefficient morphism preserves the actual finite Cech tensor comparison. -/
@[reassoc]
theorem projectiveResidueFiniteCechTensorIso_naturality (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map f) (.up ℤ)).app
      (projectiveResidueFiniteCechComplex R ι n) ≫
        (projectiveResidueFiniteCechTensorIso R ι n e J').hom =
    (projectiveResidueFiniteCechTensorIso R ι n e J).hom ≫
      (moduleFiniteCechFunctor (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) n).map
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
          (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
          ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))) := by
  let K := moduleCechIntComplex (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))
  let (q : ℤ) : Module.Flat R (K.X q) :=
    twistingCechIntComplex_flat_X R ι (-(Fintype.card ι : ℤ)) q
  exact moduleFiniteCechTensorTildeIso_naturality_coefficients (toSpec R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ))) J (coordinateOpen R ι) n e
    (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) f

/-- The model arrow retains the original tensor map and original finite-to-derived forward map. -/
@[reassoc]
theorem projectiveResidueCoefficientsDerivedModelIso_hom (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R) :
    letI : (projectiveResidueTwistTensorCoefficients R ι J).IsQuasicoherent :=
      isQuasicoherent_moduleTensorLeftFunctor (twistingSheaf R ι (-(Fintype.card ι : ℤ)))
        ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J))
    (projectiveResidueCoefficientsDerivedModelIso R ι n e J).hom =
      DerivedCategory.Q.map (projectiveResidueFiniteCechTensorIso R ι n e J).hom ≫
      (moduleFiniteCechDerivedGlobalSectionsIso (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
        (projectiveResidueTwistTensorCoefficients R ι J)
        (injectiveResolution (projectiveResidueTwistTensorCoefficients R ι J)) n e
        (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)).hom := rfl

/-- The actual model is natural for the literal tensor, pullback, and tilde coefficient morphism. -/
@[reassoc]
theorem projectiveResidueCoefficientsDerivedModelIso_naturality (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map f) (.up ℤ)).app
        (projectiveResidueFiniteCechComplex R ι n)) ≫
      (projectiveResidueCoefficientsDerivedModelIso R ι n e J').hom =
    (projectiveResidueCoefficientsDerivedModelIso R ι n e J).hom ≫
      DerivedCategory.Plus.ι.map
        ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
          (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map
            ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
              (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
              ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))))) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M := projectiveResidueTwistTensorCoefficients R ι J
  let N := projectiveResidueTwistTensorCoefficients R ι J'
  let g : M ⟶ N := (moduleTensorLeftFunctor X
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
      ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))
  let : M.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J))
  let : N.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J'))
  let I := injectiveResolution M
  let I' := injectiveResolution N
  let φ : InjectiveResolution.Hom I I' g :=
    ⟨InjectiveResolution.desc g I' I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero g I' I⟩
  have hμ := congrArg (fun q => DerivedCategory.Q.map q)
    (projectiveResidueFiniteCechTensorIso_naturality R ι n e f)
  have hD := moduleFiniteCechDerivedGlobalSectionsIso_naturality X α
    (coordinateOpen R ι) M I n e (isAffineOpen_coordinateOpen R ι)
    (iSup_coordinateOpen_eq_top R ι) φ
  simp only [CategoryTheory.Functor.map_comp] at hμ
  rw [projectiveResidueCoefficientsDerivedModelIso_hom,
    projectiveResidueCoefficientsDerivedModelIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hμ, hD]

/-- The actual trace is natural for every native base-module morphism. -/
@[reassoc]
theorem projectiveDerivedTraceCoefficients_naturality (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    DerivedCategory.Plus.ι.map
      ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp
          (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
            (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
            ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))))) ≫
      projectiveDerivedTraceCoefficients R ι n e J' =
    projectiveDerivedTraceCoefficients R ι n e J ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map f := by
  let K := projectiveResidueFiniteCechComplex R ι n
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R)
  let τ : tensorRight J ⟶ tensorRight J' := (tensoringRight (ModuleCat.{u} R)).map f
  let a := (HomologicalComplex.singleMapHomologicalComplex (tensorRight J) (.up ℤ)
    (n : ℤ)).hom.app (ModuleCat.of R R)
  let a' := (HomologicalComplex.singleMapHomologicalComplex (tensorRight J') (.up ℤ)
    (n : ℤ)).hom.app (ModuleCat.of R R)
  have ht := (NatTrans.mapHomologicalComplex τ (.up ℤ)).naturality
    (projectiveFiniteResidueTrace R ι n e)
  have htQ := congrArg (fun g => DerivedCategory.Q.map g) ht
  simp only [CategoryTheory.Functor.map_comp] at htQ
  have hs₀ := HomologicalComplex.natTransMapHomologicalComplex_app_single_obj
    τ (.up ℤ) (n : ℤ) (ModuleCat.of R R)
  have hs : (NatTrans.mapHomologicalComplex τ (.up ℤ)).app S ≫ a' =
      a ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (τ.app (ModuleCat.of R R)) := by
    have h := congrArg (fun q => q ≫ a') hs₀
    have hi : (HomologicalComplex.singleMapHomologicalComplex (tensorRight J')
        (.up ℤ) (n : ℤ)).inv.app (ModuleCat.of R R) ≫ a' = 𝟙 _ :=
      (HomologicalComplex.singleMapHomologicalComplex (tensorRight J')
        (.up ℤ) (n : ℤ)).inv_hom_id_app (ModuleCat.of R R)
    change (NatTrans.mapHomologicalComplex τ (.up ℤ)).app S ≫ a' =
      a ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (τ.app (ModuleCat.of R R)) ≫
      ((HomologicalComplex.singleMapHomologicalComplex (tensorRight J')
        (.up ℤ) (n : ℤ)).inv.app (ModuleCat.of R R) ≫ a') at h
    rw [hi] at h
    exact h.trans (congrArg (fun q => a ≫ q)
      (Category.comp_id ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ)
        (n : ℤ)).map (τ.app (ModuleCat.of R R)))))
  have hsQ := congrArg (fun g => DerivedCategory.Q.map g) hs
  simp only [CategoryTheory.Functor.map_comp] at hsQ
  change DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app S) ≫
      DerivedCategory.Q.map a' =
    DerivedCategory.Q.map a ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (τ.app (ModuleCat.of R R)) at hsQ
  have hUnit : τ.app (ModuleCat.of R R) ≫ (λ_ J').hom = (λ_ J).hom ≫ f :=
    (leftUnitorNatIso (ModuleCat.{u} R)).hom.naturality f
  have hUnitD := congrArg (fun q =>
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map q) hUnit
  simp only [CategoryTheory.Functor.map_comp] at hUnitD
  apply (cancel_epi (projectiveResidueCoefficientsDerivedModelIso R ι n e J).hom).mp
  dsimp only [projectiveDerivedTraceCoefficients]
  simp only [Category.assoc]
  rw [← reassoc_of% (projectiveResidueCoefficientsDerivedModelIso_naturality R ι n e f)]
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% htQ, reassoc_of% hsQ, hUnitD]

/-- The actual derived coefficient has its lower bound at the projective dimension. -/
theorem projectiveDerivedResidueTwistCoefficients_isGE (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) : (projectiveDerivedResidueTwistCoefficients R ι J).IsGE (n : ℤ) := by
  let := projectiveDerivedTraceCoefficients_isIso R ι n e J
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (asIso (projectiveDerivedTraceCoefficients R ι n e J)).symm (n : ℤ)

/-- The actual derived coefficient has its upper bound at the projective dimension. -/
theorem projectiveDerivedResidueTwistCoefficients_isLE (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) : (projectiveDerivedResidueTwistCoefficients R ι J).IsLE (n : ℤ) := by
  let := projectiveDerivedTraceCoefficients_isIso R ι n e J
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (asIso (projectiveDerivedTraceCoefficients R ι n e J)).symm (n : ℤ)

/-- The actual trace identifies native top homology with the unchanged base module. -/
def projectiveDerivedTraceCoefficientsHomologyIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (projectiveDerivedResidueTwistCoefficients R ι J) ≅ J := by
  letI := projectiveDerivedTraceCoefficients_isIso R ι n e J
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).mapIso
    (asIso (projectiveDerivedTraceCoefficients R ι n e J)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) (n : ℤ)).app J

/-- The native top-homology trace is R-linear, with the original module scalar action. -/
def projectiveDerivedTraceCoefficientsHomologyLinearEquiv (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (projectiveDerivedResidueTwistCoefficients R ι J)) ≃ₗ[R] J :=
  (projectiveDerivedTraceCoefficientsHomologyIso R ι n e J).toLinearEquiv

/-- The linear equivalence has exactly the original native homology-isomorphism forward map. -/
theorem projectiveDerivedTraceCoefficientsHomologyLinearEquiv_apply (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (projectiveDerivedResidueTwistCoefficients R ι J)) :
    projectiveDerivedTraceCoefficientsHomologyLinearEquiv R ι n e J x =
      (projectiveDerivedTraceCoefficientsHomologyIso R ι n e J).hom x := rfl

/-- Native top homology of the actual trace is its specified coefficient trace functional. -/
@[reassoc]
theorem projectiveDerivedTraceCoefficients_homology (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (projectiveDerivedTraceCoefficients R ι n e J) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) (n : ℤ)).hom.app J =
    (projectiveDerivedTraceCoefficientsHomologyIso R ι n e J).hom := rfl

/-- The original additive-sheaf cohomology of the literal coefficient identifies R-linearly
with `J`. -/
def projectiveTraceCoefficientsLinearEquiv (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (projectiveResidueTwistTensorCoefficients R ι J) n
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (projectiveResidueTwistTensorCoefficients R ι J)) n ≃ₗ[R] J := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M := projectiveResidueTwistTensorCoefficients R ι J
  letI := moduleCohomologyModuleOfHom X α M n
  exact (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
    (injectiveResolution M) n).symm.trans
    (projectiveDerivedTraceCoefficientsHomologyLinearEquiv R ι n e J)

/-- The sheaf-cohomology functional is the native trace after the original resolution comparison. -/
theorem projectiveTraceCoefficientsLinearEquiv_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (projectiveResidueTwistTensorCoefficients R ι J)) n) :
    projectiveTraceCoefficientsLinearEquiv R ι n e J x =
    projectiveDerivedTraceCoefficientsHomologyLinearEquiv R ι n e J
      ((moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (injectiveResolution (projectiveResidueTwistTensorCoefficients R ι J)) n).symm x) := rfl

/-- Every supplied injective resolution gives the same original native top functional. -/
theorem projectiveTraceCoefficientsLinearEquiv_derived_apply (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (I : InjectiveResolution (projectiveResidueTwistTensorCoefficients R ι J))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (projectiveDerivedResidueTwistCoefficients R ι J)) :
    projectiveTraceCoefficientsLinearEquiv R ι n e J
      (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) I n x) =
    (projectiveDerivedTraceCoefficientsHomologyIso R ι n e J).hom x := by
  rw [projectiveTraceCoefficientsLinearEquiv_apply,
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_eq _ _ I
      (injectiveResolution (projectiveResidueTwistTensorCoefficients R ι J)) n,
    LinearEquiv.symm_apply_apply]
  exact projectiveDerivedTraceCoefficientsHomologyLinearEquiv_apply R ι n e J x

/-- The actual trace agrees pointwise with original sheaf cohomology through every supplied
resolution. -/
theorem projectiveDerivedTraceCoefficients_homology_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R)
    (I : InjectiveResolution (projectiveResidueTwistTensorCoefficients R ι J))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (projectiveDerivedResidueTwistCoefficients R ι J)) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) (n : ℤ)).hom.app J
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (projectiveDerivedTraceCoefficients R ι n e J) x) =
    projectiveTraceCoefficientsLinearEquiv R ι n e J
      (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) I n x) := by
  have h := congrArg (fun q => q x) (projectiveDerivedTraceCoefficients_homology R ι n e J)
  simp only [ModuleCat.comp_apply] at h
  exact h.trans (projectiveTraceCoefficientsLinearEquiv_derived_apply R ι n e J I x).symm

/-- The actual trace respects the original structural scalar coefficient endomorphism.
The proof detects that original scalar on homology; it requires no generic RF-linear instance. -/
theorem projectiveDerivedTraceCoefficients_smul (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) (r : R) :
    let X := ProjectiveSpace R ι
    let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let M := projectiveResidueTwistTensorCoefficients R ι J
    letI := moduleCategoryLinearOfHom X α
    DerivedCategory.Plus.ι.map
      ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map (r • 𝟙 M))) ≫
      projectiveDerivedTraceCoefficients R ι n e J =
    r • projectiveDerivedTraceCoefficients R ι n e J := by
  dsimp only
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M := projectiveResidueTwistTensorCoefficients R ι J
  let := moduleCategoryLinearOfHom X α
  let I := injectiveResolution M
  let := moduleCohomologyModuleOfHom X α M n
  let f : M ⟶ M := r • 𝟙 M
  let φ : InjectiveResolution.Hom I I f :=
    ⟨InjectiveResolution.desc f I I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero f I I⟩
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)
  let d := DerivedCategory.Plus.ι.map
    ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f))
  let ℓ := (projectiveDerivedTraceCoefficientsHomologyIso R ι n e J).hom
  have hf : (SheafOfModules.toSheaf X.ringCatSheaf).map f =
      moduleScalarOfGlobal X M (α r) := by
    dsimp only [f]
    rw [moduleCategoryLinearOfHom_smul_id]
    ext U x
    exact globalScalarEndomorphism_app X M (α r) U.unop x
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n
  have hdH : H.map d = r • 𝟙 (H.obj (projectiveDerivedResidueTwistCoefficients R ι J)) := by
    ext x
    apply E.injective
    have hn := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_naturality X α φ n x
    change E
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f)) x) = E (r • x)
    rw [hn]
    change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map f) n (E x) = E (r • x)
    rw [hf, E.map_smul]
    rfl
  have hℓ : H.map d ≫ ℓ = ℓ ≫ (r • 𝟙 J) := by
    ext x
    change ℓ (H.map d x) = r • ℓ x
    rw [hdH]
    exact ℓ.hom.map_smul r x
  let := projectiveDerivedResidueTwistCoefficients_isGE R ι n e J
  let := projectiveDerivedResidueTwistCoefficients_isLE R ι n e J
  have hd : d ≫ projectiveDerivedTraceCoefficients R ι n e J =
      projectiveDerivedTraceCoefficients R ι n e J ≫ S.map (r • 𝟙 J) := by
    apply DerivedCategory.homology_map_injective_of_isGE_of_isLE _ _ (n : ℤ)
    apply (cancel_mono ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} R) (n : ℤ)).hom.app J)).mp
    have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} R) (n : ℤ)).hom.naturality (r • 𝟙 J)
    change H.map (S.map _) ≫ _ = _ ≫ _ at hn
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [projectiveDerivedTraceCoefficients_homology, hn, ← Category.assoc,
      projectiveDerivedTraceCoefficients_homology]
    exact hℓ
  change d ≫ projectiveDerivedTraceCoefficients R ι n e J =
    r • projectiveDerivedTraceCoefficients R ι n e J
  rw [hd, CategoryTheory.Functor.map_smul, S.map_id, Linear.comp_smul, Category.comp_id]

/-- At the ring coefficient, use the original tilde, pullback, and tensor right unitors. -/
def projectiveResidueTwistTensorSelfIso :
    projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R) ≅
      twistingSheaf R ι (-(Fintype.card ι : ℤ)) :=
  moduleTensorPullbackTildeSelfIso (toSpec R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))

/-- The actual tensor comparison preserves the literal original finite Cech inclusion. -/
@[reassoc]
theorem projectiveResidueFiniteCechTensorIso_hom_ιTruncLE (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R) :
    (projectiveResidueFiniteCechTensorIso R ι n e J).hom ≫
      moduleFiniteCechInclusion (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
        (projectiveResidueTwistTensorCoefficients R ι J) n =
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (moduleFiniteCechInclusion (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
        (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n) ≫
    moduleCechIntTensorTildeMap (toSpec R ι)
      (twistingSheaf R ι (-(Fintype.card ι : ℤ))) J (coordinateOpen R ι) := by
  let K := moduleCechIntComplex (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))
  let (q : ℤ) : Module.Flat R (K.X q) :=
    twistingCechIntComplex_flat_X R ι (-(Fintype.card ι : ℤ)) q
  exact moduleFiniteCechTensorTildeIso_hom_ιTruncLE (toSpec R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ))) J (coordinateOpen R ι) n e
    (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)

/-- At `J = R`, the original integer Cech coefficient map is the native right unitor. -/
@[reassoc]
theorem projectiveCechIntTensorCoefficients_self :
    moduleCechIntTensorTildeMap (toSpec R ι)
      (twistingSheaf R ι (-(Fintype.card ι : ℤ))) (ModuleCat.of R R) (coordinateOpen R ι) ≫
      (moduleCechIntFunctor (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι)).map
        (projectiveResidueTwistTensorSelfIso R ι).hom =
    (NatTrans.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)).hom (.up ℤ)).app
      (moduleCechIntComplex (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) (twistingSheaf R ι (-(Fintype.card ι : ℤ)))) := by
  let C := moduleCechComplex (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ))) (coordinateOpen R ι)
  let τ : tensorRight (ModuleCat.of R R) ⟶ 𝟭 (ModuleCat.{u} R) :=
    (rightUnitorNatIso (ModuleCat.{u} R)).hom
  let E := ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)
  have hid :
      (C.mapExtendIso (𝟭 (ModuleCat.{u} R)) ComplexShape.embeddingUpNat).hom = 𝟙 _ := by
    ext j : 1
    change (HomologicalComplex.extend.mapXIso C (𝟭 (ModuleCat.{u} R))
      (ComplexShape.embeddingUpNat.r j)).hom = 𝟙 _
    generalize ComplexShape.embeddingUpNat.r j = a
    cases a with
    | none => exact (isZero_zero (ModuleCat.{u} R)).eq_of_tgt _ _
    | some i => rfl
  have hτ := C.mapExtendIso_hom_natTrans (tensorRight (ModuleCat.of R R))
    (𝟭 (ModuleCat.{u} R)) τ ComplexShape.embeddingUpNat
  rw [hid, Category.comp_id] at hτ
  have hC := moduleCechTensorTildeMap_self (toSpec R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ))) (coordinateOpen R ι)
  have hE := congrArg (fun q =>
    (C.mapExtendIso (tensorRight (ModuleCat.of R R)) ComplexShape.embeddingUpNat).hom ≫
      E.map q) hC
  dsimp only [moduleCechIntTensorTildeMap]
  change (C.mapExtendIso (tensorRight (ModuleCat.of R R)) ComplexShape.embeddingUpNat).hom ≫
    HomologicalComplex.extendMap
      (moduleCechTensorTildeMap (toSpec R ι)
        (twistingSheaf R ι (-(Fintype.card ι : ℤ))) (ModuleCat.of R R) (coordinateOpen R ι))
      ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((cechComplexFunctor (coordinateOpen R ι)).map
        ((moduleSectionsPresheafFunctor (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).map
          (projectiveResidueTwistTensorSelfIso R ι).hom)) ComplexShape.embeddingUpNat =
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app (C.extend ComplexShape.embeddingUpNat)
  have hE' := hE.trans hτ.symm
  simpa only [E, projectiveResidueTwistTensorSelfIso,
    CategoryTheory.Functor.map_comp, Category.assoc,
    ComplexShape.Embedding.extendFunctor_obj, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_comp] using hE'

/-- At `J = R`, the original finite tensor comparison is the native right unitor. -/
@[reassoc]
theorem projectiveResidueFiniteCechTensorIso_self (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (projectiveResidueFiniteCechTensorIso R ι n e (ModuleCat.of R R)).hom ≫
      (moduleFiniteCechFunctor (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) n).map
        (projectiveResidueTwistTensorSelfIso R ι).hom =
    (NatTrans.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)).hom (.up ℤ)).app
      (projectiveResidueFiniteCechComplex R ι n) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let K := moduleCechIntComplex X α (coordinateOpen R ι) ω
  let (q : ℤ) : Module.Flat R (K.X q) :=
    twistingCechIntComplex_flat_X R ι (-(Fintype.card ι : ℤ)) q
  let u := (projectiveResidueTwistTensorSelfIso R ι).hom
  let i := moduleFiniteCechInclusion X α (coordinateOpen R ι) ω n
  let : Mono i := by
    change Mono (HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE (n : ℤ)))
    infer_instance
  apply (cancel_mono i).mp
  simp only [Category.assoc]
  rw [moduleFiniteCechInclusion_naturality, ← Category.assoc]
  rw [projectiveResidueFiniteCechTensorIso_hom_ιTruncLE, Category.assoc,
    projectiveCechIntTensorCoefficients_self]
  exact (NatTrans.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)).hom
    (.up ℤ)).naturality i

/-- The tensor of the actual chain trace at `J = R` respects the original native unitors. -/
@[reassoc]
theorem projectiveFiniteResidueTrace_tensorRight_self (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    ((tensorRight (ModuleCat.of R R)).mapHomologicalComplex (.up ℤ)).map
      (projectiveFiniteResidueTrace R ι n e) ≫
      (HomologicalComplex.singleMapHomologicalComplex (tensorRight (ModuleCat.of R R))
        (.up ℤ) (n : ℤ)).hom.app (ModuleCat.of R R) ≫
      (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (λ_ (ModuleCat.of R R)).hom =
    (NatTrans.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)).hom (.up ℤ)).app
      (projectiveResidueFiniteCechComplex R ι n) ≫ projectiveFiniteResidueTrace R ι n e := by
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R)
  let τ : tensorRight (ModuleCat.of R R) ⟶ 𝟭 (ModuleCat.{u} R) :=
    (rightUnitorNatIso (ModuleCat.{u} R)).hom
  let a := (HomologicalComplex.singleMapHomologicalComplex (tensorRight (ModuleCat.of R R))
    (.up ℤ) (n : ℤ)).hom.app (ModuleCat.of R R)
  have hi : (HomologicalComplex.singleMapHomologicalComplex (𝟭 (ModuleCat.{u} R))
      (.up ℤ) (n : ℤ)).inv.app (ModuleCat.of R R) = 𝟙 S := by
    rw [HomologicalComplex.singleMapHomologicalComplex_id_inv_app]
    ext i : 1
    rfl
  have hs := HomologicalComplex.natTransMapHomologicalComplex_app_single_obj
    τ (.up ℤ) (n : ℤ) (ModuleCat.of R R)
  rw [hi] at hs
  change (NatTrans.mapHomologicalComplex τ (.up ℤ)).app S =
    a ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (ρ_ (ModuleCat.of R R)).hom ≫ 𝟙 S at hs
  have hUnit : (λ_ (ModuleCat.of R R)).hom = (ρ_ (ModuleCat.of R R)).hom := unitors_equal
  have hS : a ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (λ_ (ModuleCat.of R R)).hom =
      (NatTrans.mapHomologicalComplex τ (.up ℤ)).app S := by
    rw [hUnit]
    exact (hs.trans (congrArg (fun q => a ≫ q)
      (Category.comp_id ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ)
        (n : ℤ)).map (ρ_ (ModuleCat.of R R)).hom)))).symm
  change _ ≫ (a ≫ _) = _
  rw [hS]
  exact (NatTrans.mapHomologicalComplex τ (.up ℤ)).naturality
    (projectiveFiniteResidueTrace R ι n e)

/-- At `J = R`, the actual trace equals the original coefficient unitor followed by unchanged
old trace. -/
@[reassoc]
theorem projectiveDerivedTraceCoefficients_self (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    projectiveDerivedTraceCoefficients R ι n e (ModuleCat.of R R) =
    DerivedCategory.Plus.ι.map
      ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp
          (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map
            (projectiveResidueTwistTensorSelfIso R ι).hom)) ≫
      projectiveDerivedTrace R ι n e := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let M := projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R)
  let : M.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor ω
    ((Scheme.Modules.pullback (toSpec R ι)).obj
      (tilde (R := CommRingCat.of R) (ModuleCat.of R R)))
  let I := injectiveResolution M
  let I' := injectiveResolution ω
  let u := (projectiveResidueTwistTensorSelfIso R ι).hom
  let φ : InjectiveResolution.Hom I I' u :=
    ⟨InjectiveResolution.desc u I' I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero u I' I⟩
  have hD := moduleFiniteCechDerivedGlobalSectionsIso_naturality X α
    (coordinateOpen R ι) M I n e (isAffineOpen_coordinateOpen R ι)
    (iSup_coordinateOpen_eq_top R ι) φ
  have hμ := congrArg (fun q => DerivedCategory.Q.map q)
    (projectiveResidueFiniteCechTensorIso_self R ι n e)
  have hf := congrArg (fun q => DerivedCategory.Q.map q)
    (projectiveFiniteResidueTrace_tensorRight_self R ι n e)
  simp only [CategoryTheory.Functor.map_comp] at hμ hf
  apply (cancel_epi
    (projectiveResidueCoefficientsDerivedModelIso R ι n e (ModuleCat.of R R)).hom).mp
  dsimp only [projectiveDerivedTraceCoefficients]
  simp only [Iso.hom_inv_id_assoc]
  rw [projectiveResidueCoefficientsDerivedModelIso_hom]
  simp only [Category.assoc]
  rw [← reassoc_of% hD, reassoc_of% hμ]
  have htrace := projectiveFiniteResidueTrace_derived R ι n e
  change DerivedCategory.Q.map (projectiveFiniteResidueTrace R ι n e) =
    (moduleFiniteCechDerivedGlobalSectionsIso X α (coordinateOpen R ι) ω I' n e
      (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)).hom ≫
      projectiveDerivedTrace R ι n e at htrace
  rw [← htrace]
  change DerivedCategory.Q.map
      (((tensorRight (ModuleCat.of R R)).mapHomologicalComplex (.up ℤ)).map
        (projectiveFiniteResidueTrace R ι n e)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (tensorRight (ModuleCat.of R R))
          (.up ℤ) (n : ℤ)).hom.app (ModuleCat.of R R)) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (λ_ (ModuleCat.of R R)).hom = _ at hf
  exact hf

/-- At the ring coefficient, native top homology retains the unchanged original residue
functional. -/
@[reassoc]
theorem projectiveDerivedTraceCoefficientsHomologyIso_self (n : ℕ)
    (e : ι ≃ Fin (n + 1)) :
    (projectiveDerivedTraceCoefficientsHomologyIso R ι n e (ModuleCat.of R R)).hom =
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (DerivedCategory.Plus.ι.map
        ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
          (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map
              (projectiveResidueTwistTensorSelfIso R ι).hom))) ≫
      ModuleCat.ofHom (projectiveDerivedTraceHomologyLinearEquiv R ι n e).toLinearMap := by
  rw [← projectiveDerivedTraceCoefficients_homology,
    projectiveDerivedTraceCoefficients_self, CategoryTheory.Functor.map_comp,
    Category.assoc, projectiveDerivedTrace_homology]

/-- Every native coefficient map preserves the specified top-homology trace functional. -/
@[reassoc]
theorem projectiveDerivedTraceCoefficientsHomologyIso_naturality (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (DerivedCategory.Plus.ι.map
        ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp
          (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map
              ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
                (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
                  ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f)))))) ≫
      (projectiveDerivedTraceCoefficientsHomologyIso R ι n e J').hom =
    (projectiveDerivedTraceCoefficientsHomologyIso R ι n e J).hom ≫ f := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)
  have ht := congrArg H.map (projectiveDerivedTraceCoefficients_naturality R ι n e f)
  simp only [CategoryTheory.Functor.map_comp] at ht
  have hs := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{u} R) (n : ℤ)).hom.naturality f
  change H.map ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).map f) ≫ _ =
    _ ≫ f at hs
  change _ ≫ (H.map (projectiveDerivedTraceCoefficients R ι n e J') ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} R) (n : ℤ)).hom.app J') =
    (H.map (projectiveDerivedTraceCoefficients R ι n e J) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} R) (n : ℤ)).hom.app J) ≫ f
  rw [← Category.assoc, ht, Category.assoc, hs, ← Category.assoc]

end AlgebraicGeometry.Scheme.Cohomology
