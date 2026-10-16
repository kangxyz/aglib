/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Quotient
public import Aglib.Algebra.Homology.Koszul.Single.Ext.Ideal
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers

/-!
# Regular-principal purity for native derived coinduction

For a scalar regular on the ring, homology in degree one of the installed
D+ coinduction along the actual principal ideal quotient is the original
coefficient quotient, linearly over that quotient ring. Its inverse sends a
literal coefficient representative to the original transported Koszul class.

Coefficient regularity alone gives the lower bound one; ring regularity
alone gives the upper bound one. With both hypotheses, the actual derived
object is the native single of that same coefficient quotient in degree one.
The isomorphism retains the homology-normalized native single comparison.
For the ring coefficient this is the actual quotient ring in degree one,
with its unchanged original quotient representatives. All three comparisons
are independent of the supplied injective resolution.

No Noetherian, flatness or finiteness premise is imposed. The Ext and two
supplied derived-category size universes remain independent. This affine
one-equation calculation does not yet give sheaf purity or the determinant
change of generators for a regular list.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ChainComplex.Koszul
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w v z
namespace ModuleCat
variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (a : R) (ha : IsSMulRegular R a)
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]
  [HasDerivedCategory.{z} (ModuleCat.{u} (R ⧸ Ideal.span {a}))]

/-- The actual degree-one homology is the original coefficient quotient, over the quotient ring. -/
def derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv
    (N : ModuleCat.{u} R) (J : InjectiveResolution N) :
    letI := singleQuotientModule a N
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).obj
      ((coextendScalars (Ideal.Quotient.mk (Ideal.span {a}))).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≃ₗ[R ⧸ Ideal.span {a}]
      SingleQuotient N a := by
  letI := singleQuotientModule a N
  letI := Ext.quotientSourceModule (Ideal.span {a}) N 1
  exact (derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv
    (Ideal.span {a}) N J 1).trans (singleIdealExtOneQuotientLinearEquiv a ha N).symm

/-- A literal representative retains its original transported Koszul Ext class. -/
@[simp]
theorem derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv_symm_mk
    (N : ModuleCat.{u} R) (J : InjectiveResolution N) (x : N) :
    letI := singleQuotientModule a N
    derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv (Ideal.span {a}) N J 1
      ((derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv a ha N J).symm
        (Submodule.Quotient.mk x)) = singleIdealExtOneClass a ha N x := by
  let := singleQuotientModule a N
  let := Ext.quotientSourceModule (Ideal.span {a}) N 1
  simp only [derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv,
    LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    singleIdealExtOneQuotientLinearEquiv_apply_mk]
  exact (derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv
    (Ideal.span {a}) N J 1).apply_symm_apply _

include ha in
/-- Ring and coefficient regularity kill every other natural-degree homology group. -/
theorem isZero_derivedCoextendScalarsPlusPrincipalHomology_of_ne_one
    (N : ModuleCat.{u} R) (J : InjectiveResolution N)
    (hN : IsSMulRegular N a) (n : ℕ) (hn : n ≠ 1) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a}))
      (n : ℤ)).obj
      ((coextendScalars (Ideal.Quotient.mk (Ideal.span {a}))).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N))) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let E := derivedCoextendScalarsPlusHomologyExtAddEquiv (Ideal.Quotient.mk (Ideal.span {a})) N J n
  refine ⟨fun x y => E.injective ?_⟩
  exact (singleIdealExt_eq_zero_of_ne_one a ha N hN n hn (E x)).trans
    (singleIdealExt_eq_zero_of_ne_one a ha N hN n hn (E y)).symm

/-- Coefficient regularity alone gives the actual lower cohomological bound one. -/
theorem derivedCoextendScalarsPlusPrincipal_isGE
    (N : ModuleCat.{u} R) (J : InjectiveResolution N) (hN : IsSMulRegular N a) :
    ((coextendScalars (Ideal.Quotient.mk (Ideal.span {a}))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsGE 1 := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro i hi
  by_cases hi0 : i < 0
  · exact Functor.isZero_homology_rightDerivedFunctorPlus_of_isGE
      (coextendScalars (Ideal.Quotient.mk (Ideal.span {a})))
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N) 0 i hi0
  · have hi' : i = 0 := by omega
    subst i
    apply ModuleCat.isZero_iff_subsingleton.mpr
    let E := derivedCoextendScalarsPlusHomologyExtAddEquiv
      (Ideal.Quotient.mk (Ideal.span {a})) N J 0
    refine ⟨fun x y => E.injective ?_⟩
    exact (singleIdealExtZero_eq_zero_of_regular a N hN (E x)).trans
      (singleIdealExtZero_eq_zero_of_regular a N hN (E y)).symm

include ha in
/-- Ring regularity alone gives the actual upper cohomological bound one. -/
theorem derivedCoextendScalarsPlusPrincipal_isLE
    (N : ModuleCat.{u} R) (J : InjectiveResolution N) :
    ((coextendScalars (Ideal.Quotient.mk (Ideal.span {a}))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLE 1 := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro i hi
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ i by omega)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let E := derivedCoextendScalarsPlusHomologyExtAddEquiv
    (Ideal.Quotient.mk (Ideal.span {a})) N J n
  refine ⟨fun x y => E.injective ?_⟩
  have hn : 1 < n := by omega
  exact (singleIdealExt_eq_zero_above_one a ha N n hn (E x)).trans
    (singleIdealExt_eq_zero_above_one a ha N n hn (E y)).symm

/-- Actual native derived coinduction is the original coefficient quotient in degree one. -/
def derivedCoextendScalarsPlusPrincipalIso
    (N : ModuleCat.{u} R) (J : InjectiveResolution N) (hN : IsSMulRegular N a) :
    letI := singleQuotientModule a N
    (coextendScalars (Ideal.Quotient.mk (Ideal.span {a}))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).obj
        (ModuleCat.of (R ⧸ Ideal.span {a}) (SingleQuotient N a)) := by
  letI := singleQuotientModule a N
  let K := (coextendScalars (Ideal.Quotient.mk (Ideal.span {a}))).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N)
  let := derivedCoextendScalarsPlusPrincipal_isGE a N J hN
  let := derivedCoextendScalarsPlusPrincipal_isLE a ha N J
  exact DerivedCategory.Plus.isoSingleHomology K 1 ≪≫
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).mapIso
      (derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv a ha N J).toModuleIso

/-- The derived isomorphism induces the original quotient-linear homology comparison. -/
@[reassoc]
theorem derivedCoextendScalarsPlusPrincipalIso_homology
    (N : ModuleCat.{u} R) (J : InjectiveResolution N) (hN : IsSMulRegular N a) :
    letI := singleQuotientModule a N
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).map
        (derivedCoextendScalarsPlusPrincipalIso a ha N J hN).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).hom.app
          (ModuleCat.of (R ⧸ Ideal.span {a}) (SingleQuotient N a)) =
      (derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv a ha N J).toModuleIso.hom := by
  let := singleQuotientModule a N
  let K := (coextendScalars (Ideal.Quotient.mk (Ideal.span {a}))).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N)
  let := derivedCoextendScalarsPlusPrincipal_isGE a N J hN
  let := derivedCoextendScalarsPlusPrincipal_isLE a ha N J
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1
  let E := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
    (C := ModuleCat.{u} (R ⧸ Ideal.span {a})) 1
  let e := (derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv a ha N J).toModuleIso
  have hn : H.map (DerivedCategory.Plus.isoSingleHomology K 1).hom ≫ E.hom.app (H.obj K) =
      𝟙 _ := by
    change (DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).map
        ((DerivedCategory.Plus.ι : _ ⥤ DerivedCategory (ModuleCat.{u} (R ⧸ Ideal.span {a}))).map
          (DerivedCategory.Plus.isoSingleHomology K 1).hom) ≫ _ = _
    rw [DerivedCategory.Plus.ι_map_isoSingleHomology_hom]
    exact DerivedCategory.isoSingleHomology_homology _ 1
  change H.map ((DerivedCategory.Plus.isoSingleHomology K 1).hom ≫ S.map e.hom) ≫
    E.hom.app _ = e.hom
  have he : H.map (S.map e.hom) ≫ E.hom.app _ =
      E.hom.app (H.obj K) ≫ e.hom := E.hom.naturality e.hom
  rw [Functor.map_comp, Category.assoc, he, ← Category.assoc, hn, Category.id_comp]

/-- A regular principal equation identifies the actual derived ring image with its quotient
in degree one. -/
def derivedCoextendScalarsPlusPrincipalRingIso
    (J : InjectiveResolution (ModuleCat.of R R)) :
    (coextendScalars (Ideal.Quotient.mk (Ideal.span {a}))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).obj
        (ModuleCat.of (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a})) := by
  letI := singleQuotientModule a R
  exact derivedCoextendScalarsPlusPrincipalIso a ha (ModuleCat.of R R) J ha ≪≫
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).mapIso
      (singleQuotientIdealQuotientLinearEquiv a).toModuleIso

/-- Ring-coefficient purity retains the original homology and original principal quotient map. -/
@[reassoc]
theorem derivedCoextendScalarsPlusPrincipalRingIso_homology
    (J : InjectiveResolution (ModuleCat.of R R)) :
    letI := singleQuotientModule a R
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).map
        (derivedCoextendScalarsPlusPrincipalRingIso a ha J).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).hom.app
          (ModuleCat.of (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a})) =
      ((derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv
        a ha (ModuleCat.of R R) J).trans
          (singleQuotientIdealQuotientLinearEquiv a)).toModuleIso.hom := by
  let := singleQuotientModule a R
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1
  let E := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
    (C := ModuleCat.{u} (R ⧸ Ideal.span {a})) 1
  let e := (singleQuotientIdealQuotientLinearEquiv a).toModuleIso
  have he : H.map (S.map e.hom) ≫ E.hom.app _ =
      E.hom.app (ModuleCat.of (R ⧸ Ideal.span {a}) (SingleQuotient R a)) ≫ e.hom :=
    E.hom.naturality e.hom
  change H.map ((derivedCoextendScalarsPlusPrincipalIso a ha (ModuleCat.of R R) J ha).hom ≫
    S.map e.hom) ≫ E.hom.app _ = _
  rw [Functor.map_comp, Category.assoc, he, ← Category.assoc,
    derivedCoextendScalarsPlusPrincipalIso_homology]
  rfl

/-- The original quotient-linear homology comparison is independent of the supplied resolution. -/
theorem derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv_independent
    (N : ModuleCat.{u} R) (I J : InjectiveResolution N) :
    letI := singleQuotientModule a N
    derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv a ha N I =
      derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv a ha N J := by
  let := singleQuotientModule a N
  let := Ext.quotientSourceModule (Ideal.span {a}) N 1
  change (derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv
      (Ideal.span {a}) N I 1).trans (singleIdealExtOneQuotientLinearEquiv a ha N).symm =
    (derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv
      (Ideal.span {a}) N J 1).trans (singleIdealExtOneQuotientLinearEquiv a ha N).symm
  rw [derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv_independent
    (Ideal.span {a}) N I J 1]

/-- The homology-normalized actual purity isomorphism is independent of the supplied resolution. -/
theorem derivedCoextendScalarsPlusPrincipalIso_independent
    (N : ModuleCat.{u} R) (I J : InjectiveResolution N) (hN : IsSMulRegular N a) :
    letI := singleQuotientModule a N
    derivedCoextendScalarsPlusPrincipalIso a ha N I hN =
      derivedCoextendScalarsPlusPrincipalIso a ha N J hN := by
  let := singleQuotientModule a N
  let := derivedCoextendScalarsPlusPrincipal_isGE a N I hN
  let := derivedCoextendScalarsPlusPrincipal_isLE a ha N I
  apply Iso.ext
  change (DerivedCategory.Plus.isoSingleHomology _ 1).hom ≫
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).map
        (derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv a ha N I).toModuleIso.hom =
    (DerivedCategory.Plus.isoSingleHomology _ 1).hom ≫
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 1).map
        (derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv a ha N J).toModuleIso.hom
  rw [derivedCoextendScalarsPlusPrincipalHomologyLinearEquiv_independent a ha N I J]

/-- Ring-coefficient purity is independent of the supplied injective resolution. -/
theorem derivedCoextendScalarsPlusPrincipalRingIso_independent
    (I J : InjectiveResolution (ModuleCat.of R R)) :
    derivedCoextendScalarsPlusPrincipalRingIso a ha I =
      derivedCoextendScalarsPlusPrincipalRingIso a ha J := by
  unfold derivedCoextendScalarsPlusPrincipalRingIso
  rw [derivedCoextendScalarsPlusPrincipalIso_independent a ha (ModuleCat.of R R) I J ha]

end ModuleCat
