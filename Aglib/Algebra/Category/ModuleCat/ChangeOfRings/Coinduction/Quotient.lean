/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Ext
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Quotient

/-!
# Quotient-linear homology of native derived coinduction

For any ideal and any coefficient module, the original additive comparison
between homology of the installed D+ scalar coinduction and native Ext is
linear over the quotient ring. Its underlying map is unchanged: scalar
multiplication is original Yoneda precomposition with quotient multiplication.
The Ext action is the existing explicit quotient-source module structure.
Coefficient naturality retains original Yoneda postcomposition, and the
comparison is independent of the supplied injective resolution.

No regularity, flatness, finiteness or Noetherian hypothesis is used.
The Ext and both supplied derived-category size universes are independent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w a b
namespace ModuleCat
variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (I : Ideal R) [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} (R ⧸ I))]

/-- Actual derived coinduction from a quotient computes the unchanged native quotient-linear Ext. -/
def derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv
    (N : ModuleCat.{u} R) (J : InjectiveResolution N) (n : ℕ) :
    letI := Ext.quotientSourceModule I N n
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ I)) (n : ℤ)).obj
      ((coextendScalars (Ideal.Quotient.mk I)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≃ₗ[R ⧸ I]
      Ext.{w} (ModuleCat.of R (R ⧸ I)) N n := by
  letI := Ext.quotientSourceModule I N n
  refine {
    __ := derivedCoextendScalarsPlusHomologyExtAddEquiv (Ideal.Quotient.mk I) N J n
    map_smul' := ?_ }
  intro b x
  change derivedCoextendScalarsPlusHomologyExtAddEquiv (Ideal.Quotient.mk I) N J n (b • x) =
    b • (show Ext.{w} (ModuleCat.of R (R ⧸ I)) N n from
      derivedCoextendScalarsPlusHomologyExtAddEquiv (Ideal.Quotient.mk I) N J n x)
  rw [derivedCoextendScalarsPlusHomologyExtAddEquiv_smul,
    Ext.quotientSourceModule_smul_eq_precomp]
  have hmul : (restrictScalars (Ideal.Quotient.mk I)).map
      (ModuleCat.ofHom (LinearMap.mulRight (R ⧸ I) b)) = Ext.quotientSourceMul I b := by
    ext y
    rfl
  rw [hmul]

/-- Quotient-linearity retains the original additive homology-to-Ext comparison. -/
@[simp]
theorem derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv_toAddEquiv
    (N : ModuleCat.{u} R) (J : InjectiveResolution N) (n : ℕ) :
    letI := Ext.quotientSourceModule I N n
    (derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv I N J n).toAddEquiv =
      derivedCoextendScalarsPlusHomologyExtAddEquiv (Ideal.Quotient.mk I) N J n := rfl

/-- The unchanged quotient-linear comparison retains original Yoneda coefficient postcomposition. -/
theorem derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv_naturality
    {M N : ModuleCat.{u} R} (J : InjectiveResolution M) (K : InjectiveResolution N)
    (g : M ⟶ N) (n : ℕ)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ I)) (n : ℤ)).obj
      ((coextendScalars (Ideal.Quotient.mk I)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M))) :
    derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv I N K n
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ I)) (n : ℤ)).map
          ((coextendScalars (Ideal.Quotient.mk I)).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map g)) x) =
      (derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv I M J n x).comp
        (Ext.mk₀ g) (add_zero n) :=
  derivedCoextendScalarsPlusHomologyExtAddEquiv_naturality (Ideal.Quotient.mk I) J K g n x

/-- The quotient-linear comparison is independent of the supplied injective resolution. -/
theorem derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv_independent
    (M : ModuleCat.{u} R) (J K : InjectiveResolution M) (n : ℕ) :
    letI := Ext.quotientSourceModule I M n
    derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv I M J n =
      derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv I M K n := by
  let := Ext.quotientSourceModule I M n
  apply LinearEquiv.ext
  intro x
  exact DFunLike.congr_fun (derivedCoextendScalarsPlusHomologyExtAddEquiv_independent
    (Ideal.Quotient.mk I) M J K n) x


private theorem derivedCoextendScalarsPlusQuotientHomology_map_smul_id_apply
    (N : ModuleCat.{u} R) (J : InjectiveResolution N) (n : ℕ) (r : R)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ I)) (n : ℤ)).obj
      ((coextendScalars (Ideal.Quotient.mk I)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N))) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ I)) (n : ℤ)).map
      ((coextendScalars (Ideal.Quotient.mk I)).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map (r • 𝟙 N))) x =
      Ideal.Quotient.mk I r • x := by
  let := Ext.quotientSourceModule.{u,w} I N n
  let E := derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv.{u,w,a,b} I N J n
  apply E.injective
  have h := derivedCoextendScalarsPlusHomologyExtQuotientLinearEquiv_naturality
    I J J (r • 𝟙 N) n x
  change E _ = (E x).comp (Ext.mk₀ (r • 𝟙 N)) (add_zero n) at h
  calc
    E _ = (E x).comp (Ext.mk₀ (r • 𝟙 N)) (add_zero n) := h
    _ = r • E x := (Ext.smul_eq_comp_mk₀ (E x) r).symm
    _ = Ideal.Quotient.mk I r • E x :=
      (Ext.quotientSourceModule_mk_smul I N n r (E x)).symm
    _ = E (Ideal.Quotient.mk I r • x) :=
      (E.map_smul (Ideal.Quotient.mk I r) x).symm

omit [HasExt.{w} (ModuleCat.{u} R)] in
/-- Multiplication on the original coefficient induces quotient multiplication on actual homology.

This identity needs no chosen Ext size or injective resolution in its public interface. -/
theorem derivedCoextendScalarsPlusQuotientHomology_map_smul_id
    (N : ModuleCat.{u} R) (n : ℕ) (r : R) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ I)) (n : ℤ)).map
      ((coextendScalars (Ideal.Quotient.mk I)).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map (r • 𝟙 N))) =
      Ideal.Quotient.mk I r • 𝟙
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R ⧸ I)) (n : ℤ)).obj
          ((coextendScalars (Ideal.Quotient.mk I)).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N))) := by
  let : HasExt.{a} (ModuleCat.{u} R) := hasExt_of_hasDerivedCategory _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact derivedCoextendScalarsPlusQuotientHomology_map_smul_id_apply.{u,a,a,b}
    I N (injectiveResolution N) n r x

end ModuleCat
