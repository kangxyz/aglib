/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Homothety
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.TwoLayer.UnitNormalization
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.ConcentratedExt

/-!
# Homothety on the original concentrated coinduced homology

The actual coinduced injective resolution is compared with the installed
bounded-below right-derived single, then with its original concentrated
homology. These are the existing derived-unit and homology-normalized
comparisons. Native Hom cohomology and the original shift functor transport
self-Ext and scalar homothety to this same selected module.

Ambient Ext, target Ext, and both derived-category universes are independent.
No replacement canonical module, projectivity over the ambient ring, supplied
canonical trivialization, or reverse Gorenstein criterion is introduced.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex

universe u a b w e

namespace CochainComplex.HomComplex

section Comparison

variable {R S : Type u} [CommRing R] [CommRing S] (q : R →+* S)
  [HasExt.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]
  (N : ModuleCat.{u} R) (I : InjectiveResolution N) (n : ℕ)
  (h : ∀ j : ℕ, j ≠ n → Subsingleton
    (Ext.{w} ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S)) N j))

/-- The original resolution/derived-unit comparison followed by the original
homology-normalized concentration comparison, for the same selected homology. -/
def coinducedCoefficientSingleIso :
    DerivedCategory.Q.obj (coinducedCoefficientComplex q I.cochainComplex) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) (n : ℤ)).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
          ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N))) := by
  let D := (ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N)
  let : D.IsGE (n : ℤ) := ModuleCat.derivedCoextendScalarsPlus_isGE_of_ext q N n
    (fun j hj => h j (by omega))
  let : D.IsLE (n : ℤ) := ModuleCat.derivedCoextendScalarsPlus_isLE_of_ext q N n
    (fun j hj => h j (by omega))
  exact (DerivedCategory.Plus.ι : _ ⥤ DerivedCategory (ModuleCat.{u} S)).mapIso
    (I.rightDerivedFunctorPlusIso (ModuleCat.coextendScalars q) ≪≫
      DerivedCategory.Plus.isoSingleHomology D (n : ℤ))

end Comparison

section Transport

variable {S : Type u} [CommRing S] [HasDerivedCategory.{b} (ModuleCat.{u} S)]

/-- The original fully faithful shift map, with its native scalar linearity. -/
def shiftHomLinearEquiv (X Y : DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    (X ⟶ Y) ≃ₗ[S] (X⟦n⟧ ⟶ Y⟦n⟧) :=
  LinearEquiv.ofBijective ((CategoryTheory.shiftFunctor _ n).mapLinearMap S)
    ((shiftEquiv _ n).fullyFaithfulFunctor.map_bijective X Y)

/-- Shift the displayed concentration comparison to the native degree-zero single. -/
def concentratedCoefficientZeroIso
    (J : CochainComplex (ModuleCat.{u} S) ℤ) (K : ModuleCat.{u} S) (n : ℤ)
    (c : DerivedCategory.Q.obj J ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj K) :
    (DerivedCategory.Q.obj J)⟦n⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj K :=
  (CategoryTheory.shiftFunctor _ n).mapIso c ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso n 0 n (add_zero n)).app K

/-- Original Hom-complex cohomology transported through a displayed
concentration comparison, using the unchanged localization and shift maps. -/
def concentratedSelfHomologyExtLinearEquiv
    [HasExt.{e} (ModuleCat.{u} S)]
    (J : CochainComplex (ModuleCat.{u} S) ℤ) [J.IsKInjective]
    (K : ModuleCat.{u} S) (n : ℤ)
    (c : DerivedCategory.Q.obj J ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj K)
    (i : ℕ) : (moduleComplex S J J).homology (i : ℤ) ≃ₗ[S] Ext.{e} K K i := by
  let z := concentratedCoefficientZeroIso J K n c
  let t : (DerivedCategory.Q.obj (J⟦(i : ℤ)⟧))⟦n⟧ ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj K)⟦(i : ℤ)⟧ :=
    (CategoryTheory.shiftFunctor _ n).mapIso ((DerivedCategory.Q.commShiftIso (i : ℤ)).app J) ≪≫
      (shiftFunctorComm _ (i : ℤ) n).app (DerivedCategory.Q.obj J) ≪≫
      (CategoryTheory.shiftFunctor _ (i : ℤ)).mapIso z
  exact (moduleHomologyDerivedLinearEquiv J J (i : ℤ)).trans
    ((shiftHomLinearEquiv (DerivedCategory.Q.obj J)
      (DerivedCategory.Q.obj (J⟦(i : ℤ)⟧)) n).trans
      ((Linear.homCongr S z t).trans (Ext.homLinearEquiv (R := S)).symm))

omit [HasDerivedCategory.{b} (ModuleCat.{u} S)] in
/-- The original scalar homothety sends a scalar to its actual scalar-identity
cocycle class, through the existing single/cycle normalization. -/
theorem homothety_homologyMap_class
    (J : CochainComplex (ModuleCat.{u} S) ℤ) (s : S) :
    homologyMap (homothety J) 0
        ((singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of S S)).inv s) =
      moduleCocycleClass J J 0 (Cocycle.ofHom (s • 𝟙 J)) := by
  apply single_homologyMap_moduleCocycleClass (ModuleCat.of S S) J J
    (homothety J) s (Cocycle.ofHom (s • 𝟙 J))
  apply Cochain.ext₀
  intro p
  apply ConcreteCategory.hom_ext
  intro x
  change (((homothety J).f 0
    ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of S S)).inv s)).v p p (add_zero p)) x = s • x
  exact homothety_f_zero_v_apply J s p x

/-- Original degree-zero Hom cohomology computes localized endomorphisms,
with the native zero-shift comparison. -/
def moduleHomologyZeroEndLinearEquiv
    (J : CochainComplex (ModuleCat.{u} S) ℤ) [J.IsKInjective] :
    (moduleComplex S J J).homology 0 ≃ₗ[S]
      (DerivedCategory.Q.obj J ⟶ DerivedCategory.Q.obj J) :=
  (moduleHomologyDerivedLinearEquiv J J 0).trans
    (Linear.homCongr S (Iso.refl _)
      (((DerivedCategory.Q.commShiftIso (0 : ℤ)).app J) ≪≫
        (CategoryTheory.shiftFunctorZero _ ℤ).app (DerivedCategory.Q.obj J)))

private theorem moduleHomologyZeroEndLinearEquiv_ofHom
    (J : CochainComplex (ModuleCat.{u} S) ℤ) [J.IsKInjective] (f : J ⟶ J) :
    moduleHomologyZeroEndLinearEquiv J (moduleCocycleClass J J 0 (Cocycle.ofHom f)) =
      DerivedCategory.Q.map f := by
  unfold moduleHomologyZeroEndLinearEquiv
  rw [LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_inv,
    Category.id_comp, moduleHomologyDerivedLinearEquiv_cocycle,
    equivHomShift_symm_ofHom_zero]
  have hm := ShiftedHom.map_mk₀ (0 : ℤ) rfl f
    (DerivedCategory.Q (C := ModuleCat.{u} S))
  change DerivedCategory.Q.map (ShiftedHom.mk₀ (0 : ℤ) rfl f) ≫
      (DerivedCategory.Q.commShiftIso (0 : ℤ)).hom.app J =
    ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map f) at hm
  change DerivedCategory.Q.map (ShiftedHom.mk₀ (0 : ℤ) rfl f) ≫
    ((DerivedCategory.Q.commShiftIso (0 : ℤ)).hom.app J ≫
      (CategoryTheory.shiftFunctorZero _ ℤ).hom.app (DerivedCategory.Q.obj J)) = _
  rw [← Category.assoc, hm]
  simp [ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero']

/-- The original cochain homothety, transported to the endomorphisms of its
concentrated module. The displayed comparison changes no scalar action. -/
def concentratedHomothetyEndLinearEquiv
    (J : CochainComplex (ModuleCat.{u} S) ℤ) [J.IsKInjective] [QuasiIso (homothety J)]
    (K : ModuleCat.{u} S) (n : ℤ)
    (c : DerivedCategory.Q.obj J ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj K) :
    S ≃ₗ[S] (K ⟶ K) := by
  let z := concentratedCoefficientZeroIso J K n c
  let H : ModuleCat.of S S ≅ (moduleComplex S J J).homology 0 :=
    (singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of S S)).symm ≪≫
      asIso (homologyMap (homothety J) 0)
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} S) 0
  let E : (K ⟶ K) ≃ₗ[S] (F.obj K ⟶ F.obj K) :=
    LinearEquiv.ofBijective (F.mapLinearMap S)
      ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective K K)
  exact H.toLinearEquiv.trans ((moduleHomologyZeroEndLinearEquiv J).trans
    ((shiftHomLinearEquiv (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj J) n).trans
      ((Linear.homCongr S z z).trans E.symm)))

/-- The transported homothety is still multiplication by the original scalar,
not an arbitrary endomorphism-module equivalence. -/
theorem concentratedHomothetyEndLinearEquiv_apply
    (J : CochainComplex (ModuleCat.{u} S) ℤ) [J.IsKInjective] [QuasiIso (homothety J)]
    (K : ModuleCat.{u} S) (n : ℤ)
    (c : DerivedCategory.Q.obj J ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj K)
    (s : S) : concentratedHomothetyEndLinearEquiv J K n c s = s • 𝟙 K := by
  let z := concentratedCoefficientZeroIso J K n c
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} S) 0
  let E : (K ⟶ K) ≃ₗ[S] (F.obj K ⟶ F.obj K) :=
    LinearEquiv.ofBijective (F.mapLinearMap S)
      ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective K K)
  apply F.map_injective
  change E (E.symm ((Linear.homCongr S z z)
    ((CategoryTheory.shiftFunctor _ n).map (moduleHomologyZeroEndLinearEquiv J
      (homologyMap (homothety J) 0
        ((singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of S S)).inv s)))))) = F.map (s • 𝟙 K)
  rw [E.apply_symm_apply, homothety_homologyMap_class,
    moduleHomologyZeroEndLinearEquiv_ofHom]
  have hQ := (DerivedCategory.Q (C := ModuleCat.{u} S)).map_id J
  have hShift := (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) n).map_id
    (DerivedCategory.Q.obj J)
  have hF := F.map_id K
  simp only [Functor.map_smul, hQ, hShift, hF, Linear.homCongr_apply,
    Linear.comp_smul, Linear.smul_comp, Category.comp_id, Iso.inv_hom_id]
  rfl

end Transport

section FiniteRegularBase

variable {R S : Type u} [CommRing R] [CommRing S] [IsRegularLocalRing R]
  (q : R →+* S) [Module.Finite R ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S))]
  (d : ℕ) (hd : ringKrullDim R = (d : ℕ))
  [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{e} (ModuleCat.{u} S)]
  [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]
  (n : ℕ) (h : ∀ j : ℕ, j ≠ n → Subsingleton
    (Ext.{w} ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S)) (ModuleCat.of R R) j))

include hd h in
/-- Positive self-Ext vanishes for the same selected concentrated homology of
installed coinduction. All resolution and homothety inputs are proved internally. -/
theorem coinducedHomology_self_ext_subsingleton (i : ℕ) (hi : 0 < i) :
    let K := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
    Subsingleton (Ext.{e} K K i) := by
  let I := injectiveResolution (ModuleCat.of R R)
  let J := coinducedCoefficientComplex q I.cochainComplex
  let : J.IsKInjective := coinducedCoefficientComplex_isKInjective q I.cochainComplex
  let : QuasiIso (homothety J) := homothety_coinduced_injectiveResolution_quasiIso q d hd I
  let c := coinducedCoefficientSingleIso.{u, a, b, w} q (ModuleCat.of R R) I n h
  let E := concentratedSelfHomologyExtLinearEquiv.{u, b, e} J _ (n : ℤ) c i
  have hzero : IsZero ((moduleComplex S J J).homology (i : ℤ)) :=
    (isZero_single_obj_homology (.up ℤ) 0 (ModuleCat.of S S) (i : ℤ) (by omega)).of_iso
      (asIso (homologyMap (homothety J) (i : ℤ))).symm
  let : Subsingleton ((moduleComplex S J J).homology (i : ℤ)) :=
    ModuleCat.isZero_iff_subsingleton.mp hzero
  exact E.symm.injective.subsingleton

omit [HasExt.{e} (ModuleCat.{u} S)] in
include hd in
/-- Scalar homothety on the same selected canonical homology, obtained from
the actual coinduced injective resolution and original concentration maps. -/
def coinducedHomologyHomothetyLinearEquiv :
    let K := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
    S ≃ₗ[S] (K ⟶ K) := by
  let I := injectiveResolution (ModuleCat.of R R)
  let J := coinducedCoefficientComplex q I.cochainComplex
  let : J.IsKInjective := coinducedCoefficientComplex_isKInjective q I.cochainComplex
  let : QuasiIso (homothety J) := homothety_coinduced_injectiveResolution_quasiIso q d hd I
  exact concentratedHomothetyEndLinearEquiv J _ (n : ℤ)
    (coinducedCoefficientSingleIso.{u, a, b, w} q (ModuleCat.of R R) I n h)

omit [HasExt.{e} (ModuleCat.{u} S)] in
include hd in
/-- The final selected-homology equivalence retains the actual scalar map. -/
theorem coinducedHomologyHomothetyLinearEquiv_apply (s : S) :
    coinducedHomologyHomothetyLinearEquiv q d hd n h s = s • 𝟙 _ := by
  let I := injectiveResolution (ModuleCat.of R R)
  let J := coinducedCoefficientComplex q I.cochainComplex
  let : J.IsKInjective := coinducedCoefficientComplex_isKInjective q I.cochainComplex
  let : QuasiIso (homothety J) := homothety_coinduced_injectiveResolution_quasiIso q d hd I
  change concentratedHomothetyEndLinearEquiv J _ (n : ℤ)
    (coinducedCoefficientSingleIso.{u, a, b, w} q (ModuleCat.of R R) I n h) s = _
  exact concentratedHomothetyEndLinearEquiv_apply _ _ _ _ s

end FiniteRegularBase

end CochainComplex.HomComplex
