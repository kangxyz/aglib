/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpen
public import Aglib.Algebra.Homology.Kunneth.MayerVietoris
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars.Zero
public import Mathlib.Algebra.FiveLemma
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# The original mixed-open Mayer–Vietoris ladder

Both rows use the unchanged ambient schemes. The finite antidiagonal source
uses the original restriction and difference maps, and the boundary carries
the degree-p Koszul factor. Its two occurrences cancel against the native
unsigned external-Ext boundary equation in every characteristic.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct DirectSum

universe u

universe r i a b

namespace DirectSum

/-- Canonical distribution of the original finite-support product family. -/
private def prodFamilyEquiv {R : Type r} [CommRing R] {ι : Type i}
    (A : ι → Type a) (B : ι → Type b)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)] :
    (⨁ i, A i × B i) ≃ₗ[R] (⨁ i, A i) × (⨁ i, B i) := by
  let f := DirectSum.lmap (fun i => LinearMap.fst R (A i) (B i))
  let g := DirectSum.lmap (fun i => LinearMap.snd R (A i) (B i))
  let l := DirectSum.lmap (fun i => LinearMap.inl R (A i) (B i))
  let r := DirectSum.lmap (fun i => LinearMap.inr R (A i) (B i))
  exact {
    toFun := fun z => (f z, g z)
    invFun := fun z => l z.1 + r z.2
    left_inv := by
      intro z
      apply DFinsupp.ext
      intro i
      simp [f, g, l, r, DirectSum.lmap_apply]
    right_inv := by
      rintro ⟨z, w⟩
      apply Prod.ext <;> apply DFinsupp.ext <;> intro i <;>
        simp [f, g, l, r, DirectSum.lmap_apply]
    map_add' := fun z w => Prod.ext (f.map_add z w) (g.map_add z w)
    map_smul' := fun c z => Prod.ext (f.map_smul c z) (g.map_smul c z) }

private theorem prodFamilyEquiv_lof {R : Type r} [CommRing R] {ι : Type i}
    [DecidableEq ι] (A : ι → Type a) (B : ι → Type b)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    (i : ι) (x : A i) (y : B i) :
    prodFamilyEquiv (R := R) A B (lof R ι (fun i => A i × B i) i (x, y)) =
      (lof R ι A i x, lof R ι B i y) := by
  change ((lmap (fun i => LinearMap.fst R (A i) (B i)))
      (lof R ι (fun i => A i × B i) i (x, y)),
    (lmap (fun i => LinearMap.snd R (A i) (B i)))
      (lof R ι (fun i => A i × B i) i (x, y))) = _
  rw [lmap_lof, lmap_lof]
  rfl

end DirectSum

namespace ModuleCat

private theorem biprodIsoProd_hom_fst_value {R : Type r} [CommRing R]
    (A B : ModuleCat.{u} R) (x : (A ⊞ B : ModuleCat.{u} R)) :
    ((ModuleCat.biprodIsoProd A B).hom x).1 =
      (biprod.fst : (A ⊞ B : ModuleCat.{u} R) ⟶ A) x := by
  have h : (ModuleCat.biprodIsoProd A B).hom ≫
      ModuleCat.ofHom (LinearMap.fst R A B) =
        (biprod.fst : (A ⊞ B : ModuleCat.{u} R) ⟶ A) := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_fst, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  exact ConcreteCategory.congr_hom h x

private theorem biprodIsoProd_hom_snd_value {R : Type r} [CommRing R]
    (A B : ModuleCat.{u} R) (x : (A ⊞ B : ModuleCat.{u} R)) :
    ((ModuleCat.biprodIsoProd A B).hom x).2 =
      (biprod.snd : (A ⊞ B : ModuleCat.{u} R) ⟶ B) x := by
  have h : (ModuleCat.biprodIsoProd A B).hom ≫
      ModuleCat.ofHom (LinearMap.snd R A B) =
        (biprod.snd : (A ⊞ B : ModuleCat.{u} R) ⟶ B) := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_snd, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  exact ConcreteCategory.congr_hom h x

private theorem biprodIsoProd_lift_value {R : Type r} [CommRing R]
    (A B C : ModuleCat.{u} R) (f : C ⟶ A) (g : C ⟶ B) (x : C) :
    (ModuleCat.biprodIsoProd A B).hom (biprod.lift f g x) = (f x, g x) := by
  apply Prod.ext
  · rw [biprodIsoProd_hom_fst_value]
    exact ConcreteCategory.congr_hom (biprod.lift_fst f g) x
  · rw [biprodIsoProd_hom_snd_value]
    exact ConcreteCategory.congr_hom (biprod.lift_snd f g) x

private theorem biprodIsoProd_desc_value {R : Type r} [CommRing R]
    (A B C : ModuleCat.{u} R) (f : A ⟶ C) (g : B ⟶ C) (x : A) (y : B) :
    biprod.desc f g ((ModuleCat.biprodIsoProd A B).inv (x, y)) = f x + g y := by
  have h : (ModuleCat.biprodIsoProd A B).inv ≫ biprod.desc f g =
      ModuleCat.ofHom (f.hom.comp (LinearMap.fst R A B) +
        g.hom.comp (LinearMap.snd R A B)) := by
    rw [biprod.desc_eq, Preadditive.comp_add, ← Category.assoc,
      ModuleCat.biprodIsoProd_inv_comp_fst, ← Category.assoc,
      ModuleCat.biprodIsoProd_inv_comp_snd]
    rfl
  have hValue := ConcreteCategory.congr_hom h (x, y)
  change biprod.desc f g ((ModuleCat.biprodIsoProd A B).inv (x, y)) =
    f x + g y at hValue
  exact hValue

private theorem biprodIsoProd_desc_sub_inv_value {R : Type r} [CommRing R]
    (A B C : ModuleCat.{u} R) (f : A ⟶ C) (g : B ⟶ C) (x : A) (y : B) :
    biprod.desc f (-g) ((ModuleCat.biprodIsoProd A B).inv (x, y)) = f x - g y := by
  have h := biprodIsoProd_desc_value A B C f (-g) x y
  change biprod.desc f (-g) ((ModuleCat.biprodIsoProd A B).inv (x, y)) =
    f x + -(g y) at h
  simpa only [sub_eq_add_neg] using h

private theorem biprodIsoProd_desc_sub_hom_value {R : Type r} [CommRing R]
    (A B C : ModuleCat.{u} R) (f : A ⟶ C) (g : B ⟶ C)
    (y : (A ⊞ B : ModuleCat.{u} R)) :
    biprod.desc f (-g) y = f ((ModuleCat.biprodIsoProd A B).hom y).1 -
      g ((ModuleCat.biprodIsoProd A B).hom y).2 := by
  have h := biprodIsoProd_desc_sub_inv_value A B C f g
    ((ModuleCat.biprodIsoProd A B).hom y).1 ((ModuleCat.biprodIsoProd A B).hom y).2
  simp only [Prod.mk.eta] at h
  have hCancel := ModuleCat.inv_hom_apply (ModuleCat.biprodIsoProd A B) y
  have hMap := congrArg (fun z => biprod.desc f (-g) z) hCancel
  exact hMap.symm.trans h

private def tensorBiprodFamilyEquiv {R : Type r} [CommRing R]
    (M : ℕ → Type a) [∀ p, AddCommGroup (M p)] [∀ p, Module R (M p)]
    (A B : ℕ → ModuleCat.{u} R) (n : ℕ) :
    Kunneth.MayerVietoris.tensorSum (R := R) M
        (fun q => (A q ⊞ B q : ModuleCat.{u} R)) n ≃ₗ[R]
      Kunneth.MayerVietoris.tensorSum (R := R) M (fun q => A q) n ×
        Kunneth.MayerVietoris.tensorSum (R := R) M (fun q => B q) n :=
  (DirectSum.congrLinearEquiv (fun s : HomologicalComplex₂.TotalDegree n =>
    (TensorProduct.congr (LinearEquiv.refl R (M s.val.1))
      (Iso.toLinearEquiv (ModuleCat.biprodIsoProd (A s.val.2) (B s.val.2)))).trans
        (TensorProduct.prodRight R R (M s.val.1) (A s.val.2) (B s.val.2)))).trans
    (DirectSum.prodFamilyEquiv
      (fun s : HomologicalComplex₂.TotalDegree n => M s.val.1 ⊗[R] A s.val.2)
      (fun s : HomologicalComplex₂.TotalDegree n => M s.val.1 ⊗[R] B s.val.2))

private theorem tensorBiprodFamilyEquiv_lof {R : Type r} [CommRing R]
    (M : ℕ → Type a) [∀ p, AddCommGroup (M p)] [∀ p, Module R (M p)]
    (A B : ℕ → ModuleCat.{u} R) (n : ℕ) (s : HomologicalComplex₂.TotalDegree n)
    (x : M s.val.1) (y : (A s.val.2 ⊞ B s.val.2 : ModuleCat.{u} R)) :
    tensorBiprodFamilyEquiv M A B n (DirectSum.lof R _ _ s (x ⊗ₜ[R] y)) =
      (DirectSum.lof R _ _ s (x ⊗ₜ[R]
          ((ModuleCat.biprodIsoProd (A s.val.2) (B s.val.2)).hom y).1),
        DirectSum.lof R _ _ s (x ⊗ₜ[R]
          ((ModuleCat.biprodIsoProd (A s.val.2) (B s.val.2)).hom y).2)) := by
  simp only [tensorBiprodFamilyEquiv, LinearEquiv.trans_apply,
    DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof, LinearEquiv.coe_toLinearMap,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.prodRight_tmul,
    DirectSum.prodFamilyEquiv_lof]
  rfl

private theorem tensorBiprodFamilyEquiv_first {R : Type r} [CommRing R]
    (M : ℕ → Type a) [∀ p, AddCommGroup (M p)] [∀ p, Module R (M p)]
    (A B P : ℕ → ModuleCat.{u} R) (f : ∀ q, P q ⟶ A q) (g : ∀ q, P q ⟶ B q)
    (n : ℕ) :
    (tensorBiprodFamilyEquiv M A B n).toLinearMap ∘ₗ
        Kunneth.MayerVietoris.tensorMap (R := R) M
          (fun q => (biprod.lift (f q) (g q)).hom) n =
      (Kunneth.MayerVietoris.tensorMap (R := R) M (fun q => (f q).hom) n).prod
        (Kunneth.MayerVietoris.tensorMap (R := R) M (fun q => (g q).hom) n) := by
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext'
  intro x y
  have hStart := Kunneth.MayerVietoris.tensorMap_lof (R := R) M
    (fun q => (biprod.lift (f q) (g q)).hom) n s (x ⊗ₜ[R] y)
  simp only [LinearMap.lTensor_tmul] at hStart
  have hStartMap := congrArg (tensorBiprodFamilyEquiv M A B n) hStart
  have hDist := tensorBiprodFamilyEquiv_lof M A B n s x
    (biprod.lift (f s.val.2) (g s.val.2) y)
  have hLift := biprodIsoProd_lift_value (A s.val.2) (B s.val.2) (P s.val.2)
    (f s.val.2) (g s.val.2) y
  have hLiftMap := congrArg
    (fun z : (A s.val.2) × (B s.val.2) =>
      (DirectSum.lof R (HomologicalComplex₂.TotalDegree n)
          (fun t => M t.val.1 ⊗[R] A t.val.2) s (x ⊗ₜ[R] z.1),
        DirectSum.lof R (HomologicalComplex₂.TotalDegree n)
          (fun t => M t.val.1 ⊗[R] B t.val.2) s (x ⊗ₜ[R] z.2))) hLift
  have hLeft := hStartMap.trans (hDist.trans hLiftMap)
  have hF := Kunneth.MayerVietoris.tensorMap_lof (R := R) M
    (fun q => (f q).hom) n s (x ⊗ₜ[R] y)
  have hG := Kunneth.MayerVietoris.tensorMap_lof (R := R) M
    (fun q => (g q).hom) n s (x ⊗ₜ[R] y)
  simp only [LinearMap.lTensor_tmul] at hF hG
  have hRight := congrArg₂ Prod.mk hF hG
  have hFinal := hLeft.trans hRight.symm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.prod_apply, Function.prod_apply] at hFinal ⊢
  exact hFinal

end ModuleCat

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

private abbrev structureOpenModule (T : FScheme k) (U : T.left.Opens) (n : ℕ) :
    ModuleCat.{u + 1} k :=
  (moduleHPrimePresheaf T.left (constants T) (SheafOfModules.unit T.left.ringCatSheaf) n).obj
    (op U)

private abbrev structureOpenMVMiddleFamily (U V : Y.left.Opens) (q : ℕ) : Type (u + 1) :=
  (structureOpenModule Y U q ⊞ structureOpenModule Y V q : ModuleCat.{u + 1} k)

private abbrev structureOpenMVMiddleSum (U V : Y.left.Opens) (n : ℕ) : Type (u + 1) :=
  Kunneth.MayerVietoris.tensorSum (R := k) (structureCohomology k X)
    (structureOpenMVMiddleFamily Y U V) n

private def structureOpenMVFirst (U V : Y.left.Opens) (q : ℕ) :
    structureOpenCohomology Y (U ⊔ V) q →ₗ[k] structureOpenMVMiddleFamily Y U V q :=
  (moduleMayerVietorisToBiprod Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q).hom

private def structureOpenMVSecond (U V : Y.left.Opens) (q : ℕ) :
    structureOpenMVMiddleFamily Y U V q →ₗ[k] structureOpenCohomology Y (U ⊓ V) q :=
  (moduleMayerVietorisFromBiprod Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q).hom

private theorem structureOpenMVFirst_value (T : FScheme k) (U V : T.left.Opens)
    (n : ℕ) (x : structureOpenCohomology T (U ⊔ V) n) :
    (ModuleCat.biprodIsoProd (structureOpenModule T U n)
        (structureOpenModule T V n)).hom (structureOpenMVFirst T U V n x) =
      (structureOpenRestriction T (homOfLE le_sup_left) n x,
        structureOpenRestriction T (homOfLE le_sup_right) n x) := by
  exact ModuleCat.biprodIsoProd_lift_value
    (structureOpenModule T U n) (structureOpenModule T V n)
    (structureOpenModule T (U ⊔ V) n)
    ((moduleHPrimePresheaf T.left (constants T)
      (SheafOfModules.unit T.left.ringCatSheaf) n).map (homOfLE le_sup_left).op)
    ((moduleHPrimePresheaf T.left (constants T)
      (SheafOfModules.unit T.left.ringCatSheaf) n).map (homOfLE le_sup_right).op) x

private theorem functionExact_of_moduleCat_exact {R : Type r} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (h : S.Exact) :
    Function.Exact S.f.hom S.g.hom :=
  LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker S).mp h).symm

private theorem structureOpenMV_exact_first (U V : Y.left.Opens) (q : ℕ) :
    Function.Exact (structureOpenMVFirst Y U V q) (structureOpenMVSecond Y U V q) := by
  let A := moduleMayerVietorisSequence Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q
  have hA := moduleMayerVietorisSequence_exact Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q
  exact functionExact_of_moduleCat_exact (A.sc hA.toIsComplex 0 (by omega))
    (hA.exact 0 (by omega))

private theorem structureOpenMV_exact_second (U V : Y.left.Opens) (q : ℕ) :
    Function.Exact (structureOpenMVSecond Y U V q)
      (structureOpenMayerVietorisDelta Y U V q) := by
  let A := moduleMayerVietorisSequence Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q
  have hA := moduleMayerVietorisSequence_exact Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q
  exact functionExact_of_moduleCat_exact (A.sc hA.toIsComplex 1 (by omega))
    (hA.exact 1 (by omega))

private theorem structureOpenMV_exact_third (U V : Y.left.Opens) (q : ℕ) :
    Function.Exact (structureOpenMayerVietorisDelta Y U V q)
      (structureOpenMVFirst Y U V (q + 1)) := by
  let A := moduleMayerVietorisSequence Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q
  have hA := moduleMayerVietorisSequence_exact Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V q
  exact functionExact_of_moduleCat_exact (A.sc hA.toIsComplex 2 (by omega))
    (hA.exact 2 (by omega))

private theorem structureOpenMV_first_zero_injective (U V : Y.left.Opens) :
    Function.Injective (structureOpenMVFirst Y U V 0) := by
  let : Mono (moduleMayerVietorisToBiprod Y.left (constants Y)
    (SheafOfModules.unit Y.left.ringCatSheaf) U V 0) :=
    moduleMayerVietorisToBiprod_mono_zero Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) U V
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

private def structureOpenKunnethMVFirst (U V : Y.left.Opens) (n : ℕ) :
    structureOpenKunnethSum X Y (U ⊔ V) n →ₗ[k] structureOpenMVMiddleSum X Y U V n :=
  Kunneth.MayerVietoris.tensorMap (R := k) (structureCohomology k X)
    (fun q => structureOpenMVFirst Y U V q) n

private def structureOpenKunnethMVSecond (U V : Y.left.Opens) (n : ℕ) :
    structureOpenMVMiddleSum X Y U V n →ₗ[k] structureOpenKunnethSum X Y (U ⊓ V) n :=
  Kunneth.MayerVietoris.tensorMap (R := k) (structureCohomology k X)
    (fun q => structureOpenMVSecond Y U V q) n

private theorem structureOpenKunnethMV_exact_first (U V : Y.left.Opens) (n : ℕ) :
    Function.Exact (structureOpenKunnethMVFirst X Y U V n)
      (structureOpenKunnethMVSecond X Y U V n) :=
  Kunneth.MayerVietoris.tensorMap_exact (structureCohomology k X)
    (fun q => structureOpenMVFirst Y U V q) (fun q => structureOpenMVSecond Y U V q)
    (fun q => structureOpenMV_exact_first Y U V q) n

private theorem structureOpenKunnethMV_exact_second (U V : Y.left.Opens) (n : ℕ) :
    Function.Exact (structureOpenKunnethMVSecond X Y U V n)
      (Kunneth.MayerVietoris.tensorBoundary (R := k) (structureCohomology k X)
        (fun q => structureOpenMayerVietorisDelta Y U V q) n) :=
  Kunneth.MayerVietoris.tensorMap_tensorBoundary_exact (structureCohomology k X)
    (fun q => structureOpenMVSecond Y U V q)
    (fun q => structureOpenMayerVietorisDelta Y U V q)
    (fun q => structureOpenMV_exact_second Y U V q) n

private theorem structureOpenKunnethMV_exact_third (U V : Y.left.Opens) (n : ℕ) :
    Function.Exact
      (Kunneth.MayerVietoris.tensorBoundary (R := k) (structureCohomology k X)
        (fun q => structureOpenMayerVietorisDelta Y U V q) n)
      (structureOpenKunnethMVFirst X Y U V (n + 1)) :=
  Kunneth.MayerVietoris.tensorBoundary_tensorMap_exact (structureCohomology k X)
    (fun q => structureOpenMayerVietorisDelta Y U V q)
    (fun q => structureOpenMVFirst Y U V q)
    (fun q => structureOpenMV_exact_third Y U V q)
    (structureOpenMV_first_zero_injective Y U V) n

/-- Only the native tensor/product and finite-support distributions enter the middle. -/
private def structureOpenMVMiddleSourceEquiv (U V : Y.left.Opens) (n : ℕ) :
    structureOpenMVMiddleSum X Y U V n ≃ₗ[k]
      structureOpenKunnethSum X Y U n × structureOpenKunnethSum X Y V n :=
  ModuleCat.tensorBiprodFamilyEquiv (structureCohomology k X)
    (structureOpenModule Y U) (structureOpenModule Y V) n

/-- The two actual mixed maps form the original binary-product middle arrow. -/
private def structureOpenMVMiddleMap (U V : Y.left.Opens) (n : ℕ) :
    structureOpenMVMiddleSum X Y U V n →ₗ[k]
      (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n ⊞
        structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ V) n : ModuleCat.{u + 1} k) :=
  (CategoryTheory.Iso.toLinearEquiv (ModuleCat.biprodIsoProd
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n)
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ V) n))).symm.toLinearMap ∘ₗ
    (LinearMap.prodMap (structureOpenKunnethMap X Y U n) (structureOpenKunnethMap X Y V n)) ∘ₗ
      (structureOpenMVMiddleSourceEquiv X Y U V n).toLinearMap

private theorem structureOpenMVMiddleMap_bijective (U V : Y.left.Opens) (n : ℕ)
    (hU : Function.Bijective (structureOpenKunnethMap X Y U n))
    (hV : Function.Bijective (structureOpenKunnethMap X Y V n)) :
    Function.Bijective (structureOpenMVMiddleMap X Y U V n) := by
  exact (CategoryTheory.Iso.toLinearEquiv (ModuleCat.biprodIsoProd _ _)).symm.bijective.comp
    ((Function.Bijective.prodMap hU hV).comp
      (structureOpenMVMiddleSourceEquiv X Y U V n).bijective)

private theorem structureOpenMVMiddleSourceEquiv_lof (U V : Y.left.Opens) (n : ℕ)
    (s : HomologicalComplex₂.TotalDegree n) (x : structureCohomology k X s.val.1)
    (y : structureOpenMVMiddleFamily Y U V s.val.2) :
    structureOpenMVMiddleSourceEquiv X Y U V n (DirectSum.lof k _ _ s (x ⊗ₜ[k] y)) =
      (DirectSum.lof k _ _ s
          (x ⊗ₜ[k] ((ModuleCat.biprodIsoProd
            (structureOpenModule Y U s.val.2) (structureOpenModule Y V s.val.2)).hom y).1),
        DirectSum.lof k _ _ s
          (x ⊗ₜ[k] ((ModuleCat.biprodIsoProd
            (structureOpenModule Y U s.val.2) (structureOpenModule Y V s.val.2)).hom y).2)) := by
  exact ModuleCat.tensorBiprodFamilyEquiv_lof (structureCohomology k X)
    (structureOpenModule Y U) (structureOpenModule Y V) n s x y

private theorem structureOpenMVSecond_value (U V : Y.left.Opens) (q : ℕ)
    (y : structureOpenMVMiddleFamily Y U V q) :
    structureOpenMVSecond Y U V q y =
      structureOpenRestriction Y (homOfLE inf_le_left) q
          ((ModuleCat.biprodIsoProd (structureOpenModule Y U q)
            (structureOpenModule Y V q)).hom y).1 -
        structureOpenRestriction Y (homOfLE inf_le_right) q
          ((ModuleCat.biprodIsoProd (structureOpenModule Y U q)
            (structureOpenModule Y V q)).hom y).2 := by
  exact ModuleCat.biprodIsoProd_desc_sub_hom_value
    (structureOpenModule Y U q) (structureOpenModule Y V q)
    (structureOpenModule Y (U ⊓ V) q)
    ((moduleHPrimePresheaf Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) q).map
        (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op)
    ((moduleHPrimePresheaf Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) q).map
        (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op) y

private theorem structureOpenMVSecond_inv_value (T : FScheme k) (U V : T.left.Opens)
    (n : ℕ) (x : structureOpenCohomology T U n) (y : structureOpenCohomology T V n) :
    structureOpenMVSecond T U V n
        ((ModuleCat.biprodIsoProd (structureOpenModule T U n)
          (structureOpenModule T V n)).inv (x, y)) =
      structureOpenRestriction T (homOfLE inf_le_left) n x -
        structureOpenRestriction T (homOfLE inf_le_right) n y := by
  exact ModuleCat.biprodIsoProd_desc_sub_inv_value
    (structureOpenModule T U n) (structureOpenModule T V n)
    (structureOpenModule T (U ⊓ V) n)
    ((moduleHPrimePresheaf T.left (constants T)
      (SheafOfModules.unit T.left.ringCatSheaf) n).map
        (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op)
    ((moduleHPrimePresheaf T.left (constants T)
      (SheafOfModules.unit T.left.ringCatSheaf) n).map
        (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op) x y

/-- Original restriction naturality of the original mixed cup. -/
theorem structureExternalOpenCup_restriction {U V : Y.left.Opens} (i : U ⟶ V)
    {p q n : ℕ} (h : p + q = n) (x : structureCohomology k X p)
    (y : structureOpenCohomology Y V q) :
    structureExternalOpenCup X Y U h x (structureOpenRestriction Y i q y) =
      structureOpenRestriction (X ⊗ Y) ((Opens.map (snd X Y).left.base).map i) n
        (structureExternalOpenCup X Y V h x y) := by
  let xE := (structureExtLinearEquiv X p).symm x
  let yE := (structureOpenExtLinearEquiv Y V q).symm y
  have hx : structureExtLinearEquiv X p xE = x := LinearEquiv.apply_symm_apply _ _
  have hy : structureOpenExtLinearEquiv Y V q yE = y := LinearEquiv.apply_symm_apply _ _
  let a := (openFreeFunctor Y.left).map i
  let iZ := (Opens.map (snd X Y).left.base).map i
  have hYR := moduleOpenExtCohomologyMap_restriction Y.left i
    (SheafOfModules.unit Y.left.ringCatSheaf) q yE
  change structureOpenExtLinearEquiv Y U q ((Ext.mk₀ a).comp yE (Nat.zero_add q)) =
    structureOpenRestriction Y i q (structureOpenExtLinearEquiv Y V q yE) at hYR
  have hU := structureExternalOpenCup_apply X Y U h (structureExtLinearEquiv X p xE)
    (structureOpenExtLinearEquiv Y U q ((Ext.mk₀ a).comp yE (Nat.zero_add q)))
  have hV := structureExternalOpenCup_apply X Y V h (structureExtLinearEquiv X p xE)
    (structureOpenExtLinearEquiv Y V q yE)
  simp only [LinearEquiv.symm_apply_apply] at hU hV
  have hRaw := structureExternalOpenExt_restriction X Y i h xE yE
  have hMap := congrArg
    (moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ U)
      (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n) hRaw
  have hZR := moduleOpenExtCohomologyMap_restriction (X ⊗ Y).left iZ
    (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n
    (structureExternalOpenExt X Y V h xE yE)
  change _ = structureOpenRestriction (X ⊗ Y) iZ n
    (moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ V)
      (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n
      (structureExternalOpenExt X Y V h xE yE)) at hZR
  have hInput := congrArg (structureExternalOpenCup X Y U h
    (structureExtLinearEquiv X p xE)) hYR
  have hOutput := congrArg (structureOpenRestriction (X ⊗ Y) iZ n) hV
  have hFinal := (hInput.symm.trans hU).trans ((hMap.trans hZR).trans hOutput.symm)
  rw [hx, hy] at hFinal
  exact hFinal

/-- The whole original tensor restriction square. -/
theorem structureExternalOpenTensor_restriction {U V : Y.left.Opens} (i : U ⟶ V)
    {p q n : ℕ} (h : p + q = n) :
    structureExternalOpenTensor X Y U h ∘ₗ
        TensorProduct.map LinearMap.id (structureOpenRestriction Y i q) =
      structureOpenRestriction (X ⊗ Y) ((Opens.map (snd X Y).left.base).map i) n ∘ₗ
        structureExternalOpenTensor X Y V h := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    structureExternalOpenTensor_tmul]
  exact structureExternalOpenCup_restriction X Y i h x y

/-- Coordinatewise original restriction on the original finite tensor antidiagonal. -/
def structureOpenKunnethRestriction {U V : Y.left.Opens} (i : U ⟶ V) (n : ℕ) :
    structureOpenKunnethSum X Y V n →ₗ[k] structureOpenKunnethSum X Y U n :=
  Kunneth.MayerVietoris.tensorMap (R := k) (structureCohomology k X)
    (fun q => structureOpenRestriction Y i q) n

/-- The whole original mixed Künneth map commutes with restriction. -/
theorem structureOpenKunnethMap_restriction {U V : Y.left.Opens} (i : U ⟶ V) (n : ℕ) :
    structureOpenKunnethMap X Y U n ∘ₗ structureOpenKunnethRestriction X Y i n =
      structureOpenRestriction (X ⊗ Y) ((Opens.map (snd X Y).left.base).map i) n ∘ₗ
        structureOpenKunnethMap X Y V n := by
  classical
  apply DirectSum.linearMap_ext
  intro s
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun (structureExternalOpenTensor_restriction X Y i s.property) z
  simp only [LinearMap.comp_apply, structureOpenKunnethRestriction,
    Kunneth.MayerVietoris.tensorMap_lof, structureOpenKunnethMap_lof,
    LinearMap.lTensor] at h ⊢
  exact h

private def structureOpenKunnethFirstPair (U V : Y.left.Opens) (n : ℕ) :
    structureOpenKunnethSum X Y (U ⊔ V) n →ₗ[k]
      structureOpenKunnethSum X Y U n × structureOpenKunnethSum X Y V n :=
  (structureOpenKunnethRestriction X Y (homOfLE le_sup_left) n).prod
    (structureOpenKunnethRestriction X Y (homOfLE le_sup_right) n)

private theorem structureOpenMVMiddleSourceEquiv_first (U V : Y.left.Opens) (n : ℕ) :
    (structureOpenMVMiddleSourceEquiv X Y U V n).toLinearMap ∘ₗ
        structureOpenKunnethMVFirst X Y U V n =
      structureOpenKunnethFirstPair X Y U V n := by
  exact ModuleCat.tensorBiprodFamilyEquiv_first (structureCohomology k X)
    (structureOpenModule Y U) (structureOpenModule Y V) (structureOpenModule Y (U ⊔ V))
    (fun q => (moduleHPrimePresheaf Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) q).map
        (homOfLE (show U ≤ U ⊔ V from le_sup_left)).op)
    (fun q => (moduleHPrimePresheaf Y.left (constants Y)
      (SheafOfModules.unit Y.left.ringCatSheaf) q).map
        (homOfLE (show V ≤ U ⊔ V from le_sup_right)).op) n

/-- The whole first restriction square uses only the original mixed restrictions. -/
private theorem structureOpenKunnethMV_first_square (U V : Y.left.Opens) (n : ℕ) :
    (structureOpenMVFirst (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
        ((snd X Y).left ⁻¹ᵁ V) n).comp (structureOpenKunnethMap X Y (U ⊔ V) n) =
      (structureOpenMVMiddleMap X Y U V n).comp
        (structureOpenKunnethMVFirst X Y U V n) := by
  apply LinearMap.ext
  intro z
  apply (CategoryTheory.Iso.toLinearEquiv (ModuleCat.biprodIsoProd
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n)
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ V) n))).injective
  have hU := LinearMap.congr_fun
    (structureOpenKunnethMap_restriction X Y (homOfLE (le_sup_left : U ≤ U ⊔ V)) n) z
  have hV := LinearMap.congr_fun
    (structureOpenKunnethMap_restriction X Y (homOfLE (le_sup_right : V ≤ U ⊔ V)) n) z
  have hB := structureOpenMVFirst_value (X ⊗ Y)
    ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n
    (structureOpenKunnethMap X Y (U ⊔ V) n z)
  have hSource := LinearMap.congr_fun
    (structureOpenMVMiddleSourceEquiv_first X Y U V n) z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    structureOpenKunnethFirstPair, LinearMap.prod_apply, Function.prod_apply] at hSource
  simp only [LinearMap.comp_apply, structureOpenMVMiddleMap,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at hB ⊢
  rw [hSource]
  simp only [LinearMap.prodMap_apply]
  exact hB.trans (Prod.ext hU.symm hV.symm)

/-- The whole original difference square follows from its two original restrictions. -/
private theorem structureOpenKunnethMV_second_square (U V : Y.left.Opens) (n : ℕ) :
    (structureOpenMVSecond (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
        ((snd X Y).left ⁻¹ᵁ V) n).comp (structureOpenMVMiddleMap X Y U V n) =
      (structureOpenKunnethMap X Y (U ⊓ V) n).comp
        (structureOpenKunnethMVSecond X Y U V n) := by
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext'
  intro x y
  let yp := (ModuleCat.biprodIsoProd
    (structureOpenModule Y U s.val.2) (structureOpenModule Y V s.val.2)).hom y
  let e := ModuleCat.biprodIsoProd
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n)
    (structureOpenModule (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ V) n)
  let f := LinearMap.prodMap (structureOpenKunnethMap X Y U n)
    (structureOpenKunnethMap X Y V n)
  let value := (structureExternalOpenCup X Y U s.property x yp.1,
    structureExternalOpenCup X Y V s.property x yp.2)
  have hM := congrArg (fun w => e.inv (f w))
    (structureOpenMVMiddleSourceEquiv_lof X Y U V n s x y)
  simp only [f, LinearMap.prodMap_apply, structureOpenKunnethMap_lof,
    structureExternalOpenTensor_tmul] at hM
  change structureOpenMVMiddleMap X Y U V n
    (DirectSum.lof k _ _ s (x ⊗ₜ[k] y)) = e.inv value at hM
  have hLeft := congrArg
    (structureOpenMVSecond (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
      ((snd X Y).left ⁻¹ᵁ V) n) hM
  have hTarget := structureOpenMVSecond_inv_value (X ⊗ Y)
    ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n
    (structureExternalOpenCup X Y U s.property x yp.1)
    (structureExternalOpenCup X Y V s.property x yp.2)
  have hSource := structureOpenMVSecond_value Y U V s.val.2 y
  have hU := structureExternalOpenCup_restriction X Y
    (homOfLE (inf_le_left : U ⊓ V ≤ U)) s.property x yp.1
  have hV := structureExternalOpenCup_restriction X Y
    (homOfLE (inf_le_right : U ⊓ V ≤ V)) s.property x yp.2
  have hSub := (structureExternalOpenCup X Y (U ⊓ V) s.property x).map_sub
    (structureOpenRestriction Y (homOfLE inf_le_left) s.val.2 yp.1)
    (structureOpenRestriction Y (homOfLE inf_le_right) s.val.2 yp.2)
  have hInput := congrArg (structureExternalOpenCup X Y (U ⊓ V) s.property x) hSource
  have hR0 := Kunneth.MayerVietoris.tensorMap_lof (R := k) (structureCohomology k X)
    (fun q => structureOpenMVSecond Y U V q) n s (x ⊗ₜ[k] y)
  simp only [LinearMap.lTensor_tmul] at hR0
  have hR := congrArg (structureOpenKunnethMap X Y (U ⊓ V) n) hR0
  have hR1 := structureOpenKunnethMap_lof X Y (U ⊓ V) n s
    (x ⊗ₜ[k] structureOpenMVSecond Y U V s.val.2 y)
  have hR2 := structureExternalOpenTensor_tmul X Y (U ⊓ V) s.property x
    (structureOpenMVSecond Y U V s.val.2 y)
  have hRight := hR.trans (hR1.trans hR2)
  have hDifference := congrArg₂ (· - ·) hU.symm hV.symm
  have hFinal := hLeft.trans (hTarget.trans
    (hDifference.trans (hSub.symm.trans (hInput.symm.trans hRight.symm))))
  simp only [LinearMap.comp_apply] at hFinal ⊢
  exact hFinal

private theorem integer_koszul_smul {T : Type*} [AddCommGroup T] [Module k T]
    (p : ℕ) (z : T) : ((-1 : ℤ) ^ p) • z = ((-1 : k) ^ p) • z := by
  rw [← Int.cast_smul_eq_zsmul k]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The original cup boundary law expressed with the identical structural field sign. -/
theorem structureExternalOpenCup_mayerVietoris_smul (U V : Y.left.Opens)
    {p q n : ℕ} (h : p + q = n) (x : structureCohomology k X p)
    (y : structureOpenCohomology Y (U ⊓ V) q) :
    structureExternalOpenCup X Y (U ⊔ V) (show p + (q + 1) = n + 1 by omega) x
        (structureOpenMayerVietorisDelta Y U V q y) =
      ((-1 : k) ^ p) • structureOpenMayerVietorisDelta (X ⊗ Y)
        ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n
        (structureExternalOpenCup X Y (U ⊓ V) h x y) := by
  rw [structureExternalOpenCup_mayerVietoris, integer_koszul_smul (k := k)]

/-- The unsigned homogeneous tensor square retains the original structural sign. -/
private theorem structureExternalOpenTensor_boundary (U V : Y.left.Opens)
    {p q n : ℕ} (h : p + q = n) :
    structureExternalOpenTensor X Y (U ⊔ V) (show p + (q + 1) = n + 1 by omega) ∘ₗ
        (structureOpenMayerVietorisDelta Y U V q).lTensor (structureCohomology k X p) =
      ((-1 : k) ^ p) •
        (structureOpenMayerVietorisDelta (X ⊗ Y)
          ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n ∘ₗ
            structureExternalOpenTensor X Y (U ⊓ V) h) := by
  apply TensorProduct.ext'
  intro x y
  change structureExternalOpenCup X Y (U ⊔ V) _ x
    (structureOpenMayerVietorisDelta Y U V q y) = _
  exact structureExternalOpenCup_mayerVietoris_smul X Y U V h x y

/-- The actual signed source boundary on the original finite antidiagonal. -/
def structureOpenKunnethBoundary (U V : Y.left.Opens) (n : ℕ) :
    structureOpenKunnethSum X Y (U ⊓ V) n →ₗ[k]
      structureOpenKunnethSum X Y (U ⊔ V) (n + 1) :=
  Kunneth.MayerVietoris.tensorBoundary (R := k) (structureCohomology k X)
    (fun q => structureOpenMayerVietorisDelta Y U V q) n

/-- The source Koszul sign cancels the native crossing sign in the whole boundary square. -/
theorem structureOpenKunnethMap_boundary (U V : Y.left.Opens) (n : ℕ) :
    structureOpenKunnethMap X Y (U ⊔ V) (n + 1) ∘ₗ structureOpenKunnethBoundary X Y U V n =
      structureOpenMayerVietorisDelta (X ⊗ Y)
          ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n ∘ₗ
        structureOpenKunnethMap X Y (U ⊓ V) n := by
  apply DirectSum.linearMap_ext
  intro s
  apply LinearMap.ext
  intro z
  have hs : s.val.1 + s.val.2 = n := s.property
  let t := Kunneth.MayerVietoris.rightSuccessor n s
  let d := (structureOpenMayerVietorisDelta Y U V s.val.2).lTensor
    (structureCohomology k X s.val.1)
  let sign : k := (-1 : k) ^ s.val.1
  let T := structureExternalOpenTensor X Y (U ⊔ V)
    (show s.val.1 + (s.val.2 + 1) = n + 1 by omega)
  have hB := Kunneth.MayerVietoris.tensorBoundary_lof (R := k) (structureCohomology k X)
    (fun q => structureOpenMayerVietorisDelta Y U V q) n s z
  have hMap := congrArg (structureOpenKunnethMap X Y (U ⊔ V) (n + 1)) hB
  have hLof := structureOpenKunnethMap_lof X Y (U ⊔ V) (n + 1) t (sign • d z)
  have hSmul := T.map_smul sign (d z)
  have hCell := LinearMap.congr_fun (structureExternalOpenTensor_boundary X Y U V s.property) z
  change T (d z) = sign •
    structureOpenMayerVietorisDelta (X ⊗ Y)
      ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n
      (structureExternalOpenTensor X Y (U ⊓ V) s.property z) at hCell
  have hSign := congrArg (fun w => sign • w) hCell
  rw [Kunneth.MayerVietoris.koszul_smul_smul (R := k)] at hSign
  have hRight := congrArg (structureOpenMayerVietorisDelta (X ⊗ Y)
    ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n)
    (structureOpenKunnethMap_lof X Y (U ⊓ V) n s z)
  have hFinal := hMap.trans (hLof.trans (hSmul.trans (hSign.trans hRight.symm)))
  exact hFinal

private theorem structureOpenKunnethMV_first_zero_injective (U V : Y.left.Opens) :
    Function.Injective (structureOpenKunnethMVFirst X Y U V 0) :=
  Kunneth.MayerVietoris.tensorMap_zero_injective (R := k) (structureCohomology k X)
    (fun q => structureOpenMVFirst Y U V q) (structureOpenMV_first_zero_injective Y U V)

/-- Bijectivity of the original mixed maps glues in degree zero by the native four lemma. -/
private theorem structureOpenKunnethMap_bijective_sup_zero (U V : Y.left.Opens)
    (hU : Function.Bijective (structureOpenKunnethMap X Y U 0))
    (hV : Function.Bijective (structureOpenKunnethMap X Y V 0))
    (hI : Function.Bijective (structureOpenKunnethMap X Y (U ⊓ V) 0)) :
    Function.Bijective (structureOpenKunnethMap X Y (U ⊔ V) 0) := by
  exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (structureOpenKunnethMVFirst X Y U V 0) (structureOpenKunnethMVSecond X Y U V 0)
    (structureOpenMVFirst (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) 0)
    (structureOpenMVSecond (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) 0)
    (structureOpenKunnethMap X Y (U ⊔ V) 0) (structureOpenMVMiddleMap X Y U V 0)
    (structureOpenKunnethMap X Y (U ⊓ V) 0)
    (structureOpenKunnethMV_first_square X Y U V 0)
    (structureOpenKunnethMV_second_square X Y U V 0)
    (structureOpenKunnethMV_exact_first X Y U V 0)
    (structureOpenMV_exact_first (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) 0)
    (structureOpenMVMiddleMap_bijective X Y U V 0 hU hV) hI.1
    (structureOpenKunnethMV_first_zero_injective X Y U V)
    (structureOpenMV_first_zero_injective (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
      ((snd X Y).left ⁻¹ᵁ V))

/-- Every positive union degree follows from the native five lemma on the actual signed ladder. -/
private theorem structureOpenKunnethMap_bijective_sup_succ (U V : Y.left.Opens) (n : ℕ)
    (hU : ∀ m, Function.Bijective (structureOpenKunnethMap X Y U m))
    (hV : ∀ m, Function.Bijective (structureOpenKunnethMap X Y V m))
    (hI : ∀ m, Function.Bijective (structureOpenKunnethMap X Y (U ⊓ V) m)) :
    Function.Bijective (structureOpenKunnethMap X Y (U ⊔ V) (n + 1)) := by
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (structureOpenKunnethMVSecond X Y U V n) (structureOpenKunnethBoundary X Y U V n)
    (structureOpenKunnethMVFirst X Y U V (n + 1))
    (structureOpenKunnethMVSecond X Y U V (n + 1))
    (structureOpenMVSecond (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n)
    (structureOpenMayerVietorisDelta (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
      ((snd X Y).left ⁻¹ᵁ V) n)
    (structureOpenMVFirst (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
      ((snd X Y).left ⁻¹ᵁ V) (n + 1))
    (structureOpenMVSecond (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
      ((snd X Y).left ⁻¹ᵁ V) (n + 1))
    (structureOpenMVMiddleMap X Y U V n) (structureOpenKunnethMap X Y (U ⊓ V) n)
    (structureOpenKunnethMap X Y (U ⊔ V) (n + 1))
    (structureOpenMVMiddleMap X Y U V (n + 1))
    (structureOpenKunnethMap X Y (U ⊓ V) (n + 1))
    (structureOpenKunnethMV_second_square X Y U V n)
    (structureOpenKunnethMap_boundary X Y U V n).symm
    (structureOpenKunnethMV_first_square X Y U V (n + 1))
    (structureOpenKunnethMV_second_square X Y U V (n + 1))
    (structureOpenKunnethMV_exact_second X Y U V n)
    (structureOpenKunnethMV_exact_third X Y U V n)
    (structureOpenKunnethMV_exact_first X Y U V (n + 1))
    (structureOpenMV_exact_second (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
      ((snd X Y).left ⁻¹ᵁ V) n)
    (structureOpenMV_exact_third (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
      ((snd X Y).left ⁻¹ᵁ V) n)
    (structureOpenMV_exact_first (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U)
      ((snd X Y).left ⁻¹ᵁ V) (n + 1))
    (structureOpenMVMiddleMap_bijective X Y U V n (hU n) (hV n)).2 (hI n)
    (structureOpenMVMiddleMap_bijective X Y U V (n + 1) (hU (n + 1)) (hV (n + 1)))
    (hI (n + 1)).1

/-- The literal original mixed-open maps glue across an actual union, in all degrees. -/
theorem structureOpenKunnethMap_bijective_sup (U V : Y.left.Opens)
    (hU : ∀ n, Function.Bijective (structureOpenKunnethMap X Y U n))
    (hV : ∀ n, Function.Bijective (structureOpenKunnethMap X Y V n))
    (hI : ∀ n, Function.Bijective (structureOpenKunnethMap X Y (U ⊓ V) n)) :
    ∀ n, Function.Bijective (structureOpenKunnethMap X Y (U ⊔ V) n) := by
  intro n
  cases n with
  | zero => exact structureOpenKunnethMap_bijective_sup_zero X Y U V (hU 0) (hV 0) (hI 0)
  | succ n => exact structureOpenKunnethMap_bijective_sup_succ X Y U V n hU hV hI

end AlgebraicGeometry.Scheme.Cohomology
