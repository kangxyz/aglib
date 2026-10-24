/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.AffineComparison
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.DegreeZero
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Cohomology
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Cohomology.Derived
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.NormalCoefficient

/-!
# Original canonical cohomology and the native derived dual

The same degree-(n+r) closed-embedding Serre map, actual affine derived
sections, original supplied structure-resolution model, native coinduction
complex and original coefficient augmentation compare canonical cohomology
with the actual A-valued derived dual of literal moduleDerivedStructure.

A-linearity follows by matching original source multiplication on both
sides. The same scalar lift acts on the actual supplied resolution; no
linearity of the entire right-derived sections functor is assumed.
The current consumers use r=0 and r=1, and the construction works in every
natural degree. The original source unit and its chain augmentation are
retained explicitly. The final degree-zero regular-source augmentation
normalization against the geometric trace remains the next same-family
adapter and is not asserted in this first comparison row.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CochainComplex CochainComplex.HomComplex HomologicalComplex Opposite

universe u v d

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original structure module, with its scheme module category fixed explicitly. -/
abbrev normalSurfaceUnit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The original structure module has its native finite presentation. -/
theorem normalSurfaceUnit_isFinitePresentation (X : Scheme.{u}) :
    (normalSurfaceUnit X).IsFinitePresentation := by
  let F : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}
  let e : F ≅ normalSurfaceUnit X :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => normalSurfaceUnit X)
  let : IsFiniteLocallyFree X F := finiteLocallyFree_free (X := X) PUnit.{u + 1}
  have hF : F.IsFinitePresentation := isFinitePresentation_of_finiteLocallyFree F
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e hF

end AlgebraicGeometry.Scheme.Cohomology

attribute [local instance]
  AlgebraicGeometry.Scheme.Cohomology.normalSurfaceUnit_isFinitePresentation

private theorem normalSurface_paste_squares
    {C : Type*} [Category* C] {X₀ X₁ X₂ Y₀ Y₁ Y₂ : C}
    {f₀ : X₀ ⟶ Y₀} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : Y₀ ⟶ Y₁} {d : Y₁ ⟶ Y₂}
    (h₁ : f₀ ≫ c = a ≫ f₁) (h₂ : f₁ ≫ d = b ≫ f₂) :
    f₀ ≫ (c ≫ d) = (a ≫ b) ≫ f₂ := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

private theorem normalSurface_preimage_precomp
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C} {Z : D}
    (b : X ⟶ X) (f : F.obj X ⟶ Z) (t : Z ⟶ F.obj Y) :
    F.preimage ((F.map b ≫ f) ≫ t) = b ≫ F.preimage (f ≫ t) := by
  apply F.map_injective
  rw [F.map_comp, F.map_preimage, F.map_preimage]
  exact Category.assoc _ _ _

private theorem normalSurface_map_square
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z W : C} {a : X ⟶ Y} {b : Y ⟶ W} {c : X ⟶ Z} {d : Z ⟶ W}
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg F.map h).trans (F.map_comp c d))

private theorem normalSurface_iso_smul_id
    {C : Type*} [Category* C] [Preadditive C] {A : Type*} [CommRing A] [Linear A C]
    {M N : C} (e : M ≅ N) (a : A) : e.hom ≫ (a • 𝟙 N) ≫ e.inv = a • 𝟙 M := by
  rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, e.hom_inv_id]

private theorem normalSurface_map_three_comp
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X₀ X₁ X₂ X₃ : C} {Y : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (j : F.obj X₃ ⟶ Y) (v : F.obj X₂ ⟶ Y) (h : F.map c ≫ j = v) :
    F.map (a ≫ b ≫ c) ≫ j = F.map a ≫ F.map b ≫ v := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, h]

private theorem normalSurface_paste_three_endomorphisms
    {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ : C}
    {f₀ : X₀ ⟶ X₀} {f₁ : X₁ ⟶ X₁} {f₂ : X₂ ⟶ X₂} {f₃ : X₃ ⟶ X₃}
    {b : X₀ ⟶ X₁} {c : X₁ ⟶ X₂} {d : X₂ ⟶ X₃}
    (hb : f₀ ≫ b = b ≫ f₁) (hc : f₁ ≫ c = c ≫ f₂)
    (hd : f₂ ≫ d = d ≫ f₃) :
    f₀ ≫ b ≫ c ≫ d = (b ≫ c ≫ d) ≫ f₃ := by
  have hbc := normalSurface_paste_squares hb hc
  have h := normalSurface_paste_squares hbc hd
  simpa only [Category.assoc] using h

private theorem normalSurface_source_square_value
    {C : Type*} [Category* C] {X Y Z W : C}
    {a : X ⟶ X} {b : Y ⟶ Y} (c : X ⟶ Y) (t : Z ⟶ W)
    {u v : Y ⟶ Z} (hc : a ≫ c = c ≫ b) (hu : u = b ≫ v) :
    (c ≫ u) ≫ t = a ≫ (c ≫ v) ≫ t := by
  rw [hu, ← Category.assoc c b v, ← hc]
  simp only [Category.assoc]

private theorem normalSurface_resolution_unit
    {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
    [Category* D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] {O : C} (I : InjectiveResolution O)
    {M : D} (c : M ⟶ F.obj O) :
    (DerivedCategory.singleFunctorIsoCompQ D 0).hom.app M ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map c ≫
          (singleMapHomologicalComplex F (.up ℤ) 0).inv.app O ≫
          (F.mapHomologicalComplex (.up ℤ)).map I.ι') ≫
        DerivedCategory.Plus.ι.map (I.rightDerivedFunctorPlusIso F).hom =
      DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.singleFunctor D 0).map c ≫
        F.rightDerivedSingleUnit O) := by
  have hu := congrArg DerivedCategory.Plus.ι.map (I.rightDerivedFunctorPlusIso_unit F)
  simp only [CategoryTheory.Functor.map_comp] at hu
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map I.ι') ≫
      DerivedCategory.Plus.ι.map (I.rightDerivedFunctorPlusIso F).hom =
    DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj O)) at hu
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  change DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map c ≫
      (singleMapHomologicalComplex F (.up ℤ) 0).inv.app O ≫
      (F.mapHomologicalComplex (.up ℤ)).map I.ι') ≫
      DerivedCategory.Plus.ι.map (I.rightDerivedFunctorPlusIso F).hom =
    DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map c) ≫
      DerivedCategory.Q.map ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app O) ≫
      DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj O))
  let j : DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ⟶
      DerivedCategory.Plus.ι.obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj O)) :=
    DerivedCategory.Plus.ι.map (I.rightDerivedFunctorPlusIso F).hom
  let v : DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj O)) ⟶
      DerivedCategory.Plus.ι.obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj O)) :=
    DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj O))
  exact normalSurface_map_three_comp DerivedCategory.Q
    ((CochainComplex.singleFunctor D 0).map c)
    ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app O)
    ((F.mapHomologicalComplex (.up ℤ)).map I.ι') j v hu

private theorem normalSurface_resolution_naturality
    {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
    [Category* D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] {M N : C} {I : InjectiveResolution M}
    {J : InjectiveResolution N} {f : M ⟶ N} (φ : InjectiveResolution.Hom I J f) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
        DerivedCategory.Plus.ι.map (J.rightDerivedFunctorPlusIso F).hom =
      DerivedCategory.Plus.ι.map (I.rightDerivedFunctorPlusIso F).hom ≫
        DerivedCategory.Plus.ι.map
          (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) := by
  let eI : DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ⟶
      DerivedCategory.Plus.ι.obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M)) :=
    DerivedCategory.Plus.ι.map (I.rightDerivedFunctorPlusIso F).hom
  let eJ : DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) ⟶
      DerivedCategory.Plus.ι.obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N)) :=
    DerivedCategory.Plus.ι.map (J.rightDerivedFunctorPlusIso F).hom
  let q : DerivedCategory.Plus.ι.obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M)) ⟶
      DerivedCategory.Plus.ι.obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N)) :=
    DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f))
  have h := normalSurface_map_square DerivedCategory.Plus.ι
    (I.rightDerivedFunctorPlusIso_naturality F φ)
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫ eJ =
    eI ≫ q at h
  exact h

/-- The original affine Hom transport, constructed with variable native endpoints. -/
def normalSurfaceAffineHomEquiv
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
    [Preadditive C₀] [Preadditive C₁] [Preadditive D₀] [Preadditive D₁]
    {R : Type*} [CommRing R] [Linear R D₁]
    (U : C₀ ⥤ C₁) [U.Additive] [U.Full] [U.Faithful]
    (F : C₀ ⥤ D₀) [F.Additive] (V : D₀ ⥤ D₁) [V.Additive] [V.Full] [V.Faithful]
    {K L : C₀} {P : C₁} {S T : D₁} (t : P ≅ U.obj L)
    (c : S ≅ V.obj (F.obj K)) (d : V.obj (F.obj L) ≅ T)
    (hf : Function.Bijective (F.map (X := K) (Y := L))) :
    (U.obj K ⟶ P) ≃+ (S ⟶ T) := by
  let eU : (K ⟶ L) ≃+ (U.obj K ⟶ U.obj L) :=
    { toFun := U.map
      invFun := U.preimage
      left_inv := U.preimage_map
      right_inv := U.map_preimage
      map_add' := fun _ _ => U.map_add }
  let eF : (K ⟶ L) ≃+ (F.obj K ⟶ F.obj L) := AddEquiv.ofBijective F.mapAddHom hf
  let eV : (F.obj K ⟶ F.obj L) ≃+ (V.obj (F.obj K) ⟶ V.obj (F.obj L)) :=
    { toFun := V.map
      invFun := V.preimage
      left_inv := V.preimage_map
      right_inv := V.map_preimage
      map_add' := fun _ _ => V.map_add }
  exact (Linear.homCongr ℤ (Iso.refl _) t).toAddEquiv.trans
    (eU.symm.trans (eF.trans (eV.trans (Linear.homCongr R c.symm d).toAddEquiv)))

private theorem normalSurfaceAffineHomEquiv_apply
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
    [Preadditive C₀] [Preadditive C₁] [Preadditive D₀] [Preadditive D₁]
    {R : Type*} [CommRing R] [Linear R D₁]
    (U : C₀ ⥤ C₁) [U.Additive] [U.Full] [U.Faithful]
    (F : C₀ ⥤ D₀) [F.Additive] (V : D₀ ⥤ D₁) [V.Additive] [V.Full] [V.Faithful]
    {K L : C₀} {P : C₁} {S T : D₁} (t : P ≅ U.obj L)
    (c : S ≅ V.obj (F.obj K)) (d : V.obj (F.obj L) ≅ T)
    (hf : Function.Bijective (F.map (X := K) (Y := L))) (f : U.obj K ⟶ P) :
    normalSurfaceAffineHomEquiv (R := R) U F V t c d hf f =
      c.hom ≫ V.map (F.map (U.preimage (f ≫ t.hom))) ≫ d.hom := by
  change (c.hom ≫ V.map (F.map (U.preimage (((𝟙 _) ≫ f) ≫ t.hom)))) ≫ d.hom = _
  rw [Category.id_comp, Category.assoc]

private theorem normalSurfaceAffineHomEquiv_precomp
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
    [Preadditive C₀] [Preadditive C₁] [Preadditive D₀] [Preadditive D₁]
    {R : Type*} [CommRing R] [Linear R D₁]
    (U : C₀ ⥤ C₁) [U.Additive] [U.Full] [U.Faithful]
    (F : C₀ ⥤ D₀) [F.Additive] (V : D₀ ⥤ D₁) [V.Additive] [V.Full] [V.Faithful]
    {K L : C₀} {P : C₁} {S T : D₁} (t : P ≅ U.obj L)
    (c : S ≅ V.obj (F.obj K)) (d : V.obj (F.obj L) ≅ T)
    (hf : Function.Bijective (F.map (X := K) (Y := L)))
    (b : K ⟶ K) (a : S ⟶ S) (hc : a ≫ c.hom = c.hom ≫ V.map (F.map b))
    (f : U.obj K ⟶ P) :
    normalSurfaceAffineHomEquiv (R := R) U F V t c d hf (U.map b ≫ f) =
      a ≫ normalSurfaceAffineHomEquiv (R := R) U F V t c d hf f := by
  rw [normalSurfaceAffineHomEquiv_apply, normalSurfaceAffineHomEquiv_apply,
    normalSurface_preimage_precomp, F.map_comp, V.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ V.map (F.map (U.preimage (f ≫ t.hom))) ≫ d.hom) hc.symm

private theorem normalSurface_serre_composite_precomp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {X Y : C} {U V W : D} {P Q : E}
    (F : (X ⟶ Y) ≃+ (U ⟶ V)) (t : V ≅ W) (G : (U ⟶ W) ≃+ (P ⟶ Q))
    (a : X ⟶ X) (b : U ⟶ U) (c : P ⟶ P)
    (hF : ∀ x, F (a ≫ x) = b ≫ F x) (hG : ∀ y, G (b ≫ y) = c ≫ G y) (x : X ⟶ Y) :
    (F.trans ((Linear.homCongr ℤ (Iso.refl U) t).toAddEquiv.trans G)) (a ≫ x) =
      c ≫ (F.trans ((Linear.homCongr ℤ (Iso.refl U) t).toAddEquiv.trans G)) x := by
  change G (((𝟙 U) ≫ F (a ≫ x)) ≫ t.hom) = c ≫ G (((𝟙 U) ≫ F x) ≫ t.hom)
  rw [Category.id_comp, Category.id_comp, hF, Category.assoc, hG]

private theorem normalSurface_restricted_iso_smul
    {R A : Type*} [CommRing R] [CommRing A] (σ : R →+* A)
    {M : ModuleCat.{v} A} {N : ModuleCat.{v} R}
    (e : (ModuleCat.restrictScalars σ).obj M ≅ N)
    {P : Type*} (D : N → P)
    (a : A) (m : M ⟶ M) (n : N ⟶ N) (q : P → P)
    (hm : m = a • 𝟙 M)
    (he : (ModuleCat.restrictScalars σ).map m ≫ e.hom = e.hom ≫ n)
    (hd : ∀ y, D (n.hom y) = q (D y)) (x : M) :
    D (e.hom.hom (a • x)) = q (D (e.hom.hom x)) := by
  have h := ConcreteCategory.congr_hom he x
  change e.hom.hom (m.hom x) = n.hom (e.hom.hom x) at h
  rw [hm] at h
  change e.hom.hom (a • x) = n.hom (e.hom.hom x) at h
  exact (congrArg D h).trans (hd _)

/-- The original isomorphism and linear equivalence, with its already identified value
as the forward function and its unchanged original inverse. -/
def normalSurfaceIsoAddEquivOfValue
    {R : Type*} [CommRing R] {M N : ModuleCat.{v} R}
    {P : Type*} [AddCommGroup P] [Module R P]
    (e : M ≅ N) (D : N ≃ₗ[R] P) (d : N → P) (hd : (D : N → P) = d) :
    M ≃+ P where
  toFun := fun x => d (e.hom.hom x)
  invFun := (e.toLinearEquiv.trans D).symm
  left_inv x := by
    rw [← hd]
    exact (e.toLinearEquiv.trans D).symm_apply_apply x
  right_inv y := by
    rw [← hd]
    exact (e.toLinearEquiv.trans D).apply_symm_apply y
  map_add' x y := by
    rw [← hd]
    exact (e.toLinearEquiv.trans D).map_add x y

/-- The value-based constructor is the same original composite equivalence. -/
theorem normalSurfaceIsoAddEquivOfValue_eq
    {R : Type*} [CommRing R] {M N : ModuleCat.{v} R}
    {P : Type*} [AddCommGroup P] [Module R P]
    (e : M ≅ N) (D : N ≃ₗ[R] P) (d : N → P) (hd : (D : N → P) = d) :
    normalSurfaceIsoAddEquivOfValue e D d hd = (e.toLinearEquiv.trans D).toAddEquiv := by
  apply AddEquiv.ext
  intro x
  exact (congrFun hd (e.hom.hom x)).symm

/-- Two original additive comparisons with the same source-scalar formula give a linear
comparison, without installing scalars on the common target. -/
def AddEquiv.linearOfMatchedScalar
    {A S T P : Type*} [CommRing A] [AddCommGroup S] [AddCommGroup T] [AddCommGroup P]
    [Module A S] [Module A T] (E : S ≃+ P) (D : T ≃+ P) (q : A → P → P)
    (hE : ∀ a x, E (a • x) = q a (E x)) (hD : ∀ a y, D (a • y) = q a (D y)) :
    S ≃ₗ[A] T :=
  { E.trans D.symm with
    map_smul' a x := by
      apply D.injective
      change D (D.symm (E (a • x))) = D (a • D.symm (E x))
      rw [D.apply_symm_apply, hD, D.apply_symm_apply]
      exact hE a x }

namespace CochainComplex.HomComplex

variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)

/-- Native restriction and the original evaluation-at-one coinduction chain isomorphism. -/
def coinducedHomologyIso (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ) :
    (ModuleCat.restrictScalars σ).obj
        ((moduleComplex A K (coinducedCoefficientComplex σ I)).homology r) ≅
      (moduleComplex R
        (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) I).homology r :=
  (((moduleComplex A K (coinducedCoefficientComplex σ I)).sc r).mapHomologyIso
      (ModuleCat.restrictScalars σ)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) r).mapIso
      (coinductionComplexIso σ K I)

/-- The comparison retains native homology of both original precomposition chain maps. -/
theorem coinducedHomologyIso_naturality
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ) :
    (ModuleCat.restrictScalars σ).map
        (HomologicalComplex.homologyMap (precomp A f (coinducedCoefficientComplex σ I)) r) ≫
      (coinducedHomologyIso σ K I r).hom =
    (coinducedHomologyIso σ L I r).hom ≫
      HomologicalComplex.homologyMap
        (precomp R (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map f) I) r := by
  let U := ModuleCat.restrictScalars σ
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) r
  let J := coinducedCoefficientComplex σ I
  let b := precomp A f J
  let eK : H.obj ((U.mapHomologicalComplex (.up ℤ)).obj (moduleComplex A K J)) ≅
      U.obj ((moduleComplex A K J).homology r) :=
    ((moduleComplex A K J).sc r).mapHomologyIso U
  let eL : H.obj ((U.mapHomologicalComplex (.up ℤ)).obj (moduleComplex A L J)) ≅
      U.obj ((moduleComplex A L J).homology r) :=
    ((moduleComplex A L J).sc r).mapHomologyIso U
  have h₁ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) (.up ℤ) r).map b) U
  change U.map (HomologicalComplex.homologyMap b r) ≫ eK.inv =
    eL.inv ≫ H.map ((U.mapHomologicalComplex (.up ℤ)).map b) at h₁
  have h₂ := congrArg H.map (coinductionComplexIso_naturality σ f I)
  simp only [CategoryTheory.Functor.map_comp] at h₂
  let cK : H.obj ((U.mapHomologicalComplex (.up ℤ)).obj (moduleComplex A K J)) ⟶
      (moduleComplex R ((U.mapHomologicalComplex (.up ℤ)).obj K) I).homology r :=
    H.map (coinductionComplexIso σ K I).hom
  let cL : H.obj ((U.mapHomologicalComplex (.up ℤ)).obj (moduleComplex A L J)) ⟶
      (moduleComplex R ((U.mapHomologicalComplex (.up ℤ)).obj L) I).homology r :=
    H.map (coinductionComplexIso σ L I).hom
  change H.map ((U.mapHomologicalComplex (.up ℤ)).map b) ≫ cK = cL ≫
    HomologicalComplex.homologyMap
      (precomp R ((U.mapHomologicalComplex (.up ℤ)).map f) I) r at h₂
  change U.map (HomologicalComplex.homologyMap b r) ≫ (eK.inv ≫ cK) =
    (eL.inv ≫ cL) ≫
      HomologicalComplex.homologyMap
        (precomp R ((U.mapHomologicalComplex (.up ℤ)).map f) I) r
  exact normalSurface_paste_squares h₁ h₂

variable [HasDerivedCategory.{d} (ModuleCat.{u} R)]

/-- The genuine A-valued dual homology is compared to original R-derived arrows,
using the actual coinduction, homology/class and localization maps. -/
def coinducedHomologyDerivedAddEquiv (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] (r : ℤ) :
    (ModuleCat.restrictScalars σ).obj
        ((moduleComplex A K (coinducedCoefficientComplex σ I)).homology r) ≃+
      (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) ⟶
        DerivedCategory.Q.obj (I⟦r⟧)) :=
  normalSurfaceIsoAddEquivOfValue (coinducedHomologyIso σ K I r)
    (moduleHomologyDerivedLinearEquiv
      (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) I r)
    (moduleHomologyDerivedValue I r
      (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K))
    (moduleHomologyDerivedLinearEquiv_coe I r
      (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K))

/-- The same original coinduction comparison followed by the compact native class value. -/
def coinducedHomologyDerivedValue (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] (r : ℤ) :
    (ModuleCat.restrictScalars σ).obj
        ((moduleComplex A K (coinducedCoefficientComplex σ I)).homology r) →
      (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) ⟶
        DerivedCategory.Q.obj (I⟦r⟧)) :=
  fun x => moduleHomologyDerivedValue I r
    (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K)
    ((coinducedHomologyIso σ K I r).hom.hom x)

/-- The compact function keeps the original comparison, with no new scalar action. -/
theorem coinducedHomologyDerivedAddEquiv_coe (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] (r : ℤ) :
    (coinducedHomologyDerivedAddEquiv σ K I r : _ → _) =
      coinducedHomologyDerivedValue σ K I r := rfl

/-- The original A-scalar becomes precomposition by the same restricted source multiplication. -/
theorem coinducedHomologyDerivedAddEquiv_smul
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] (r : ℤ)
    (a : A) (x : (moduleComplex A K (coinducedCoefficientComplex σ I)).homology r) :
    coinducedHomologyDerivedAddEquiv σ K I r (a • x) =
      DerivedCategory.Q.map
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map (a • 𝟙 K)) ≫
        coinducedHomologyDerivedAddEquiv σ K I r x := by
  let J := coinducedCoefficientComplex σ I
  let f : K ⟶ K := a • 𝟙 K
  let U := ModuleCat.restrictScalars σ
  let L : CochainComplex (ModuleCat.{u} R) ℤ := (U.mapHomologicalComplex (.up ℤ)).obj K
  let fR : L ⟶ L := (U.mapHomologicalComplex (.up ℤ)).map f
  let M : ModuleCat.{u} A := (moduleComplex A K J).homology r
  let N : ModuleCat.{u} R := (moduleComplex R L I).homology r
  let e : U.obj M ≅ N := coinducedHomologyIso σ K I r
  let m : M ⟶ M := HomologicalComplex.homologyMap (precomp A f J) r
  let g : N ⟶ N := HomologicalComplex.homologyMap (precomp R fR I) r
  let D : N → (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj (I⟦r⟧)) :=
    moduleHomologyDerivedValue I r L
  let q := fun t : DerivedCategory.Q.obj L ⟶
      DerivedCategory.Q.obj (I⟦r⟧) =>
    DerivedCategory.Q.map fR ≫ t
  have hf : m = a • 𝟙 M := by
    change HomologicalComplex.homologyMap (precomp A (a • 𝟙 K) J) r = a • 𝟙 _
    rw [precomp_smul_id, moduleHomologyMap_smul]
    rw [HomologicalComplex.homologyMap_id]
  have he : U.map m ≫ e.hom = e.hom ≫ g := coinducedHomologyIso_naturality σ f I r
  have hd (y : N) : D (g.hom y) = q (D y) := by
    have h := moduleHomologyDerivedLinearEquiv_precomp I r fR y
    simpa only [moduleHomologyDerivedLinearEquiv_coe] using h
  simp only [coinducedHomologyDerivedAddEquiv_coe]
  exact normalSurface_restricted_iso_smul σ e D a m g q hf he hd x

end CochainComplex.HomComplex

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
/-- The standard derived-category model for modules over the coefficient ring. -/
local instance comparisonModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))

/-- The actual supplied structure resolution gives the original model of derived sections. -/
def normalSurfaceStructureResolutionIso
    (I : InjectiveResolution (normalSurfaceUnit X : X.Modules)) :
    DerivedCategory.Q.obj (moduleResolutionSectionComplex X α I) ≅
      DerivedCategory.Plus.ι.obj (moduleDerivedStructure X α) :=
  (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A)).symm.app
      ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj I.cochainComplexPlus) ≪≫
    DerivedCategory.Plus.ι.mapIso
      (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α))

/-- The native inclusion comparison contributes its identity component before the original
resolution comparison. -/
theorem normalSurfaceStructureResolutionIso_hom
    (I : InjectiveResolution (normalSurfaceUnit X)) :
    (normalSurfaceStructureResolutionIso X α I).hom =
      DerivedCategory.Plus.ι.map
        (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).hom := by
  change (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A)).inv.app _ ≫
    DerivedCategory.Plus.ι.map
      (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).hom = _
  rw [DerivedCategory.Plus.QCompιIso_inv_app]
  exact Category.id_comp _

/-- The source-chain unit is the original structural section map followed by the
native single comparison and the actual supplied resolution augmentation. -/
def normalSurfaceStructureResolutionUnit
    (I : InjectiveResolution (normalSurfaceUnit X : X.Modules)) :
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ⟶
      moduleResolutionSectionComplex X α I :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map (moduleStructuralSectionsMap X α) ≫
    (singleMapHomologicalComplex (moduleGlobalSectionsFunctorOfHom X α) (.up ℤ) 0).inv.app
      (normalSurfaceUnit X) ≫
    ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).map I.ι'

/-- Localizing this exact augmentation recovers the installed structural eta_A. -/
theorem normalSurfaceStructureResolutionUnit_normalization
    (I : InjectiveResolution (normalSurfaceUnit X : X.Modules)) :
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).hom.app (ModuleCat.of A A) ≫
        DerivedCategory.Q.map (normalSurfaceStructureResolutionUnit X α I) ≫
        (normalSurfaceStructureResolutionIso X α I).hom =
      DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit X α) := by
  rw [normalSurfaceStructureResolutionIso_hom]
  exact normalSurface_resolution_unit (moduleGlobalSectionsFunctorOfHom X α) I
    (moduleStructuralSectionsMap X α)

/-- Native homology of the actual derived dual is the original supplied-model Hom homology. -/
def normalSurfaceDerivedDualHomologyIso
    (I : InjectiveResolution (normalSurfaceUnit X : X.Modules))
    (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective] (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj
        ((derivedDual J).obj (op (DerivedCategory.Plus.ι.obj (moduleDerivedStructure X α)))) ≅
      (moduleComplex A (moduleResolutionSectionComplex X α I) J).homology r :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).mapIso
      ((derivedDual J).mapIso (normalSurfaceStructureResolutionIso X α I).op ≪≫
        (derivedDualFactors J).app (op (moduleResolutionSectionComplex X α I))) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) r).app
      (moduleComplex A (moduleResolutionSectionComplex X α I) J)

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
/-- The standard derived-category model for modules over the coefficient ring. -/
local instance scalarModelModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))
    (I : InjectiveResolution (normalSurfaceUnit X : X.Modules))

private theorem sectionFunctorLinear :
    letI := moduleCategoryLinearOfHom X α
    (moduleGlobalSectionsFunctorOfHom X α).Linear A := by
  let := moduleCategoryLinearOfHom X α
  constructor
  intro M N f a
  ext x
  have h := moduleCategoryLinearOfHom_smul_app X α f a ⊤ x
  have ht : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := rfl
  rw [ht, X.presheaf.map_id] at h
  exact h

/-- The actual scalar resolution lift is multiplication on the supplied resolution itself. -/
def normalSurfaceScalarResolutionHom (a : A) :
    letI := moduleCategoryLinearOfHom X α
    InjectiveResolution.Hom I I
      (a • 𝟙 (normalSurfaceUnit X : X.Modules)) := by
  let := moduleCategoryLinearOfHom X α
  refine ⟨a • 𝟙 I.cocomplex, ?_⟩
  change I.ι.f 0 ≫ (a • 𝟙 _) = (a • 𝟙 _) ≫ I.ι.f 0
  rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- Extending the original scalar lift preserves the actual scalar on every degree. -/
theorem normalSurfaceScalarResolutionHom_hom (a : A) :
    letI := moduleCategoryLinearOfHom X α
    (normalSurfaceScalarResolutionHom X α I a).hom' = a • 𝟙 I.cochainComplex := by
  let := moduleCategoryLinearOfHom X α
  apply HomologicalComplex.hom_ext
  intro q
  by_cases hq : 0 ≤ q
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [InjectiveResolution.Hom.hom'_f _ (k : ℤ) k rfl]
    let E : (I.cochainComplex.X (k : ℤ) : X.Modules) ≅ I.cocomplex.X k :=
      I.cochainComplexXIso (k : ℤ) k rfl
    change E.hom ≫ (a • 𝟙 _) ≫ E.inv = a • 𝟙 _
    exact normalSurface_iso_smul_id (C := X.Modules) E a
  · exact (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 q
      (lt_of_not_ge hq)).eq_of_src _ _

/-- The source model intertwines original chain multiplication with the actual
derived image of the structure-module multiplication. -/
theorem normalSurfaceStructureResolutionIso_scalar (a : A) :
    letI := moduleCategoryLinearOfHom X α
    DerivedCategory.Q.map (a • 𝟙 (moduleResolutionSectionComplex X α I)) ≫
        (normalSurfaceStructureResolutionIso X α I).hom =
      (normalSurfaceStructureResolutionIso X α I).hom ≫
        DerivedCategory.Plus.ι.map
          ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
              (a • 𝟙 (normalSurfaceUnit X : X.Modules)))) := by
  let := moduleCategoryLinearOfHom X α
  let F := moduleGlobalSectionsFunctorOfHom X α
  let : F.Linear A := sectionFunctorLinear X α
  let φ := normalSurfaceScalarResolutionHom X α I a
  have h := normalSurface_resolution_naturality F φ
  rw [normalSurfaceScalarResolutionHom_hom, CategoryTheory.Functor.map_smul,
    CategoryTheory.Functor.map_id] at h
  rw [normalSurfaceStructureResolutionIso_hom]
  exact h

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
/-- The standard derived-category model for modules over the coefficient ring. -/
local instance comparisonModuleDerivedModel (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable {R A : Type u} [CommRing R] [CommRing A] (X : Scheme.{u})
    (σ : R →+* A) (αA : A →+* Γ(X, ⊤)) (αR : R →+* Γ(X, ⊤))
    (hα : αR = αA.comp σ)

/-- The actual restricted supplied section model, through native exact restriction
and the same original Gamma-restriction comparison. -/
def normalSurfaceRestrictedResolutionIso
    (I : InjectiveResolution (normalSurfaceUnit X : X.Modules)) :
    DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
          (moduleResolutionSectionComplex X αA I)) ≅
      DerivedCategory.Plus.ι.obj (moduleDerivedStructure X αR) :=
  ((ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app
      (moduleResolutionSectionComplex X αA I)).symm ≪≫
    (ModuleCat.restrictScalars σ).mapDerivedCategory.mapIso
      (normalSurfaceStructureResolutionIso X αA I) ≪≫
    (moduleDerivedStructureRestrictionIso X σ αA αR hα).symm

/-- The same full restriction comparison carries every original source endomorphism. -/
theorem normalSurfaceRestrictionIso_source
    (m : (normalSurfaceUnit X : X.Modules) ⟶
      (normalSurfaceUnit X : X.Modules)) :
    (ModuleCat.restrictScalars σ).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((moduleGlobalSectionsFunctorOfHom X αA).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m))) ≫
      (moduleDerivedStructureRestrictionIso X σ αA αR hα).inv =
    (moduleDerivedStructureRestrictionIso X σ αA αR hα).inv ≫
      DerivedCategory.Plus.ι.map
        ((moduleGlobalSectionsFunctorOfHom X αR).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m)) := by
  let U := ModuleCat.restrictScalars σ
  let FA := (moduleGlobalSectionsFunctorOfHom X αA).rightDerivedFunctorPlus
  let FR := (moduleGlobalSectionsFunctorOfHom X αR).rightDerivedFunctorPlus
  let E := moduleDerivedGlobalSectionsRestrictIso X σ αA αR hα
  let T := U.rightDerivedFunctorPlusCompιIso
  let M := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj
    (normalSurfaceUnit X)
  let q := (DerivedCategory.Plus.singleFunctor X.Modules 0).map m
  have hE := congrArg DerivedCategory.Plus.ι.map (E.inv.naturality q)
  simp only [CategoryTheory.Functor.map_comp] at hE
  change DerivedCategory.Plus.ι.map (U.rightDerivedFunctorPlus.map (FA.map q)) ≫
      DerivedCategory.Plus.ι.map (E.inv.app M) =
    DerivedCategory.Plus.ι.map (E.inv.app M) ≫ DerivedCategory.Plus.ι.map (FR.map q) at hE
  have hT := T.inv.naturality (FA.map q)
  change U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (FA.map q)) ≫
      T.inv.app (FA.obj M) =
    T.inv.app (FA.obj M) ≫ DerivedCategory.Plus.ι.map
      (U.rightDerivedFunctorPlus.map (FA.map q)) at hT
  change U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (FA.map q)) ≫
      (T.inv.app (FA.obj M) ≫ DerivedCategory.Plus.ι.map (E.inv.app M)) =
    (T.inv.app (FA.obj M) ≫ DerivedCategory.Plus.ι.map (E.inv.app M)) ≫
      DerivedCategory.Plus.ι.map (FR.map q)
  rw [← Category.assoc, hT, Category.assoc, hE]
  simp only [Category.assoc]

/-- The actual restricted source model preserves source multiplication, without a
linearity assumption on the whole right-derived sections functor. -/
theorem normalSurfaceRestrictedResolutionIso_scalar
    (I : InjectiveResolution (normalSurfaceUnit X : X.Modules)) (a : A) :
    letI := moduleCategoryLinearOfHom X αA
    DerivedCategory.Q.map
        (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map
          (a • 𝟙 (moduleResolutionSectionComplex X αA I))) ≫
      (normalSurfaceRestrictedResolutionIso X σ αA αR hα I).hom =
    (normalSurfaceRestrictedResolutionIso X σ αA αR hα I).hom ≫
      DerivedCategory.Plus.ι.map
        ((moduleGlobalSectionsFunctorOfHom X αR).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
            (a • 𝟙 (normalSurfaceUnit X : X.Modules)))) := by
  let := moduleCategoryLinearOfHom X αA
  let U := ModuleCat.restrictScalars σ
  let K := moduleResolutionSectionComplex X αA I
  let f : K ⟶ K := a • 𝟙 K
  let m : (normalSurfaceUnit X : X.Modules) ⟶
      (normalSurfaceUnit X : X.Modules) := a • 𝟙 _
  let q := (DerivedCategory.Plus.singleFunctor X.Modules 0).map m
  let FA := (moduleGlobalSectionsFunctorOfHom X αA).rightDerivedFunctorPlus
  let FR := (moduleGlobalSectionsFunctorOfHom X αR).rightDerivedFunctorPlus
  let b := U.mapDerivedCategoryFactors.inv.app K
  let c := U.mapDerivedCategory.map (normalSurfaceStructureResolutionIso X αA I).hom
  let d := (moduleDerivedStructureRestrictionIso X σ αA αR hα).inv
  have hb := U.mapDerivedCategoryFactors.inv.naturality f
  change DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map f) ≫ b =
    b ≫ U.mapDerivedCategory.map (DerivedCategory.Q.map f) at hb
  have hc₀ : DerivedCategory.Q.map f ≫ (normalSurfaceStructureResolutionIso X αA I).hom =
      (normalSurfaceStructureResolutionIso X αA I).hom ≫
        DerivedCategory.Plus.ι.map (FA.map q) :=
    normalSurfaceStructureResolutionIso_scalar X αA I a
  have hc : U.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫ c =
      c ≫ U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (FA.map q)) :=
    normalSurface_map_square U.mapDerivedCategory hc₀
  have hd := normalSurfaceRestrictionIso_source X σ αA αR hα m
  change U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (FA.map q)) ≫ d =
    d ≫ DerivedCategory.Plus.ι.map (FR.map q) at hd
  change DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map f) ≫ b ≫ c ≫ d =
    (b ≫ c ≫ d) ≫ DerivedCategory.Plus.ι.map (FR.map q)
  exact normalSurface_paste_three_endomorphisms hb hc hd

end AlgebraicGeometry.Scheme.Cohomology

private theorem functor_map_bijective_of_iso
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F ≅ G) (M N : C)
    (h : Function.Bijective (G.map (X := M) (Y := N))) :
    Function.Bijective (F.map (X := M) (Y := N)) := by
  let E := Iso.homCongr (e.app M) (e.app N)
  have he : E ∘ (F.map (X := M) (Y := N)) = G.map := by
    funext f
    change e.inv.app M ≫ F.map f ≫ e.hom.app N = G.map f
    rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
  exact (Equiv.comp_bijective _ E).mp (he ▸ h)

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
/-- The standard derived-category model for modules over the coefficient ring. -/
local instance comparisonModuleDerived' (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- Both degrees are reindexed through the installed single-functor shifts. -/
def normalSurfaceSingleReindexIso {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (N : C) (n r : ℕ) :
    ((DerivedCategory.singleFunctor C (n : ℤ)).obj N)⟦((n + r : ℕ) : ℤ)⟧ ≅
      ((DerivedCategory.singleFunctor C 0).obj N)⟦(r : ℤ)⟧ :=
  ((DerivedCategory.singleFunctors C).shiftIso ((n + r : ℕ) : ℤ)
      (-(r : ℤ)) (n : ℤ) (by omega)).app N ≪≫
    (((DerivedCategory.singleFunctors C).shiftIso (r : ℤ)
      (-(r : ℤ)) 0 (by omega)).app N).symm

/-- Zero-degree reindexing retains precisely the old target normalization and native zero shift. -/
theorem normalSurfaceSingleReindexIso_zero
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (N : C) (n : ℕ) :
    (normalSurfaceSingleReindexIso N n 0).hom ≫
        (shiftFunctorZero (DerivedCategory C) ℤ).hom.app
          ((DerivedCategory.singleFunctor C 0).obj N) =
      (((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) 0 n (by omega)).app N).hom := by
  change (((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) 0 (n : ℤ)
      (by omega)).hom.app N ≫
    ((DerivedCategory.singleFunctors C).shiftIso (0 : ℤ) 0 0 rfl).inv.app N) ≫
      (shiftFunctorZero (DerivedCategory C) ℤ).hom.app
        ((DerivedCategory.singleFunctor C 0).obj N) = _
  rw [Category.assoc, SingleFunctors.shiftIso_zero_inv_app, Iso.inv_hom_id_app]
  exact Category.comp_id _

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    [IsDominant (i ≫ toSpec R ι)]
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hfin : (genericImageBaseMap R ι i).Finite)

/-- The original Hom source of the actual Serre map in degree n+r. -/
abbrev normalSurfaceCohomologyInput (r : ℕ) :=
  (DerivedCategory.singleFunctor X.Modules 0).obj
      (normalSurfaceUnit X) ⟶
    (DerivedCategory.Plus.ι.obj (normalSurfaceDualizingObject R ι i n))⟦((n + r : ℕ) : ℤ)⟧

/-- The original normalized concentration supplies the higher-degree input reindexing. -/
def normalSurfaceCanonicalDegreeIso (r : ℕ) :
    (DerivedCategory.Plus.ι.obj (normalSurfaceDualizingObject R ι i n))⟦((n + r : ℕ) : ℤ)⟧ ≅
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (normalSurfaceCanonicalModule R ι i n))⟦(r : ℤ)⟧ :=
  (CategoryTheory.shiftFunctor (DerivedCategory X.Modules) ((n + r : ℕ) : ℤ)).mapIso
      (DerivedCategory.Plus.ι.mapIso (normalSurfaceCanonicalIso R ι i hX hXdim n e hfin)) ≪≫
    normalSurfaceSingleReindexIso (normalSurfaceCanonicalModule R ι i n) n r

include hX hXdim e hfin in
/-- Original cohomology and original Ext, followed by the actual concentration and native shifts. -/
def normalSurfaceCohomologyInputLinearEquiv {A : Type u} [CommRing A]
    (α : A →+* Γ(X, ⊤)) (r : ℕ) :
    letI := moduleCategoryLinearOfHom X α
    letI := moduleCohomologyModuleOfHom X α (normalSurfaceCanonicalModule R ι i n) r
    Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) r ≃ₗ[A]
      normalSurfaceCohomologyInput R ι i n r := by
  let := moduleCategoryLinearOfHom X α
  let := moduleCohomologyModuleOfHom X α (normalSurfaceCanonicalModule R ι i n) r
  let O : X.Modules := normalSurfaceUnit X
  let N : X.Modules := normalSurfaceCanonicalModule R ι i n
  let E : Ext.{u + 1} (C := X.Modules) O N r ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf X N) r :=
    moduleExtCohomologyLinearEquivOfCategory X α N r
  let D : Ext.{u + 1} (C := X.Modules) O N r ≃ₗ[A]
      ((DerivedCategory.singleFunctor X.Modules 0).obj O ⟶
        ((DerivedCategory.singleFunctor X.Modules 0).obj N)⟦(r : ℤ)⟧) :=
    Ext.homLinearEquiv (R := A) (X := O) (Y := N) (n := r)
  exact E.symm.trans
    (D.trans
      (Linear.homCongr A (Iso.refl _)
        (normalSurfaceCanonicalDegreeIso R ι i hX hXdim n e hfin r).symm))

/-- Source multiplication on canonical cohomology is the original source multiplication
on the actual degree-(n+r) derived Hom. -/
theorem normalSurfaceCohomologyInputLinearEquiv_source_smul
    {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤)) (r : ℕ) (a : A) :
    letI := moduleCategoryLinearOfHom X α
    letI := moduleCohomologyModuleOfHom X α (normalSurfaceCanonicalModule R ι i n) r
    ∀ x : Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) r,
      normalSurfaceCohomologyInputLinearEquiv R ι i hX hXdim n e hfin α r (a • x) =
        (DerivedCategory.singleFunctor X.Modules 0).map
            (a • 𝟙 (normalSurfaceUnit X : X.Modules)) ≫
          normalSurfaceCohomologyInputLinearEquiv R ι i hX hXdim n e hfin α r x := by
  let := moduleCategoryLinearOfHom X α
  let := moduleCohomologyModuleOfHom X α (normalSurfaceCanonicalModule R ι i n) r
  intro x
  rw [LinearEquiv.map_smul, CategoryTheory.Functor.map_smul,
    CategoryTheory.Functor.map_id, Linear.smul_comp, Category.id_comp]

/-- The original Serre map in the actual degree n+r, with its existing bijectivity theorem. -/
def normalSurfaceSerreDegreeAddEquiv (r : ℕ) :
    normalSurfaceCohomologyInput R ι i n r ≃+
      (DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (i ≫ toSpec R ι)).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
            (normalSurfaceUnit X))) ⟶
        ((DerivedCategory.singleFunctor (Spec (.of R)).Modules (n : ℤ)).obj
          (normalSurfaceUnit (Spec (.of R))))⟦((n + r : ℕ) : ℤ)⟧) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  let O : X.Modules := normalSurfaceUnit X
  let N : (Spec (.of R)).Modules := normalSurfaceUnit (Spec (.of R))
  let : O.IsFinitePresentation := normalSurfaceUnit_isFinitePresentation X
  let : N.IsQuasicoherent := isQuasicoherent_unit (Spec (.of R))
  exact AddEquiv.ofBijective
    (relativeClosedEmbeddingSerreMap i (toSpec R ι) R ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec R ι)) n e
      N O (n + r))
    (relativeClosedEmbeddingSerreMap_bijective i (toSpec R ι) R ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec R ι)) n e
      N O
      (affineLocallyFiniteType_of_finitePresentation O) (n + r))

omit [IsDomain R] [IsRegularLocalRing R] [IsIntegral X]
  [IsDominant (i ≫ toSpec R ι)] in
include n e in
/-- The original derived-sections map is bijective on the actual shifted affine Hom group. -/
theorem normalSurfaceAffineSectionsMap_bijective (r : ℕ) :
    let F := moduleGlobalSectionsFunctorOfHom (Spec (.of R)) (ΓSpecIso (.of R)).inv.hom
    let C := (derivedPushforwardPlus (i ≫ toSpec R ι)).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        (normalSurfaceUnit X))
    let N := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj
      (normalSurfaceUnit (Spec (.of R)))
    Function.Bijective (F.rightDerivedFunctorPlus.map (X := C) (Y := N⟦(r : ℤ)⟧)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let F := moduleGlobalSectionsFunctorOfHom (Spec (.of R)) (ΓSpecIso (.of R)).inv.hom
  let G : (Spec (.of R)).Modules ⥤ ModuleCat.{u} R := moduleSpecΓFunctor
  let : G.Additive := moduleSpecΓFunctor_additive (.of R)
  let D : F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus :=
    F.rightDerivedFunctorPlusIso (moduleAffineGlobalSectionsIso (.of R)).symm
  let : (normalSurfaceUnit X).IsQuasicoherent := isQuasicoherent_unit X
  let : (normalSurfaceUnit (Spec (.of R))).IsQuasicoherent :=
    isQuasicoherent_unit (Spec (.of R))
  exact functor_map_bijective_of_iso D _ _
    (moduleSpecDerivedPushforwardSectionsHom_bijective (i ≫ toSpec R ι)
      (normalSurfaceUnit X)
      (normalSurfaceUnit (Spec (.of R))) 0 r)

/-- Actual derived sections, with the SAME affine target normalization as the original trace. -/
def normalSurfaceAffineHomAddEquiv (r : ℕ) :
    (DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (i ≫ toSpec R ι)).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          (normalSurfaceUnit X))) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of R)).Modules 0).obj
        (normalSurfaceUnit (Spec (.of R))))⟦(r : ℤ)⟧) ≃+
    (DerivedCategory.Plus.ι.obj
        (moduleDerivedStructure X (chosenEmbeddingBaseScalar R i (toSpec R ι))) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))⟦(r : ℤ)⟧) := by
  let Y := Spec (.of R)
  let OX : X.Modules := normalSurfaceUnit X
  let OY : Y.Modules := normalSurfaceUnit Y
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let P := derivedPushforwardPlus (i ≫ toSpec R ι)
  let K := P.obj (SX.obj OX)
  let L := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY
  let F := (moduleGlobalSectionsFunctorOfHom Y (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
  let IY : DerivedCategory.Plus Y.Modules ⥤ DerivedCategory Y.Modules := DerivedCategory.Plus.ι
  let IR : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
    DerivedCategory.Plus.ι
  let C₀ : moduleDerivedStructure X (chosenEmbeddingBaseScalar R i (toSpec R ι)) ≅ F.obj K :=
    (moduleDerivedGlobalSectionsPushforwardCompIso
      (i ≫ toSpec R ι) (ΓSpecIso (.of R)).inv.hom).app (SX.obj OX)
  let C := IR.mapIso C₀
  let T : IR.obj (F.obj (L⟦(r : ℤ)⟧)) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))⟦(r : ℤ)⟧ :=
    IR.mapIso ((F.commShiftIso (r : ℤ)).app L ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory.Plus (ModuleCat.{u} R)) (r : ℤ)).mapIso
        (affineDerivedStructureTargetIso (.of R))) ≪≫
      (IR.commShiftIso (r : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  exact normalSurfaceAffineHomEquiv (R := R) IY F IR ((IY.commShiftIso (r : ℤ)).app L).symm C T
    (normalSurfaceAffineSectionsMap_bijective R ι i n e r)

omit [IsDomain R] [IsRegularLocalRing R] [IsIntegral X]
  [IsDominant (i ≫ toSpec R ι)] in
/-- The explicit forward arrow uses the original bounded-below preimage, actual
derived sections, original composition comparison and same shifted affine target. -/
theorem normalSurfaceAffineHomAddEquiv_apply (r : ℕ)
    (f : DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (i ≫ toSpec R ι)).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          (normalSurfaceUnit X))) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of R)).Modules 0).obj
        (normalSurfaceUnit (Spec (.of R))))⟦(r : ℤ)⟧) :
    let Y := Spec (.of R)
    let L := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
      (normalSurfaceUnit Y)
    let F := (moduleGlobalSectionsFunctorOfHom Y (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
    let C := (moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ toSpec R ι)
      (ΓSpecIso (.of R)).inv.hom).app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          (normalSurfaceUnit X))
    let T := DerivedCategory.Plus.ι.mapIso
        ((F.commShiftIso (r : ℤ)).app L ≪≫
          (CategoryTheory.shiftFunctor (DerivedCategory.Plus (ModuleCat.{u} R)) (r : ℤ)).mapIso
            (affineDerivedStructureTargetIso (.of R))) ≪≫
      (DerivedCategory.Plus.ι.commShiftIso (r : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
    normalSurfaceAffineHomAddEquiv R ι i n e r f =
      DerivedCategory.Plus.ι.map C.hom ≫
        DerivedCategory.Plus.ι.map (F.map
          (DerivedCategory.Plus.ι.preimage
            (f ≫ (DerivedCategory.Plus.ι.commShiftIso (r : ℤ)).inv.app L))) ≫ T.hom := by
  let Y := Spec (.of R)
  let OX : X.Modules := normalSurfaceUnit X
  let OY : Y.Modules := normalSurfaceUnit Y
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let P := derivedPushforwardPlus (i ≫ toSpec R ι)
  let K := P.obj (SX.obj OX)
  let L := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY
  let F := (moduleGlobalSectionsFunctorOfHom Y (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
  let IY : DerivedCategory.Plus Y.Modules ⥤ DerivedCategory Y.Modules := DerivedCategory.Plus.ι
  let IR : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
    DerivedCategory.Plus.ι
  let C₀ : moduleDerivedStructure X (chosenEmbeddingBaseScalar R i (toSpec R ι)) ≅ F.obj K :=
    (moduleDerivedGlobalSectionsPushforwardCompIso
      (i ≫ toSpec R ι) (ΓSpecIso (.of R)).inv.hom).app (SX.obj OX)
  let C := IR.mapIso C₀
  let T : IR.obj (F.obj (L⟦(r : ℤ)⟧)) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))⟦(r : ℤ)⟧ :=
    IR.mapIso ((F.commShiftIso (r : ℤ)).app L ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory.Plus (ModuleCat.{u} R)) (r : ℤ)).mapIso
        (affineDerivedStructureTargetIso (.of R))) ≪≫
      (IR.commShiftIso (r : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  exact normalSurfaceAffineHomEquiv_apply (R := R) IY F IR
    ((IY.commShiftIso (r : ℤ)).app L).symm C T
    (normalSurfaceAffineSectionsMap_bijective R ι i n e r) f

omit [IsDomain R] [IsRegularLocalRing R] [IsIntegral X]
  [IsDominant (i ≫ toSpec R ι)] in
/-- Actual affine derived sections retain every original source module endomorphism. -/
theorem normalSurfaceAffineHomAddEquiv_precomp (r : ℕ)
    (m : (normalSurfaceUnit X : X.Modules) ⟶
      (normalSurfaceUnit X : X.Modules))
    (f : DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (i ≫ toSpec R ι)).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          (normalSurfaceUnit X))) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of R)).Modules 0).obj
        (normalSurfaceUnit (Spec (.of R))))⟦(r : ℤ)⟧) :
    normalSurfaceAffineHomAddEquiv R ι i n e r
        ((derivedPushforwardPlus (i ≫ toSpec R ι) ⋙ DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m) ≫ f) =
      DerivedCategory.Plus.ι.map
          ((moduleGlobalSectionsFunctorOfHom X
            (chosenEmbeddingBaseScalar R i (toSpec R ι))).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m)) ≫
        normalSurfaceAffineHomAddEquiv R ι i n e r f := by
  let Y := Spec (.of R)
  let OX : X.Modules := normalSurfaceUnit X
  let OY : Y.Modules := normalSurfaceUnit Y
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let P := derivedPushforwardPlus (i ≫ toSpec R ι)
  let K := P.obj (SX.obj OX)
  let L := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY
  let F := (moduleGlobalSectionsFunctorOfHom Y (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
  let IY : DerivedCategory.Plus Y.Modules ⥤ DerivedCategory Y.Modules := DerivedCategory.Plus.ι
  let IR : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
    DerivedCategory.Plus.ι
  let C₀ : moduleDerivedStructure X (chosenEmbeddingBaseScalar R i (toSpec R ι)) ≅ F.obj K :=
    (moduleDerivedGlobalSectionsPushforwardCompIso
      (i ≫ toSpec R ι) (ΓSpecIso (.of R)).inv.hom).app (SX.obj OX)
  let C := IR.mapIso C₀
  let T : IR.obj (F.obj (L⟦(r : ℤ)⟧)) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))⟦(r : ℤ)⟧ :=
    IR.mapIso ((F.commShiftIso (r : ℤ)).app L ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory.Plus (ModuleCat.{u} R)) (r : ℤ)).mapIso
        (affineDerivedStructureTargetIso (.of R))) ≪≫
      (IR.commShiftIso (r : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  let FX := (moduleGlobalSectionsFunctorOfHom X
    (chosenEmbeddingBaseScalar R i (toSpec R ι))).rightDerivedFunctorPlus
  let E : FX ≅ P ⋙ F :=
    moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ toSpec R ι) (ΓSpecIso (.of R)).inv.hom
  let q := SX.map m
  let b : K ⟶ K := P.map q
  let a := IR.map (FX.map q)
  have hC : FX.map q ≫ C₀.hom = C₀.hom ≫ F.map b := E.hom.naturality q
  have hc : a ≫ C.hom = C.hom ≫ IR.map (F.map b) := normalSurface_map_square IR hC
  exact normalSurfaceAffineHomEquiv_precomp (R := R) IY F IR
    ((IY.commShiftIso (r : ℤ)).app L).symm C T
    (normalSurfaceAffineSectionsMap_bijective R ι i n e r) b a hc f

/-- The source-local comparison in degree n+r uses the original Serre map,
native target reindexing and actual affine derived sections. -/
def normalSurfaceDerivedSerreAddEquiv (r : ℕ) :
    normalSurfaceCohomologyInput R ι i n r ≃+
      (DerivedCategory.Plus.ι.obj
          (moduleDerivedStructure X (chosenEmbeddingBaseScalar R i (toSpec R ι))) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))⟦(r : ℤ)⟧) :=
  (normalSurfaceSerreDegreeAddEquiv R ι i n e r).trans
    ((Linear.homCongr ℤ (Iso.refl _)
      (normalSurfaceSingleReindexIso (C := (Spec (.of R)).Modules)
        (normalSurfaceUnit (Spec (.of R))) n r)).toAddEquiv.trans
      (normalSurfaceAffineHomAddEquiv R ι i n e r))

omit [IsDomain R] [IsIntegral X] [IsDominant (i ≫ toSpec R ι)] in
/-- The full original Serre-to-derived-sections comparison retains source precomposition. -/
theorem normalSurfaceDerivedSerreAddEquiv_precomp (r : ℕ)
    (m : (normalSurfaceUnit X : X.Modules) ⟶
      (normalSurfaceUnit X : X.Modules))
    (x : normalSurfaceCohomologyInput R ι i n r) :
    normalSurfaceDerivedSerreAddEquiv R ι i n e r
        ((DerivedCategory.singleFunctor X.Modules 0).map m ≫ x) =
      DerivedCategory.Plus.ι.map
          ((moduleGlobalSectionsFunctorOfHom X
            (chosenEmbeddingBaseScalar R i (toSpec R ι))).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m)) ≫
        normalSurfaceDerivedSerreAddEquiv R ι i n e r x := by
  let E := normalSurfaceSerreDegreeAddEquiv R ι i n e r
  let T := normalSurfaceSingleReindexIso (C := (Spec (.of R)).Modules)
    (normalSurfaceUnit (Spec (.of R))) n r
  let G := normalSurfaceAffineHomAddEquiv R ι i n e r
  let a := (DerivedCategory.singleFunctor X.Modules 0).map m
  let b := (derivedPushforwardPlus (i ≫ toSpec R ι) ⋙ DerivedCategory.Plus.ι).map
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m)
  let c := DerivedCategory.Plus.ι.map
    ((moduleGlobalSectionsFunctorOfHom X
      (chosenEmbeddingBaseScalar R i (toSpec R ι))).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m))
  have hE (z : normalSurfaceCohomologyInput R ι i n r) : E (a ≫ z) = b ≫ E z :=
    relativeClosedEmbeddingSerreMap_precomp i (toSpec R ι) R ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec R ι)) n e (normalSurfaceUnit (Spec (.of R))) m (n + r) z
  have hG : ∀ z, G (b ≫ z) = c ≫ G z :=
    normalSurfaceAffineHomAddEquiv_precomp R ι i n e r m
  exact normalSurface_serre_composite_precomp E T G a b c hE hG x

variable {A : Type u} [CommRing A] (σ : R →+* A) (g : X ⟶ Spec (.of A))
    (hg : i ≫ toSpec R ι = g ≫ Spec.map (CommRingCat.ofHom σ))
    (IX : InjectiveResolution (normalSurfaceUnit X : X.Modules))
    (IR : InjectiveResolution (ModuleCat.of R R))

include hX hXdim e hfin hg in
/-- The geometric half uses the SAME Serre map, original source model and target augmentation. -/
def normalSurfaceCohomologyModelAddEquiv (r : ℕ) :
    Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) r ≃+
      (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
            (moduleResolutionSectionComplex X (normalSurfaceTraceScalar g) IX)) ⟶
        DerivedCategory.Q.obj (IR.cochainComplex⟦(r : ℤ)⟧)) := by
  let αA := normalSurfaceTraceScalar g
  let αR := chosenEmbeddingBaseScalar R i (toSpec R ι)
  let hα := normalSurfaceTraceScalar_compatibility R ι i σ g hg
  let := moduleCategoryLinearOfHom X αA
  let := moduleCohomologyModuleOfHom X αA (normalSurfaceCanonicalModule R ι i n) r
  let sourceIso := normalSurfaceRestrictedResolutionIso X σ αA αR hα IX
  let coefficientIso := coefficientShiftIso (ModuleCat.of R R) IR.cochainComplex IR.ι' (r : ℤ)
  exact (normalSurfaceCohomologyInputLinearEquiv R ι i hX hXdim n e hfin αA r).toAddEquiv.trans
    ((normalSurfaceDerivedSerreAddEquiv R ι i n e r).trans
      (Linear.homCongr R sourceIso.symm coefficientIso).toAddEquiv)

/-- The algebraic half uses the actual dual factorization, native coinduction and
passed homology/class/localization comparison on the same supplied source model. -/
def normalSurfaceDualModelAddEquiv (r : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r : ℤ)).obj
        ((derivedDual (coinducedCoefficientComplex σ IR.cochainComplex)).obj
          (op (DerivedCategory.Plus.ι.obj
            (moduleDerivedStructure X (normalSurfaceTraceScalar g))))) ≃+
      (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
            (moduleResolutionSectionComplex X (normalSurfaceTraceScalar g) IX)) ⟶
        DerivedCategory.Q.obj (IR.cochainComplex⟦(r : ℤ)⟧)) :=
  (normalSurfaceDerivedDualHomologyIso X (normalSurfaceTraceScalar g) IX
      (coinducedCoefficientComplex σ IR.cochainComplex) (r : ℤ)).toLinearEquiv.toAddEquiv.trans
    (coinducedHomologyDerivedAddEquiv σ
      (moduleResolutionSectionComplex X (normalSurfaceTraceScalar g) IX) IR.cochainComplex (r : ℤ))

/-- The SAME two original comparisons give the actual dual cohomology equivalence. -/
def normalSurfaceCohomologyDualAddEquiv (r : ℕ) :
    Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) r ≃+
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r : ℤ)).obj
        ((derivedDual (coinducedCoefficientComplex σ IR.cochainComplex)).obj
          (op (DerivedCategory.Plus.ι.obj
            (moduleDerivedStructure X (normalSurfaceTraceScalar g))))) := by
  exact (normalSurfaceCohomologyModelAddEquiv R ι i hX hXdim n e hfin σ g hg IX IR r).trans
    (normalSurfaceDualModelAddEquiv R σ g IX IR r).symm

include hX hXdim e hfin hg IR in
/-- The geometric comparison takes original cohomology scalars to the actual
restricted source multiplication on the same supplied model. -/
theorem normalSurfaceCohomologyModelAddEquiv_smul (r : ℕ) (a : A) :
    letI := moduleCategoryLinearOfHom X (normalSurfaceTraceScalar g)
    letI := moduleCohomologyModuleOfHom X (normalSurfaceTraceScalar g)
      (normalSurfaceCanonicalModule R ι i n) r
    ∀ x : Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) r,
      normalSurfaceCohomologyModelAddEquiv R ι i hX hXdim n e hfin σ g hg IX IR r (a • x) =
        DerivedCategory.Q.map
            (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map
              (a • 𝟙 (moduleResolutionSectionComplex X (normalSurfaceTraceScalar g) IX))) ≫
          normalSurfaceCohomologyModelAddEquiv R ι i hX hXdim n e hfin σ g hg IX IR r x := by
  let αA := normalSurfaceTraceScalar g
  let αR := chosenEmbeddingBaseScalar R i (toSpec R ι)
  let hα := normalSurfaceTraceScalar_compatibility R ι i σ g hg
  let := moduleCategoryLinearOfHom X αA
  let := moduleCohomologyModuleOfHom X αA (normalSurfaceCanonicalModule R ι i n) r
  intro x
  let E := normalSurfaceCohomologyInputLinearEquiv R ι i hX hXdim n e hfin αA r
  let Φ := normalSurfaceDerivedSerreAddEquiv R ι i n e r
  let C := normalSurfaceRestrictedResolutionIso X σ αA αR hα IX
  let T := coefficientShiftIso (ModuleCat.of R R) IR.cochainComplex IR.ι' (r : ℤ)
  let f := ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map
    (a • 𝟙 (moduleResolutionSectionComplex X αA IX))
  let m : (normalSurfaceUnit X : X.Modules) ⟶
      (normalSurfaceUnit X : X.Modules) := a • 𝟙 _
  let b : DerivedCategory.Plus.ι.obj (moduleDerivedStructure X αR) ⟶
      DerivedCategory.Plus.ι.obj (moduleDerivedStructure X αR) :=
    DerivedCategory.Plus.ι.map
      ((moduleGlobalSectionsFunctorOfHom X αR).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m))
  have hs : DerivedCategory.Q.map f ≫ C.hom = C.hom ≫ b :=
    normalSurfaceRestrictedResolutionIso_scalar X σ αA αR hα IX a
  have hE : E (a • x) = (DerivedCategory.singleFunctor X.Modules 0).map m ≫ E x :=
    normalSurfaceCohomologyInputLinearEquiv_source_smul R ι i hX hXdim n e hfin αA r a x
  have hΦ : Φ (E (a • x)) = b ≫ Φ (E x) :=
    (congrArg Φ hE).trans (normalSurfaceDerivedSerreAddEquiv_precomp R ι i n e r m (E x))
  change (C.hom ≫ Φ (E (a • x))) ≫ T.hom =
    DerivedCategory.Q.map f ≫ (C.hom ≫ Φ (E x)) ≫ T.hom
  exact normalSurface_source_square_value C.hom T.hom hs hΦ

omit [IsDomain R] [IsRegularLocalRing R] [IsIntegral X] in
/-- The algebraic comparison has the SAME source-multiplication law, with native A-homology. -/
theorem normalSurfaceDualModelAddEquiv_smul (r : ℕ) (a : A)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r : ℤ)).obj
      ((derivedDual (coinducedCoefficientComplex σ IR.cochainComplex)).obj
        (op (DerivedCategory.Plus.ι.obj
          (moduleDerivedStructure X (normalSurfaceTraceScalar g)))))) :
    normalSurfaceDualModelAddEquiv R σ g IX IR r (a • x) =
      DerivedCategory.Q.map
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map
            (a • 𝟙 (moduleResolutionSectionComplex X (normalSurfaceTraceScalar g) IX))) ≫
        normalSurfaceDualModelAddEquiv R σ g IX IR r x := by
  let K := moduleResolutionSectionComplex X (normalSurfaceTraceScalar g) IX
  let I := IR.cochainComplex
  let H := (normalSurfaceDerivedDualHomologyIso X (normalSurfaceTraceScalar g) IX
    (coinducedCoefficientComplex σ I) (r : ℤ)).toLinearEquiv
  change coinducedHomologyDerivedAddEquiv σ K I (r : ℤ) (H (a • x)) = _
  rw [H.map_smul, coinducedHomologyDerivedAddEquiv_smul]
  rfl

/-- Actual canonical cohomology is A-linearly the native cohomology of the literal
derived dual. The current GR consumers use r=0 and r=1. -/
def normalSurfaceCohomologyDualLinearEquiv (r : ℕ) :
    letI := moduleCohomologyModuleOfHom X (normalSurfaceTraceScalar g)
      (normalSurfaceCanonicalModule R ι i n) r
    Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) r ≃ₗ[A]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r : ℤ)).obj
        ((derivedDual (coinducedCoefficientComplex σ IR.cochainComplex)).obj
          (op (DerivedCategory.Plus.ι.obj
            (moduleDerivedStructure X (normalSurfaceTraceScalar g))))) := by
  let := moduleCategoryLinearOfHom X (normalSurfaceTraceScalar g)
  let := moduleCohomologyModuleOfHom X (normalSurfaceTraceScalar g)
    (normalSurfaceCanonicalModule R ι i n) r
  let E := normalSurfaceCohomologyModelAddEquiv R ι i hX hXdim n e hfin σ g hg IX IR r
  let D := normalSurfaceDualModelAddEquiv R σ g IX IR r
  exact AddEquiv.linearOfMatchedScalar E D
    (fun a t => DerivedCategory.Q.map
      (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map
        (a • 𝟙 (moduleResolutionSectionComplex X (normalSurfaceTraceScalar g) IX))) ≫ t)
    (normalSurfaceCohomologyModelAddEquiv_smul R ι i hX hXdim n e hfin σ g hg IX IR r)
    (normalSurfaceDualModelAddEquiv_smul R σ g IX IR r)

/-- The linear comparison has exactly the original additive forward map. -/
theorem normalSurfaceCohomologyDualLinearEquiv_apply (r : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) r) :
    normalSurfaceCohomologyDualLinearEquiv R ι i hX hXdim n e hfin σ g hg IX IR r x =
      normalSurfaceCohomologyDualAddEquiv R ι i hX hXdim n e hfin σ g hg IX IR r x := rfl

end AlgebraicGeometry.Scheme.Cohomology
