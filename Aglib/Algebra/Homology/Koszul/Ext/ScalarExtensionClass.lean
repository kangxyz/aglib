/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors, kangxyz
-/
module
public import Aglib.Algebra.Homology.Koszul.Ext.BaseChange
public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Functor
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Aglib.Algebra.Homology.Embedding.MapExtend
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Regular.Flat

/-!
Original top Koszul classes under exact scalar extension. The private two-column
calculation and ordered ring-complex comparison are selected from the user-owned
Motivic archive, files KoszulScalarRestrictionTensor, KoszulFiniteProjectionExtension
and KoszulExteriorCoefficientComparison, current742 source m27 (2026-10-16).
Only the calculations consumed by the original top-class comparison are retained.
-/
@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Abelian
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra
namespace ChainComplex.Koszul

variable {R S : Type u} [CommRing R] [CommRing S]
section Cross
variable (F : ModuleCat R ⥤ ModuleCat S) [F.Additive]
variable (a : R) (b : S) (K : ChainComplex (ModuleCat R) ℕ)

/-- The image complex under an additive module functor. -/
private abbrev crossMappedComplex := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K

set_option backward.isDefEq.respectTransparency false in
/-- Mapped old-column and new-column inclusions jointly detect maps in positive degrees. -/
private theorem crossMappedSingleTensor_hom_ext {A : ModuleCat S} (n : ℕ)
    {f g : F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1)) ⟶ A}
    (h₀ : F.map (singleTensorιZero a K (n + 1)) ≫ f =
      F.map (singleTensorιZero a K (n + 1)) ≫ g)
    (h₁ : F.map (singleTensorιOne a K n) ≫ f = F.map (singleTensorιOne a K n) ≫ g) :
    f = g := by
  have hd : F.map (singleTensorπZero a K (n + 1)) ≫
        F.map (singleTensorιZero a K (n + 1)) +
      F.map (singleTensorπOne a K n) ≫ F.map (singleTensorιOne a K n) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, singleTensor_decomposition]
    exact F.map_id _
  have h := congrArg (fun p => p ≫ f) hd
  have h' := congrArg (fun p => p ≫ g) hd
  simp only [Preadditive.add_comp, Category.assoc, Category.id_comp] at h h'
  rw [h₀, h₁] at h
  exact h.symm.trans h'

omit [F.Additive] in
set_option backward.isDefEq.respectTransparency false in
/-- The mapped old-column inclusion detects maps in degree zero. -/
private theorem crossMappedSingleTensor_hom_ext_zero {A : ModuleCat S}
    {f g : F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X 0) ⟶ A}
    (h : F.map (singleTensorιZero a K 0) ≫ f = F.map (singleTensorιZero a K 0) ≫ g) :
    f = g := by
  have hd : F.map (singleTensorπZero a K 0) ≫ F.map (singleTensorιZero a K 0) = 𝟙 _ := by
    rw [← Functor.map_comp, singleTensor_decomposition_zero]
    exact F.map_id _
  have h' := congrArg (fun p => F.map (singleTensorπZero a K 0) ≫ p) h
  simpa only [← Category.assoc, hd, Category.id_comp] using h'

/-- The explicit termwise comparison from the image of a one-element tensor. -/
private noncomputable def singleTensorCrossMapToX : (n : ℕ) →
    F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X n) ⟶
      (HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K)).X n
  | 0 => F.map (singleTensorπZero a K 0) ≫ singleTensorιZero b (crossMappedComplex F K) 0
  | n + 1 =>
      F.map (singleTensorπZero a K (n + 1)) ≫
          singleTensorιZero b (crossMappedComplex F K) (n + 1) +
        F.map (singleTensorπOne a K n) ≫ singleTensorιOne b (crossMappedComplex F K) n

/-- The explicit inverse comparison on terms. -/
private noncomputable def singleTensorCrossMapFromX : (n : ℕ) →
    (HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K)).X n ⟶
      F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X n)
  | 0 => singleTensorπZero b (crossMappedComplex F K) 0 ≫ F.map (singleTensorιZero a K 0)
  | n + 1 =>
      singleTensorπZero b (crossMappedComplex F K) (n + 1) ≫
          F.map (singleTensorιZero a K (n + 1)) +
        singleTensorπOne b (crossMappedComplex F K) n ≫ F.map (singleTensorιOne a K n)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private theorem crossMappedιZero_singleTensorCrossMapToX (n : ℕ) :
    F.map (singleTensorιZero a K n) ≫ singleTensorCrossMapToX F a b K n =
      singleTensorιZero b (crossMappedComplex F K) n := by
  cases n <;> simp [singleTensorCrossMapToX, Preadditive.comp_add, ← Category.assoc,
    ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private theorem crossMappedιOne_singleTensorCrossMapToX (n : ℕ) :
    F.map (singleTensorιOne a K n) ≫ singleTensorCrossMapToX F a b K (n + 1) =
      singleTensorιOne b (crossMappedComplex F K) n := by
  simp [singleTensorCrossMapToX, Preadditive.comp_add, ← Category.assoc, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private theorem ιZero_singleTensorCrossMapFromX (n : ℕ) :
    singleTensorιZero b (crossMappedComplex F K) n ≫ singleTensorCrossMapFromX F a b K n =
      F.map (singleTensorιZero a K n) := by
  cases n <;> simp [singleTensorCrossMapFromX, Preadditive.comp_add, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private theorem ιOne_singleTensorCrossMapFromX (n : ℕ) :
    singleTensorιOne b (crossMappedComplex F K) n ≫ singleTensorCrossMapFromX F a b K (n + 1) =
      F.map (singleTensorιOne a K n) := by
  simp [singleTensorCrossMapFromX, Preadditive.comp_add, ← Category.assoc]

/-- The comparison is an actual isomorphism in every degree. -/
private noncomputable def singleTensorCrossMapXIso (n : ℕ) :
    F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X n) ≅
      (HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K)).X n where
  hom := singleTensorCrossMapToX F a b K n
  inv := singleTensorCrossMapFromX F a b K n
  hom_inv_id := by
    cases n with
    | zero =>
      apply crossMappedSingleTensor_hom_ext_zero F a K
      simp only [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX,
        ιZero_singleTensorCrossMapFromX, Category.comp_id]
    | succ n =>
      apply crossMappedSingleTensor_hom_ext F a K n
      · simp only [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX,
          ιZero_singleTensorCrossMapFromX, Category.comp_id]
      · simp only [← Category.assoc, crossMappedιOne_singleTensorCrossMapToX,
          ιOne_singleTensorCrossMapFromX, Category.comp_id]
  inv_hom_id := by
    cases n with
    | zero =>
      apply singleTensor_hom_ext_zero b (crossMappedComplex F K)
      simp only [← Category.assoc, ιZero_singleTensorCrossMapFromX,
        crossMappedιZero_singleTensorCrossMapToX, Category.comp_id]
    | succ n =>
      apply singleTensor_hom_ext b (crossMappedComplex F K) n
      · simp only [← Category.assoc, ιZero_singleTensorCrossMapFromX,
          crossMappedιZero_singleTensorCrossMapToX, Category.comp_id]
      · simp only [← Category.assoc, ιOne_singleTensorCrossMapFromX,
          crossMappedιOne_singleTensorCrossMapToX, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Cross-ring scalar compatibility makes the explicit comparison commute with differentials. -/
private theorem singleTensorCrossMapToX_comm
    (ha : ∀ X : ModuleCat R, F.map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul S (F.obj X) b)) (n : ℕ) :
    singleTensorCrossMapToX F a b K (n + 1) ≫
        (HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K)).d (n + 1) n =
      F.map ((HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n) ≫
        singleTensorCrossMapToX F a b K n := by
  apply crossMappedSingleTensor_hom_ext F a K n
  · rw [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX, singleTensorιZero_d]
    rw [← Category.assoc, ← Functor.map_comp, singleTensorιZero_d,
      Functor.map_comp, Category.assoc, crossMappedιZero_singleTensorCrossMapToX]
    rfl
  · rw [← Category.assoc, crossMappedιOne_singleTensorCrossMapToX]
    cases n with
    | zero =>
      rw [singleTensorιOne_zero_d, ← Category.assoc, ← Functor.map_comp,
        singleTensorιOne_zero_d, Functor.map_comp, Category.assoc,
        crossMappedιZero_singleTensorCrossMapToX, ha]
      rfl
    | succ n =>
      rw [singleTensorιOne_d, ← Category.assoc, ← Functor.map_comp,
        singleTensorιOne_d, Functor.map_sub, Preadditive.sub_comp, Functor.map_comp,
        Functor.map_comp, Category.assoc, Category.assoc,
        crossMappedιZero_singleTensorCrossMapToX, crossMappedιOne_singleTensorCrossMapToX, ha]
      rfl

/-- An additive functor preserving the scalar gives a genuine one-element tensor comparison. -/
private noncomputable def singleTensorCrossMapIso
    (ha : ∀ X : ModuleCat R, F.map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul S (F.obj X) b)) :
    crossMappedComplex F (HomologicalComplex.tensorObj (singleComplex R a) K) ≅
      HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K) :=
  HomologicalComplex.Hom.isoOfComponents (singleTensorCrossMapXIso F a b K) (by
    intro i j hij
    have hi : j + 1 = i := hij
    subst i
    exact singleTensorCrossMapToX_comm F a b K ha j)


private theorem extendScalars_map_lsmul (f : R →+* S) (a : R) (M : ModuleCat R) :
    (ModuleCat.extendScalars f).map (ModuleCat.ofHom (LinearMap.lsmul R M a)) =
      ModuleCat.ofHom (LinearMap.lsmul S ((ModuleCat.extendScalars f).obj M) (f a)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let := f.toAlgebra
  change (1 : S) ⊗ₜ[R] (a • m) = f a • ((1 : S) ⊗ₜ[R] m)
  rw [← TensorProduct.smul_tmul]
  simp only [Algebra.smul_def, mul_one, TensorProduct.smul_tmul']
  rfl


end Cross

section RingComparison
variable [Algebra R S]

private def scalarRingUnitIso :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R R) ≅ ModuleCat.of S S :=
  ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R R) ≪≫
    (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

@[simp] private theorem scalarRingUnitIso_tmul (x : S) (r : R) :
    (scalarRingUnitIso (R := R) (S := S)).hom (x ⊗ₜ[R,algebraMap R S] r) =
      x * algebraMap R S r := by
  change (TensorProduct.AlgebraTensorModule.rid R S S)
    ((ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R R)).hom
      (x ⊗ₜ[R,algebraMap R S] r)) = _
  rw [ModuleCat.extendScalarsAlgebraObjIso_hom_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm]

private def ringExtendIso : (s : List R) →
    crossMappedComplex (ModuleCat.extendScalars (algebraMap R S)) (chainComplex s) ≅
      chainComplex (s.map (algebraMap R S))
  | [] =>
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap R S)) (.down ℕ) 0).app (ModuleCat.of R R) ≪≫
      (ChainComplex.single₀ (ModuleCat S)).mapIso scalarRingUnitIso
  | a :: s =>
      singleTensorCrossMapIso (ModuleCat.extendScalars (algebraMap R S)) a
        (algebraMap R S a) (chainComplex s)
        (extendScalars_map_lsmul (algebraMap R S) a) ≪≫
      whiskerLeftIso (singleComplex S (algebraMap R S a)) (ringExtendIso s)

private theorem tensorιZero_naturality {K L : ChainComplex (ModuleCat S) ℕ}
    (b : S) (f : K ⟶ L) (n : ℕ) :
    singleTensorιZero b K n ≫ ((singleComplex S b) ◁ f).f n =
      f.f n ≫ singleTensorιZero b L n := by
  change (λ_ (K.X n)).inv ≫
    HomologicalComplex.ιMapBifunctor (singleComplex S b) K (curriedTensor (ModuleCat S))
      (.down ℕ) 0 n n (by change 0 + n = n; omega) ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 _) f _ _).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  change (λ_ (K.X n)).inv ≫ (𝟙_ (ModuleCat S)) ◁ f.f n ≫
    HomologicalComplex.ιTensorObj (singleComplex S b) L 0 n n (by omega) =
      f.f n ≫ (λ_ (L.X n)).inv ≫
        HomologicalComplex.ιTensorObj (singleComplex S b) L 0 n n (by omega)
  exact ((leftUnitor_inv_naturality (f.f n)) =≫
    HomologicalComplex.ιTensorObj (singleComplex S b) L 0 n n (by omega)).symm


private theorem tensorιOne_naturality {K L : ChainComplex (ModuleCat S) ℕ}
    (b : S) (f : K ⟶ L) (n : ℕ) :
    singleTensorιOne b K n ≫ ((singleComplex S b) ◁ f).f (n + 1) =
      f.f n ≫ singleTensorιOne b L n := by
  change (λ_ (K.X n)).inv ≫
    HomologicalComplex.ιMapBifunctor (singleComplex S b) K (curriedTensor (ModuleCat S))
      (.down ℕ) 1 n (n + 1) (by change 1 + n = n + 1; omega) ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 _) f _ _).f (n + 1) = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  change (λ_ (K.X n)).inv ≫ (𝟙_ (ModuleCat S)) ◁ f.f n ≫
    HomologicalComplex.ιTensorObj (singleComplex S b) L 1 n (n + 1) (by omega) =
      f.f n ≫ (λ_ (L.X n)).inv ≫
        HomologicalComplex.ιTensorObj (singleComplex S b) L 1 n (n + 1) (by omega)
  exact ((leftUnitor_inv_naturality (f.f n)) =≫
    HomologicalComplex.ιTensorObj (singleComplex S b) L 1 n (n + 1) (by omega)).symm


private theorem ringExtendIso_ιZero (a : R) (s : List R) (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).map (singleTensorιZero a (chainComplex s) n) ≫
        (ringExtendIso (R := R) (S := S) (a :: s)).hom.f n =
      (ringExtendIso (R := R) (S := S) s).hom.f n ≫
        singleTensorιZero (algebraMap R S a) (chainComplex (s.map (algebraMap R S))) n := by
  dsimp only [ringExtendIso, Iso.trans_hom, HomologicalComplex.comp_f,
    whiskerLeftIso_hom, singleTensorCrossMapIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
      singleTensorCrossMapXIso]
  rw [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX]
  exact tensorιZero_naturality _ _ _

private theorem ringExtendIso_ιOne (a : R) (s : List R) (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).map (singleTensorιOne a (chainComplex s) n) ≫
        (ringExtendIso (R := R) (S := S) (a :: s)).hom.f (n + 1) =
      (ringExtendIso (R := R) (S := S) s).hom.f n ≫
        singleTensorιOne (algebraMap R S a) (chainComplex (s.map (algebraMap R S))) n := by
  dsimp only [ringExtendIso, Iso.trans_hom, HomologicalComplex.comp_f,
    whiskerLeftIso_hom, singleTensorCrossMapIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
      singleTensorCrossMapXIso]
  rw [← Category.assoc, crossMappedιOne_singleTensorCrossMapToX]
  exact tensorιOne_naturality _ _ _

private def scalarTopFrame (s : List S) (n : ℕ) (h : n = s.length) :
    (chainComplex s).X n ≅ ModuleCat.of S S :=
  (chainComplex s).XIsoOfEq h ≪≫ topComponentIso s

private theorem scalarTopFrame_cons (b : S) (s : List S) (n : ℕ) (h : n = s.length) :
    singleTensorιOne b (chainComplex s) n ≫
        (scalarTopFrame (b :: s) (n + 1) (by simpa using congrArg Nat.succ h)).hom =
      (scalarTopFrame s n h).hom := by
  subst n
  simpa [scalarTopFrame] using topComponentIso_cons b s

private theorem scalarZeroFrame_cons (a : R) (s : List R) :
    singleTensorιZero a (chainComplex s) 0 ≫ (zeroComponentIso (a :: s)).hom =
      (zeroComponentIso s).hom := by
  dsimp only [singleTensorιZero]
  rw [Category.assoc, ιCons_zero_zero_zeroComponentIso]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem ringExtendIso_zero (s : List R) :
    (ringExtendIso (R := R) (S := S) s).hom.f 0 ≫
        (zeroComponentIso (s.map (algebraMap R S))).hom =
      (ModuleCat.extendScalars (algebraMap R S)).map (zeroComponentIso s).hom ≫
        (scalarRingUnitIso (R := R) (S := S)).hom := by
  induction s with
  | nil =>
    change (ringExtendIso (R := R) (S := S) []).hom.f 0 ≫
      (zeroComponentIso ([] : List S)).hom = _
    have hF : ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap R S)) (.down ℕ) 0).hom.app
          (ModuleCat.of R R)).f 0 =
        𝟙 ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R R)) := by
      rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
      simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
        CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
    dsimp only [ringExtendIso, zeroComponentIso, scalarRingUnitIso, Iso.trans_hom,
      HomologicalComplex.comp_f, Functor.mapIso_hom]
    simp only [ChainComplex.single₀_map_f_zero, ChainComplex.single₀ObjXSelf, Iso.refl_hom]
    change (((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap R S)) (.down ℕ) 0).hom.app
          (ModuleCat.of R R)).f 0 ≫
      (scalarRingUnitIso (R := R) (S := S)).hom) ≫ (𝟙 _) =
        (ModuleCat.extendScalars (algebraMap R S)).map (𝟙 _) ≫
          (scalarRingUnitIso (R := R) (S := S)).hom
    rw [hF, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact Category.id_comp _
  | cons a s ih =>
    apply crossMappedSingleTensor_hom_ext_zero
      (ModuleCat.extendScalars (algebraMap R S)) a (chainComplex s)
    change (ModuleCat.extendScalars (algebraMap R S)).map
      (singleTensorιZero a (chainComplex s) 0) ≫
        (ringExtendIso (R := R) (S := S) (a :: s)).hom.f 0 ≫
          (zeroComponentIso ((algebraMap R S a) :: s.map (algebraMap R S))).hom = _
    rw [← Category.assoc, ringExtendIso_ιZero, Category.assoc,
      scalarZeroFrame_cons, ih]
    rw [← Functor.map_comp_assoc, scalarZeroFrame_cons]

private theorem ringExtendIso_top (s : List R) :
    (ringExtendIso (R := R) (S := S) s).hom.f s.length ≫
        (scalarTopFrame (s.map (algebraMap R S)) s.length (List.length_map (as := s) _).symm).hom =
      (ModuleCat.extendScalars (algebraMap R S)).map (topComponentIso s).hom ≫
        (scalarRingUnitIso (R := R) (S := S)).hom := by
  induction s with
  | nil =>
    change (ringExtendIso (R := R) (S := S) []).hom.f 0 ≫
      (topComponentIso ([] : List S)).hom = _
    exact ringExtendIso_zero (R := R) (S := S) []
  | cons a s ih =>
    simp only [List.length_cons]
    have hι : IsIso (singleTensorιOne a (chainComplex s) s.length) := by
      exact inferInstanceAs (IsIso (topComponentConsIso a s).inv)
    apply (cancel_epi ((ModuleCat.extendScalars (algebraMap R S)).map
      (singleTensorιOne a (chainComplex s) s.length))).mp
    change (ModuleCat.extendScalars (algebraMap R S)).map
      (singleTensorιOne a (chainComplex s) s.length) ≫
        (ringExtendIso (R := R) (S := S) (a :: s)).hom.f (s.length + 1) ≫
          (scalarTopFrame ((algebraMap R S a) :: s.map (algebraMap R S))
            (s.length + 1) (by simp)).hom = _
    rw [← Category.assoc, ringExtendIso_ιOne, Category.assoc,
      scalarTopFrame_cons (algebraMap R S a) (s.map (algebraMap R S)) s.length
        (List.length_map (as := s) _).symm, ih]
    rw [← Functor.map_comp_assoc, topComponentIso_cons]

private theorem ringExtendIso_inv_top (s : List R) :
    (ringExtendIso (R := R) (S := S) s).inv.f s.length ≫
        (ModuleCat.extendScalars (algebraMap R S)).map (topComponentIso s).hom ≫
        (scalarRingUnitIso (R := R) (S := S)).hom =
      (scalarTopFrame (s.map (algebraMap R S)) s.length
        (List.length_map (as := s) _).symm).hom := by
  have h := congrArg (fun k => (ringExtendIso (R := R) (S := S) s).inv.f s.length ≫ k)
    (ringExtendIso_top (R := R) (S := S) s)
  simpa only [← Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.id_comp] using h.symm

end RingComparison

section ProjectiveClass
open HomologicalComplex CochainComplex HomComplex
variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesProjectiveObjects] {X Y : C} (P : ProjectiveResolution X)

private def mappedProjectiveCochainIso :
    (G.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex ≅
      (G.mapProjectiveResolution P).cochainComplex :=
  P.complex.mapExtendIso G ComplexShape.embeddingDownNat

private theorem mappedProjectiveCochainIso_term (n : ℕ) :
    (mappedProjectiveCochainIso G P).hom.f (-(n : ℤ)) ≫
        ((G.mapProjectiveResolution P).cochainComplexXIso (-(n : ℤ)) n rfl).hom =
      G.map (P.cochainComplexXIso (-(n : ℤ)) n rfl).hom :=
  P.complex.mapExtendIso_hom_f_extendXIso G ComplexShape.embeddingDownNat rfl

private theorem mappedProjectiveCochainIso_inv_term (n : ℕ) :
    (mappedProjectiveCochainIso G P).inv.f (-(n : ℤ)) ≫
        G.map (P.cochainComplexXIso (-(n : ℤ)) n rfl).hom =
      ((G.mapProjectiveResolution P).cochainComplexXIso (-(n : ℤ)) n rfl).hom := by
  have h := congrArg (fun k => (mappedProjectiveCochainIso G P).inv.f (-(n : ℤ)) ≫ k)
    (mappedProjectiveCochainIso_term G P n)
  simpa only [← Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.id_comp] using h.symm

private theorem mappedProjectiveCochainIso_augmentation :
    (mappedProjectiveCochainIso G P).hom ≫ (G.mapProjectiveResolution P).π' =
      (G.mapHomologicalComplex (.up ℤ)).map P.π' ≫
        (G.mapCochainComplexSingleFunctor 0).hom.app X := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, ProjectiveResolution.π'_f_zero,
    Functor.mapProjectiveResolution_π, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Functor.mapCochainComplexSingleFunctor, Functor.map_comp, Category.assoc,
    ]
  have ht : (mappedProjectiveCochainIso G P).hom.f 0 ≫
      ((G.mapProjectiveResolution P).cochainComplexXIso 0 0 rfl).hom =
        G.map (P.cochainComplexXIso 0 0 rfl).hom :=
    mappedProjectiveCochainIso_term G P 0
  rw [reassoc_of% ht]
  simp [CochainComplex.singleFunctor]


private def projectiveCycleHom {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n + 1) n ≫ f = 0) :
    ShiftedHom P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ) :=
  Cocycle.equivHomShift.symm
    (Cocycle.toSingleMk ((P.cochainComplexXIso (-(n : ℤ)) n rfl).hom ≫ f)
      (by simp) (-((n + 1 : ℕ) : ℤ)) (by omega)
      (by
        rw [P.cochainComplex_d _ _ (n + 1) n rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hf, comp_zero]))


variable [HasExt.{w} C] [HasExt.{z} D]

private theorem projectiveExtMk_hom [HasDerivedCategory C]
    {n : ℕ} (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n + 1) n ≫ f = 0) :
    (P.extMk f (n + 1) rfl hf).hom =
      inv (DerivedCategory.Q.map P.π') ≫ (projectiveCycleHom P f hf).map DerivedCategory.Q := by
  rw [P.extMk_hom]
  change (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 _ ≫ inv (DerivedCategory.Q.map P.π'))).comp
    (((projectiveCycleHom P f hf).map DerivedCategory.Q).comp
      (ShiftedHom.mk₀ 0 rfl (𝟙 _)) (zero_add _)) (add_zero _) = _
  simp only [Category.id_comp, ShiftedHom.comp_mk₀_id, ShiftedHom.mk₀_comp]

omit [HasExt C] [HasExt D] in
private theorem mappedProjectiveCycleHom {n : ℕ}
    (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n + 1) n ≫ f = 0) :
    projectiveCycleHom (G.mapProjectiveResolution P) (G.map f)
        (by
          change G.map (P.complex.d (n + 1) n) ≫ G.map f = 0
          rw [← G.map_comp, hf, G.map_zero]) =
      (mappedProjectiveCochainIso G P).inv ≫
        (projectiveCycleHom P f hf).map (G.mapHomologicalComplex (.up ℤ)) ≫
          ((G.mapCochainComplexSingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' := by
  have htransport (i j : ℤ) (h : i = j) :
      (Cochain.ofHom (mappedProjectiveCochainIso G P).inv).v i j
          (by simpa using h) ≫
        G.map (eqToHom (congrArg P.cochainComplex.X h.symm)) =
      (mappedProjectiveCochainIso G P).inv.f i := by
    subst j
    simp
  have hsingle (i : ℤ) (h : i = 0) :
      G.map (singleObjXSelf (.up ℤ) 0 Y).inv ≫
        G.map (eqToHom (congrArg ((CochainComplex.singleFunctor C 0).obj Y).X h.symm)) ≫
          ((singleMapHomologicalComplex G (.up ℤ) 0).hom.app Y).f i ≫
            eqToHom (congrArg ((CochainComplex.singleFunctor D 0).obj (G.obj Y)).X h) ≫
              (singleObjXSelf (.up ℤ) 0 (G.obj Y)).hom = 𝟙 _ := by
    subst i
    simp [Category.assoc, ← G.map_comp]
  apply Cocycle.equivHomShift.injective
  apply Subtype.ext
  apply (Cochain.toSingleEquiv (show -(n : ℤ) + n = 0 by omega)).injective
  simp only [Cochain.toSingleEquiv, Cochain.toSingleMk, Cochain.single,
    HomologicalComplex.XIsoOfEq, eqToIso.inv, eqToIso.hom, Category.assoc,
    projectiveCycleHom, Nat.cast_add, Nat.cast_one,
    Cocycle.equivHomShift_symm_apply, Cocycle.equivHomShift_apply,
    Cocycle.ofHom_homOf_eq_self, Cocycle.rightUnshift_coe, Cochain.rightUnshift,
    shiftFunctor_obj_X', Cocycle.rightShift_coe, Cochain.rightShift,
    Cocycle.toSingleMk_coe, Cochain.mk_v, shiftFunctor_obj_X,
    shiftFunctorObjXIso, eqToHom_trans, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    neg_add_cancel, and_self, ↓reduceDIte, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.mapCochainComplexSingleFunctor,
    ShiftedHom.map, Cocycle.ofHom_coe, Cochain.ofHom_comp, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Functor.mapHomologicalComplex_map_f,
    Cocycle.homOf_f, add_zero, Functor.map_dite, Functor.map_comp, Functor.map_zero,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, shiftFunctor_map_f',
    ]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% htransport (-(n : ℤ)) (-(n : ℤ) + 0) (add_zero _).symm]
  rw [hsingle (-(n : ℤ) + 0 + n) (by omega), Category.comp_id]
  simpa only [Category.assoc] using
    ((mappedProjectiveCochainIso_inv_term G P n) =≫ G.map f).symm

omit [HasExt C] [HasExt D] in
private theorem mappedProjectiveDerivedAugmentation
    [HasDerivedCategory C] [HasDerivedCategory D] :
    (G.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        G.mapDerivedCategory.map (inv (DerivedCategory.Q.map P.π')) ≫
        G.mapDerivedCategoryFactors.hom.app P.cochainComplex =
      inv (DerivedCategory.Q.map (G.mapProjectiveResolution P).π') ≫
        DerivedCategory.Q.map (mappedProjectiveCochainIso G P).inv := by
  apply (cancel_mono (DerivedCategory.Q.map (mappedProjectiveCochainIso G P).hom)).mp
  apply (cancel_mono (DerivedCategory.Q.map (G.mapProjectiveResolution P).π')).mp
  have he : DerivedCategory.Q.map (mappedProjectiveCochainIso G P).inv ≫
      DerivedCategory.Q.map (mappedProjectiveCochainIso G P).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  simp only [Category.assoc, reassoc_of% he, IsIso.inv_hom_id]
  rw [← Functor.map_comp, mappedProjectiveCochainIso_augmentation, Functor.map_comp]
  rw [← G.mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [G.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  exact DerivedCategory.Q.map_id _

omit [HasExt C] [HasExt D] [G.PreservesProjectiveObjects] in
private theorem mappedProjectiveDerivedCycle [HasDerivedCategory C] [HasDerivedCategory D]
    {n : ℕ} (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n + 1) n ≫ f = 0) :
    ((projectiveCycleHom P f hf).map DerivedCategory.Q).map G.mapDerivedCategory ≫
        ((G.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' =
      G.mapDerivedCategoryFactors.hom.app P.cochainComplex ≫
        ((projectiveCycleHom P f hf).map (G.mapHomologicalComplex (.up ℤ))).map
          DerivedCategory.Q ≫
        (DerivedCategory.Q.map ((G.mapCochainComplexSingleFunctor 0).hom.app Y))⟦(n : ℤ)⟧' := by
  have h := ShiftedHom.map_naturality (projectiveCycleHom P f hf)
    G.mapDerivedCategoryFactors.hom
  simp only [ShiftedHom.comp_map, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  rw [← Category.assoc, ← h]
  simp only [Category.assoc]
  rw [← G.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
  rw [← (CategoryTheory.shiftFunctor (DerivedCategory D) (n : ℤ)).map_comp,
    Iso.hom_inv_id_app_assoc]

private theorem projectiveExtMk_mapExactFunctor {n : ℕ}
    (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n + 1) n ≫ f = 0) :
    (P.extMk f (n + 1) rfl hf : Ext.{w} X Y n).mapExactFunctor G =
      ((G.mapProjectiveResolution P).extMk (G.map f) (n + 1) rfl
        (by
          change G.map (P.complex.d (n + 1) n) ≫ G.map f = 0
          rw [← G.map_comp, hf, G.map_zero]) : Ext.{z} (G.obj X) (G.obj Y) n) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  apply Ext.ext
  rw [Ext.mapExactFunctor_hom, projectiveExtMk_hom, projectiveExtMk_hom]
  rw [← ShiftedHom.mk₀_comp (0 : ℤ) rfl (inv (DerivedCategory.Q.map P.π'))
      ((projectiveCycleHom P f hf).map DerivedCategory.Q),
    ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp]
  simp only [Category.assoc]
  rw [mappedProjectiveDerivedCycle]
  have hc := congrArg (fun x => x.map DerivedCategory.Q) (mappedProjectiveCycleHom G P f hf)
  rw [← ShiftedHom.mk₀_comp (0 : ℤ) rfl (mappedProjectiveCochainIso G P).inv,
    ← ShiftedHom.comp_mk₀
      ((projectiveCycleHom P f hf).map (G.mapHomologicalComplex (.up ℤ)))
      (0 : ℤ) rfl ((G.mapCochainComplexSingleFunctor 0).hom.app Y),
    ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at hc
  rw [hc]
  simpa only [Category.assoc] using
    ((mappedProjectiveDerivedAugmentation G P) =≫
      ((projectiveCycleHom P f hf).map (G.mapHomologicalComplex (.up ℤ))).map
        DerivedCategory.Q) =≫
      (DerivedCategory.Q.map
        ((G.mapCochainComplexSingleFunctor 0).hom.app Y))⟦(n : ℤ)⟧'

end ProjectiveClass

/-- The actual scalar-extension quotient isomorphism, through the native
algebra tensor/quotient and original ideal-image comparisons. -/
def scalarExtensionQuotientIso [Algebra R S] (s : List R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (R ⧸ Ideal.ofList s)) ≅
      ModuleCat.of S (S ⧸ Ideal.ofList (s.map (algebraMap R S))) :=
  ModuleCat.extendScalarsAlgebraObjIso R S _ ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (Ideal.ofList s)).symm.toLinearEquiv.toModuleIso ≪≫
    (Submodule.quotEquivOfEq _ _
      (congrArg (fun I : Ideal S => (I : Submodule S S))
        (Ideal.map_ofList (algebraMap R S) s))).toModuleIso

/-- The quotient comparison sends the original unit pure tensor to the original
image of that quotient representative. -/
@[simp] theorem scalarExtensionQuotientIso_one_tmul [Algebra R S] (s : List R) (r : R) :
    (scalarExtensionQuotientIso (S := S) s).hom
        ((1 : S) ⊗ₜ[R,algebraMap R S] (Ideal.Quotient.mk (Ideal.ofList s) r)) =
      Ideal.Quotient.mk (Ideal.ofList (s.map (algebraMap R S))) (algebraMap R S r) := by
  change (Submodule.quotEquivOfEq _ _
    (congrArg (fun I : Ideal S => (I : Submodule S S))
      (Ideal.map_ofList (algebraMap R S) s)))
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.ofList s)).symm
      ((ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R (R ⧸ Ideal.ofList s))).hom
        ((1 : S) ⊗ₜ[R,algebraMap R S] (Ideal.Quotient.mk (Ideal.ofList s) r)))) = _
  rw [ModuleCat.extendScalarsAlgebraObjIso_hom_tmul,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
    Submodule.quotEquivOfEq_mk]
  simp [Algebra.smul_def]

private abbrev scalarF [Algebra R S] : ModuleCat.{u} R ⥤ ModuleCat.{u} S :=
  ModuleCat.extendScalars (algebraMap R S)

section FlatClass
variable [Algebra R S] [Module.Flat R S]
local instance scalarFiniteLimits : PreservesFiniteLimits
    (ModuleCat.extendScalars (algebraMap R S) : ModuleCat.{u} R ⥤ ModuleCat.{u} S) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat (algebraMap R S)
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R S from inferInstance))
local instance scalarFiniteColimits : PreservesFiniteColimits
    (ModuleCat.extendScalars (algebraMap R S) : ModuleCat.{u} R ⥤ ModuleCat.{u} S) :=
  ModuleCat.extendScalars_preservesFiniteColimits_of_flat (algebraMap R S)
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R S from inferInstance))
local instance scalarProjectives :
    (ModuleCat.extendScalars (algebraMap R S) :
      ModuleCat.{u} R ⥤ ModuleCat.{u} S).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj.{u} (algebraMap R S))

private theorem idealAugmentation_zero (s : List R) (x : (chainComplex s).X 0) :
    (idealAugmentation s).f 0 x =
      Ideal.Quotient.mk (Ideal.ofList s) ((zeroComponentIso s).hom x) := by
  simp only [idealAugmentation, HomologicalComplex.comp_f, augmentation_f_zero,
    ChainComplex.single₀_map_f_zero, ModuleCat.comp_apply]
  rfl

private theorem scalarAugmentation (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    let hsA := hs.of_flat (S := S)
    let P := (scalarF (R := R) (S := S)).mapProjectiveResolution (finiteProjectiveResolution s hs)
    let Q := finiteProjectiveResolution (s.map (algebraMap R S)) hsA
    (ringExtendIso (R := R) (S := S) s).hom ≫ Q.π =
      P.π ≫ (ChainComplex.single₀ (ModuleCat S)).map
        (scalarExtensionQuotientIso (S := S) s).hom := by
  intro hsA P Q
  apply HomologicalComplex.to_single_hom_ext
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  have hz := LinearMap.congr_fun
    (congrArg (fun k => k.hom) (ringExtendIso_zero (R := R) (S := S) s))
      ((1 : S) ⊗ₜ[R,algebraMap R S] x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  change (zeroComponentIso (s.map (algebraMap R S))).hom
      ((ringExtendIso (R := R) (S := S) s).hom.f 0
        ((1 : S) ⊗ₜ[R,algebraMap R S] x)) =
    (scalarRingUnitIso (R := R) (S := S)).hom
      ((ModuleCat.extendScalars (algebraMap R S)).map (zeroComponentIso s).hom
        ((1 : S) ⊗ₜ[R,algebraMap R S] x)) at hz
  rw [ModuleCat.ExtendScalars.map_tmul, scalarRingUnitIso_tmul, one_mul] at hz
  change (zeroComponentIso (s.map (algebraMap R S))).hom
      ((ringExtendIso (R := R) (S := S) s).hom.f 0 ((1 : S) ⊗ₜ[R,(algebraMap R S)] x)) =
    algebraMap R S ((zeroComponentIso s).hom x) at hz
  change (idealAugmentation (s.map (algebraMap R S))).f 0
      ((ringExtendIso (R := R) (S := S) s).hom.f 0 ((1 : S) ⊗ₜ[R,(algebraMap R S)] x)) = _
  rw [idealAugmentation_zero, hz]
  change Ideal.Quotient.mk (Ideal.ofList (s.map (algebraMap R S)))
      (algebraMap R S ((zeroComponentIso s).hom x)) =
    (scalarExtensionQuotientIso (S := S) s).hom
      ((1 : S) ⊗ₜ[R,algebraMap R S] ((idealAugmentation s).f 0 x))
  rw [idealAugmentation_zero, scalarExtensionQuotientIso_one_tmul]

private def scalarResolutionHom (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    (finiteProjectiveResolution (s.map (algebraMap R S)) (hs.of_flat (S := S))).Hom
      ((scalarF (R := R) (S := S)).mapProjectiveResolution (finiteProjectiveResolution s hs))
      (scalarExtensionQuotientIso (S := S) s).inv where
  hom := (ringExtendIso (R := R) (S := S) s).inv
  hom_f_zero_comp_π_f_zero := by
    have h := congrArg (fun k => (ringExtendIso (R := R) (S := S) s).inv ≫ k ≫
      (ChainComplex.single₀ (ModuleCat S)).map (scalarExtensionQuotientIso (S := S) s).inv)
      (scalarAugmentation (S := S) s hs)
    have h' := congrArg (fun k => k.f 0) h
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id,
        HomologicalComplex.comp_f] using h'.symm

omit [Module.Flat R S] in
private theorem scalarRingUnitIso_map_span (r : R) :
    (scalarF (R := R) (S := S)).map (ModuleCat.ofHom (LinearMap.toSpanSingleton R R r)) ≫
        (scalarRingUnitIso (R := R) (S := S)).hom =
      (scalarRingUnitIso (R := R) (S := S)).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton S S ((algebraMap R S) r)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (scalarRingUnitIso (R := R) (S := S)).hom
    ((ModuleCat.extendScalars (algebraMap R S)).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R R r))
        ((1 : S) ⊗ₜ[R,algebraMap R S] x)) =
    (scalarRingUnitIso (R := R) (S := S)).hom ((1 : S) ⊗ₜ[R,algebraMap R S] x) *
      algebraMap R S r
  rw [ModuleCat.ExtendScalars.map_tmul, scalarRingUnitIso_tmul,
    scalarRingUnitIso_tmul]
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, smul_eq_mul,
    one_mul, map_mul]

private theorem scalarClass_cast [HasExt.{z} (ModuleCat.{u} S)]
    (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s) (r : R) :
    cast (congrArg (fun n => Ext.{z}
      (ModuleCat.of S (S ⧸ Ideal.ofList (s.map (algebraMap R S)))) (ModuleCat.of S S) n)
      (List.length_map (as := s) (algebraMap R S)))
        (topExtClass (s.map (algebraMap R S)) (hs.of_flat (S := S))
      (ModuleCat.of S S) ((algebraMap R S) r)) =
    (finiteProjectiveResolution (s.map (algebraMap R S)) (hs.of_flat (S := S))).extMk
      ((scalarTopFrame (s.map (algebraMap R S)) s.length (List.length_map (as := s) _).symm).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton S S ((algebraMap R S) r))) (s.length + 1) rfl
        ((isZero_X (s.map (algebraMap R S)) (s.length + 1) (by simp)).eq_of_src _ _) := by
  have general_cast (t : List S) (ht : RingTheory.Sequence.IsWeaklyRegular S t)
      (n : ℕ) (h : t.length = n) (z : S) :
      cast (congrArg (fun k => Ext.{z}
        (ModuleCat.of S (S ⧸ Ideal.ofList t)) (ModuleCat.of S S) k) h)
          (topExtClass t ht (ModuleCat.of S S) z) =
        (finiteProjectiveResolution t ht).extMk
          ((scalarTopFrame t n h.symm).hom ≫
            ModuleCat.ofHom (LinearMap.toSpanSingleton S S z)) (n + 1) rfl
          ((isZero_X t (n + 1) (by omega)).eq_of_src _ _) := by
    subst n
    rfl
  exact general_cast (s.map (algebraMap R S)) (hs.of_flat (S := S)) s.length
    (List.length_map (as := s) (algebraMap R S)) ((algebraMap R S) r)

private theorem scalarClassEquation [HasExt.{w} (ModuleCat.{u} R)]
    [HasExt.{z} (ModuleCat.{u} S)]
    (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s) (r : R) :
    ((Ext.mk₀ (scalarExtensionQuotientIso (S := S) s).inv).comp
        ((topExtClass s hs (ModuleCat.of R R) r).mapExactFunctor (scalarF (R := R) (S := S)))
          (zero_add s.length)).comp
      (Ext.mk₀ (scalarRingUnitIso (R := R) (S := S)).hom) (add_zero s.length) =
      cast (congrArg (fun n => Ext.{z}
        (ModuleCat.of S (S ⧸ Ideal.ofList (s.map (algebraMap R S)))) (ModuleCat.of S S) n)
        (List.length_map (as := s) (algebraMap R S)))
          (topExtClass (s.map (algebraMap R S)) (hs.of_flat (S := S))
      (ModuleCat.of S S) ((algebraMap R S) r)) := by
  rw [topExtClass_apply, projectiveExtMk_mapExactFunctor]
  rw [ProjectiveResolution.mk₀_comp_extMk (φ := scalarResolutionHom (S := S) s hs),
    ProjectiveResolution.extMk_comp_mk₀, scalarClass_cast (S := S) s hs r]
  congr 1
  change ((ringExtendIso (R := R) (S := S) s).inv.f s.length ≫
    (scalarF (R := R) (S := S)).map ((topComponentIso s).hom ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton R R r))) ≫
        (scalarRingUnitIso (R := R) (S := S)).hom = _
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [scalarRingUnitIso_map_span]
  simpa only [Category.assoc] using
    (ringExtendIso_inv_top (R := R) (S := S) s) =≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton S S (algebraMap R S r))

end FlatClass

/-- Actual exact scalar extension of an original top Koszul class for a flat
ring map. Both source and coefficient are normalized by their native quotient
and ring-unit isomorphisms; only the same-list length equality is transported. -/
theorem topExtClass_map_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} S)]
    (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s) (r : R) :
    letI := φ.toAlgebra
    let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars φ
    letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hφ
    letI : PreservesFiniteLimits F :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat φ hφ
    letI : PreservesFiniteColimits F :=
      ModuleCat.extendScalars_preservesFiniteColimits_of_flat φ hφ
    let ε := ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R R) ≪≫
      (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso
    ((Ext.mk₀ (scalarExtensionQuotientIso (S := S) s).inv).comp
        ((topExtClass s hs (ModuleCat.of R R) r).mapExactFunctor F) (zero_add s.length)).comp
      (Ext.mk₀ ε.hom) (add_zero s.length) =
      cast (congrArg (fun n => Ext.{z}
        (ModuleCat.of S (S ⧸ Ideal.ofList (s.map φ))) (ModuleCat.of S S) n)
        (List.length_map (as := s) φ))
          (topExtClass (s.map φ) (hs.of_flat (S := S)) (ModuleCat.of S S) (φ r)) := by
  let := φ.toAlgebra
  let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hφ
  exact scalarClassEquation (S := S) s hs r

/-- Principal localization preserves the original same-list top class through
the actual exact scalar-extension map and native source/coefficient frames. -/
theorem topExtClass_map_principal
    {R : Type u} [CommRing R] (a : R)
    [HasExt.{w} (ModuleCat.{u} R)]
    [HasExt.{z} (ModuleCat.{u} (Localization.Away a))]
    (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s) (r : R) :
    let S := Localization.Away a
    let φ := algebraMap R S
    let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars φ
    letI : Module.Flat R S := IsLocalization.flat (Localization.Away a) (Submonoid.powers a)
    letI : PreservesFiniteLimits F := ModuleCat.extendScalars_preservesFiniteLimits_of_flat φ
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers a)))
    letI : PreservesFiniteColimits F := ModuleCat.extendScalars_preservesFiniteColimits_of_flat φ
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away a) (Submonoid.powers a)))
    let ε := ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R R) ≪≫
      (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso
    ((Ext.mk₀ (scalarExtensionQuotientIso (S := S) s).inv).comp
        ((topExtClass s hs (ModuleCat.of R R) r).mapExactFunctor F) (zero_add s.length)).comp
      (Ext.mk₀ ε.hom) (add_zero s.length) =
      cast (congrArg (fun n => Ext.{z}
        (ModuleCat.of S (S ⧸ Ideal.ofList (s.map φ))) (ModuleCat.of S S) n)
        (List.length_map (as := s) φ))
          (topExtClass (s.map φ) (hs.of_flat (S := S)) (ModuleCat.of S S) (φ r)) := by
  let : Module.Flat R (Localization.Away a) :=
    IsLocalization.flat (Localization.Away a) (Submonoid.powers a)
  exact scalarClassEquation (S := Localization.Away a) s hs r

end ChainComplex.Koszul
