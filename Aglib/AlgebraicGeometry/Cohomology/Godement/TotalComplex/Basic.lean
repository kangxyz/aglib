/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Resolution
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.DerivedPushforward
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Data.Int.Interval

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementComplex.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 326]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The integer-indexed Godement resolution and its complex totalization

Extend the actual cokernel resolution by zero in negative degrees, and then apply
that natural resolution to the terms of an original cochain complex.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- Extension by zero of the actual Godement resolution into integer degrees. -/
def godementResolutionInt (X : Scheme.{u}) : X.Modules ⥤ CochainComplex X.Modules ℤ :=
  godementResolution X ⋙ ComplexShape.embeddingUpNat.extendFunctor X.Modules

instance godementResolutionInt_additive (X : Scheme.{u}) :
    (godementResolutionInt X).Additive := by dsimp [godementResolutionInt]; infer_instance

instance godementResolutionInt_isStrictlyGE (X : Scheme.{u}) (M : X.Modules) :
    ((godementResolutionInt X).obj M).IsStrictlyGE 0 := by
  dsimp [godementResolutionInt]
  infer_instance

/-- The nonnegative term is its actual original Godement term. -/
def godementResolutionIntXIso (X : Scheme.{u}) (M : X.Modules) (n : ℤ) (k : ℕ) (h : k = n) :
    ((godementResolutionInt X).obj M).X n ≅ ((godementResolution X).obj M).X k :=
  HomologicalComplex.extendXIso _ _ h

/-- The actual augmentation to the integer-indexed Godement complex. -/
def godementResolutionIntUnit (X : Scheme.{u}) :
    CochainComplex.singleFunctor X.Modules 0 ⟶ godementResolutionInt X where
  app M := (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 (by simp)).inv ≫
    (ComplexShape.embeddingUpNat.extendFunctor X.Modules).map
      ((godementResolutionUnit X).app M)
  naturality {M N} f := by
    apply HomologicalComplex.from_single_hom_ext
    dsimp only [godementResolutionInt, Functor.comp_map, ComplexShape.Embedding.extendFunctor]
    simp only [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f]
    rw [HomologicalComplex.extendMap_f ((godementResolutionUnit X).app N)
      ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp),
      HomologicalComplex.extendMap_f ((godementResolutionUnit X).app M)
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp),
      HomologicalComplex.extendMap_f ((godementResolution X).map f)
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp)]
    simp [CochainComplex.singleFunctor, HomologicalComplex.single,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      godementResolutionUnit_f_zero, godementResolution_map_f, godementIterate,
      ← (godementFirstProductUnit X).naturality f]

/-- Extension by zero retains the actual augmentation quasi-isomorphism. -/
instance godementResolutionIntUnit_quasiIso (X : Scheme.{u}) (M : X.Modules) :
    QuasiIso ((godementResolutionIntUnit X).app M) := by
  dsimp [godementResolutionIntUnit]
  infer_instance

/-- The actual degreewise resolution bicomplex of an original integer cochain complex. -/
def godementBicomplex (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ HomologicalComplex₂ X.Modules (.up ℤ) (.up ℤ) :=
  (godementResolutionInt X).mapHomologicalComplex (.up ℤ)

/-- The original total complex of the degreewise Godement bicomplex. -/
def godementTotal (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  godementBicomplex X ⋙ HomologicalComplex₂.totalFunctor X.Modules (.up ℤ) (.up ℤ) (.up ℤ)


/-- Every original zero module sheaf is flasque. -/
theorem godement_isFlasque_of_isZero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M) :
    TopCat.Presheaf.IsFlasque M.presheaf where
  epi {U V} k := (AddCommGrpCat.epi_iff_surjective _).mpr (by
    intro z
    refine ⟨0, ?_⟩
    have hz : z = 0 := congrArg (fun f : M ⟶ M => f.app V.unop z)
      (hM.eq_of_src (𝟙 M) 0)
    simpa only [map_zero] using hz.symm)

/-- Extension by zero preserves flasqueness of every actual resolution term. -/
instance godementResolutionInt_isFlasque (X : Scheme.{u}) (M : X.Modules) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((godementResolutionInt X).obj M).X n).presheaf := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact flasque_of_iso (godementResolutionIntXIso X M _ k rfl).symm
  · exact godement_isFlasque_of_isZero _
      (CochainComplex.isZero_of_isStrictlyGE _ 0 n (by omega))

/-- Applying the actual integer resolution to a zero sheaf gives zero in every degree. -/
theorem godementResolutionInt_isZero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M) (n : ℤ) :
    IsZero (((godementResolutionInt X).obj M).X n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact (godementResolution_isZero M hM k).of_iso (godementResolutionIntXIso X M _ k rfl)
  · exact CochainComplex.isZero_of_isStrictlyGE _ 0 n (by omega)

/-- Every actual finite biproduct of flasque module sheaves is flasque. -/
theorem godement_finiteBiproduct_isFlasque {X : Scheme.{u}} {I : Type} [Finite I]
    (M : I → X.Modules) (hM : ∀ i, TopCat.Presheaf.IsFlasque (M i).presheaf) :
    TopCat.Presheaf.IsFlasque (⨁ M).presheaf where
  epi {U V} k := (AddCommGrpCat.epi_iff_surjective _).mpr (by
    classical
    let := Fintype.ofFinite I
    intro z
    have hlift : ∀ i, ∃ s : (M i).presheaf.obj U,
        (M i).presheaf.map k s = (biproduct.π M i).app V.unop z := by
      intro i
      let := hM i
      exact (AddCommGrpCat.epi_iff_surjective _).mp (TopCat.Presheaf.IsFlasque.epi k) _
    choose s hs using hlift
    refine ⟨∑ i, (biproduct.ι M i).app U.unop (s i), ?_⟩
    rw [map_sum]
    have hn (i : I) : (biproduct.ι M i).app V.unop ((M i).presheaf.map k (s i)) =
        (⨁ M).presheaf.map k ((biproduct.ι M i).app U.unop (s i)) :=
      ConcreteCategory.congr_hom ((biproduct.ι M i).mapPresheaf.naturality k) (s i)
    change ∑ i, (⨁ M).presheaf.map k ((biproduct.ι M i).app U.unop (s i)) = z
    have hcoord (i : I) : (⨁ M).presheaf.map k ((biproduct.ι M i).app U.unop (s i)) =
        (biproduct.ι M i).app V.unop ((biproduct.π M i).app V.unop z) := by
      rw [← hn i, hs i]
    simp_rw [hcoord]
    have htotal' : ∑ i, biproduct.π M i ≫ biproduct.ι M i = 𝟙 (⨁ M) := biproduct.total
    have htotal := congrArg (fun f : (⨁ M) ⟶ ⨁ M =>
      (moduleSectionEvaluation X V.unop).map f z) htotal'
    rw [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id] at htotal
    simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
      ModuleCat.comp_apply, ModuleCat.id_apply] at htotal
    exact htotal)

/-- The finite diagonal keeping the original horizontal indices. -/
abbrev GodementFiniteDegree (a n : ℤ) := ↥(Finset.Icc a n)

/-- The actual finite diagonal biproduct for a complex with lower bound `a`. -/
def godementFiniteDiagonal {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (a n : ℤ) :
    X.Modules :=
  ⨁ fun p : GodementFiniteDegree a n => ((godementResolutionInt X).obj (K.X p.val)).X (n - p.val)

/-- The actual total summands outside the finite diagonal are zero. -/
theorem godementBicomplex_isZero_offDiagonal {X : Scheme.{u}}
    (K : CochainComplex X.Modules ℤ) (a n p q : ℤ)
    (hK : ∀ i, i < a → IsZero (K.X i)) (hpq : p + q = n)
    (h : ¬ (a ≤ p ∧ p ≤ n)) : IsZero (((godementBicomplex X).obj K).X p |>.X q) := by
  by_cases hp : a ≤ p
  · have hq : q < 0 := by omega
    exact CochainComplex.isZero_of_isStrictlyGE ((godementResolutionInt X).obj (K.X p)) 0 q hq
  · exact godementResolutionInt_isZero (K.X p) (hK p (by omega)) q

/-- The original total complex is strictly bounded below by the same bound as its source. -/
theorem godementTotal_isStrictlyGE {X : Scheme.{u}}
    (K : CochainComplex X.Modules ℤ) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    ((godementTotal X).obj K).IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  have hpq' : p + q = n := hpq
  have hz := godementBicomplex_isZero_offDiagonal K a n p q hK hpq' (by omega)
  exact hz.eq_of_src _ _


/-- The map from the original total sheaf to its finite diagonal, discarding only zero terms. -/
def godementTotalToFinite {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (a n : ℤ) :
    ((godementTotal X).obj K).X n ⟶ godementFiniteDiagonal K a n :=
  ((godementBicomplex X).obj K).totalDesc (fun p q hpq =>
    if hp : p ∈ Finset.Icc a n then
      eqToHom (by
        have h : p + q = n := hpq
        have hq : q = n - p := by omega
        rw [hq]
        rfl) ≫ biproduct.ι _ ⟨p, hp⟩
    else 0)

/-- The finite diagonal's summands have their original inclusions in the actual total sheaf. -/
def godementFiniteToTotal {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (a n : ℤ) :
    godementFiniteDiagonal K a n ⟶ ((godementTotal X).obj K).X n :=
  biproduct.desc (fun p => ((godementBicomplex X).obj K).ιTotal (.up ℤ)
    p.val (n - p.val) n (by change p.val + (n - p.val) = n; omega))

/-- A lower-bounded complex's total degree is its actual finite diagonal biproduct. -/
def godementTotalFiniteIso {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (n : ℤ) :
    ((godementTotal X).obj K).X n ≅ godementFiniteDiagonal K a n where
  hom := godementTotalToFinite K a n
  inv := godementFiniteToTotal K a n
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    dsimp only [godementTotalToFinite]
    rw [HomologicalComplex₂.ι_totalDesc_assoc]
    by_cases hp : p ∈ Finset.Icc a n
    · rw [dite_eq_left hp]
      dsimp only [godementFiniteToTotal]
      rw [Category.assoc, biproduct.ι_desc]
      have hpq' : p + q = n := hpq
      obtain rfl : q = n - p := by omega
      simp only [eqToHom_refl, Category.id_comp]
      dsimp only [godementTotal, Functor.comp_obj, HomologicalComplex₂.totalFunctor]
      rw [Category.comp_id]
    · rw [dite_eq_right hp, zero_comp]
      have hpq' : p + q = n := hpq
      have hz := godementBicomplex_isZero_offDiagonal K a n p q hK hpq'
        (by simpa only [Finset.mem_Icc] using hp)
      exact hz.eq_of_src _ _
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro p
    dsimp only [godementFiniteToTotal]
    rw [← Category.assoc, biproduct.ι_desc]
    dsimp only [godementTotalToFinite]
    rw [HomologicalComplex₂.ι_totalDesc]
    simp only [dite_eq_left p.property, eqToHom_refl, Category.id_comp]
    dsimp only [godementFiniteDiagonal]
    rw [Category.comp_id]

/-- Every degree of the finite-diagonal totalization is flasque. -/
theorem godementTotal_isFlasque {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((godementTotal X).obj K).X n).presheaf := by
  let : TopCat.Presheaf.IsFlasque (godementFiniteDiagonal K a n).presheaf :=
    godement_finiteBiproduct_isFlasque _ (fun _ => godementResolutionInt_isFlasque _ _ _)
  exact flasque_of_iso (godementTotalFiniteIso K a hK n).symm


/-- The original degree-zero germ map into the integer-indexed resolution. -/
def godementIntGerm (X : Scheme.{u}) (M : X.Modules) :
    M ⟶ ((godementResolutionInt X).obj M).X 0 := ((godementResolutionIntUnit X).app M).f 0

@[reassoc]
theorem godementIntGerm_naturality {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    f ≫ godementIntGerm X N = godementIntGerm X M ≫ ((godementResolutionInt X).map f).f 0 := by
  have h := congrArg (fun φ => φ.f 0) ((godementResolutionIntUnit X).naturality f)
  simpa [godementIntGerm, CochainComplex.singleFunctor, HomologicalComplex.single,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq] using h

@[reassoc (attr := simp)]
theorem godementIntGerm_d (X : Scheme.{u}) (M : X.Modules) :
    godementIntGerm X M ≫ ((godementResolutionInt X).obj M).d 0 1 = 0 := by
  have h := ((godementResolutionIntUnit X).app M).comm 0 1
  simpa only [godementIntGerm, CochainComplex.singleFunctor_obj_d, zero_comp] using h

/-- The horizontal differential in the zero resolution row is the actual resolved differential. -/
theorem godementBicomplex_d₁_zeroRow {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((godementBicomplex X).obj K).d₁ (.up ℤ) n 0 (n + 1) =
      ((godementResolutionInt X).map (K.d n (n + 1))).f 0 ≫
        ((godementBicomplex X).obj K).ιTotal (.up ℤ) (n + 1) 0 (n + 1)
          (by change n + 1 + 0 = n + 1; omega) := by
  rw [HomologicalComplex₂.d₁_eq _ (.up ℤ)
    (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) 0 (n + 1)
    (by change n + 1 + 0 = n + 1; omega)]
  change (1 : ℤˣ) • _ = _
  rw [one_smul]
  rfl

/-- The actual augmentation annihilates the vertical total differential. -/
theorem godementBicomplex_germ_d₂ {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    godementIntGerm X (K.X n) ≫ ((godementBicomplex X).obj K).d₂ (.up ℤ) n 0 (n + 1) = 0 := by
  rw [HomologicalComplex₂.d₂_eq _ (.up ℤ) n
    (show (ComplexShape.up ℤ).Rel (0 : ℤ) 1 from rfl) (n + 1)
    (by change n + 1 = n + 1; rfl), Linear.comp_units_smul]
  change _ • (godementIntGerm X (K.X n) ≫
    (((godementResolutionInt X).obj (K.X n)).d 0 1 ≫ _)) = 0
  rw [← Category.assoc, godementIntGerm_d, zero_comp, smul_zero]

/-- The actual natural augmentation of an original complex into its Godement totalization. -/
def godementTotalUnit (X : Scheme.{u}) : 𝟭 (CochainComplex X.Modules ℤ) ⟶ godementTotal X where
  app K :=
    { f n := godementIntGerm X (K.X n) ≫ ((godementBicomplex X).obj K).ιTotal (.up ℤ)
        n 0 n (by change n + 0 = n; omega)
      comm' n m h := by
        obtain rfl : n + 1 = m := h
        dsimp only [godementTotal, Functor.comp_obj, HomologicalComplex₂.totalFunctor]
        rw [Category.assoc, HomologicalComplex₂.total_d, Preadditive.comp_add,
          HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
          Preadditive.comp_add, godementBicomplex_d₁_zeroRow,
          godementBicomplex_germ_d₂, add_zero, ← Category.assoc]
        dsimp only [godementBicomplex, CategoryTheory.Functor.mapHomologicalComplex,
          CategoryTheory.Functor.id_obj]
        rw [← godementIntGerm_naturality, Category.assoc] }
  naturality {K L} f := by
    ext1 n
    dsimp only [Functor.id_map, HomologicalComplex.comp_f, godementTotal,
      Functor.comp_map, HomologicalComplex₂.totalFunctor]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
    dsimp only [godementBicomplex, CategoryTheory.Functor.mapHomologicalComplex]
    change f.f n ≫ godementIntGerm X (L.X n) ≫ _ =
      (godementIntGerm X (K.X n) ≫ ((godementResolutionInt X).map (f.f n)).f 0) ≫ _
    rw [← godementIntGerm_naturality, Category.assoc]

/-- The original totalization restricts to the actual category of lower-bounded complexes. -/
def godementTotalPlus (X : Scheme.{u}) :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  ObjectProperty.lift _ (CochainComplex.Plus.ι X.Modules ⋙ godementTotal X) (fun K => by
    obtain ⟨a, ha⟩ := K.property
    let := ha
    exact ⟨a, godementTotal_isStrictlyGE K.obj a
      (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)⟩)

/-- Every actual Godement totalization computes its own installed derived direct image.
Comparison with the source complex additionally needs the total augmentation quasi-isomorphism. -/
theorem godementTotalPlus_derivedPushforwardUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex.Plus X.Modules) :
    IsIso ((derivedPushforwardPlusUnit f).app ((godementTotalPlus X).obj K)) := by
  obtain ⟨a, ha⟩ := K.property
  let := ha
  exact isIso_derivedPushforwardPlusUnit_of_flasque f _ (fun n =>
    godementTotal_isFlasque K.obj a
      (fun i hi => CochainComplex.isZero_of_isStrictlyGE K.obj a i hi) n)

end AlgebraicGeometry.Scheme.Modules.Godement
