/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.Structural
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.GlobalSectionsComposition.SingleUnit
public import Aglib.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.AcyclicSingle

/-!
# The original counit and source action in the chosen-embedding trace

The source is the actual Hom into the original closed right-adjoint object.
No concentration or identification with sections of a canonical module is used.
The coefficient remains the literal top-differential coefficient functor at N.
The native source action and a unit square give the coinduced coefficient law.
The original section restriction and pushforward comparisons transport this
map to actual module-valued derived sections. Their original units identify
the resulting native coinduced trace with Phi0 after restriction of eta_A.
This source-local equation precedes concentration and makes no assertion
about embedding-independent proper traces or Grauert--Riemenschneider vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Functor HomologicalComplex Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u v w dR dA u' v' w' u'' v'' w''

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit

private theorem unit_square_paste {C : Type*} [Category* C]
    {U V W : C} (η : U ⟶ V) (m : U ⟶ U) (c : V ⟶ V) (φ : V ⟶ W)
    (h : m ≫ η = η ≫ c) : η ≫ c ≫ φ = m ≫ η ≫ φ := by
  calc
    _ = (η ≫ c) ≫ φ := (Category.assoc _ _ _).symm
    _ = (m ≫ η) ≫ φ := congrArg (fun f => f ≫ φ) h.symm
    _ = _ := Category.assoc _ _ _

private theorem map_source_scalar_square
    {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    {A : Type*} [CommRing A] [Linear A C]
    (F : C ⥤ D) {U V : C} (η : U ⟶ V) (a : A) :
    F.map (a • 𝟙 U) ≫ F.map η = F.map η ≫ F.map (a • 𝟙 V) := by
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

private theorem unit_comparison_paste {C : Type*} [Category* C]
    {U V W B L D E T : C}
    (c : U ⟶ V) (t : V ⟶ L) (e : L ⟶ T) (s : U ⟶ W)
    (b : W ⟶ B) (v : V ⟶ B) (d : B ⟶ D) (d₀ : W ⟶ E)
    (f : E ⟶ D) (g : D ⟶ T) (fg : E ⟶ T)
    (ht : t ≫ e = v ≫ d ≫ g) (hc : c ≫ v = s ≫ b)
    (hd : b ≫ d = d₀ ≫ f) (hfg : fg = f ≫ g) :
    (c ≫ t) ≫ e = s ≫ d₀ ≫ fg := by
  rw [Category.assoc, ht, ← Category.assoc c v, hc]
  rw [Category.assoc s b, ← Category.assoc b d, hd]
  simp only [hfg, Category.assoc]

private theorem mapped_iso_unit {C D : Type*} [Category* C] [Category* D]
    (Q : C ⥤ D) {X Y : C} (e : X ≅ Y) {Z : D}
    (u : Q.obj X ⟶ Z) (t : Z ⟶ Q.obj Y) (h : u ≫ t = Q.map e.hom) :
    (Q.map e.inv ≫ u) ≫ t = 𝟙 (Q.obj Y) := by
  rw [Category.assoc, h, ← Q.map_comp, e.inv_hom_id, Q.map_id]

private theorem comp_iso_inv_of_comp_hom {C : Type*} [Category* C]
    {U V W : C} (e : V ≅ W) (u : U ⟶ V) (v : U ⟶ W)
    (h : u ≫ e.hom = v) : v ≫ e.inv = u := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem comp_eq_iso_inv {C : Type*} [Category* C]
    {U V W : C} (e : W ≅ U) (d : U ⟶ V) (t : V ⟶ W)
    (h : d ≫ (t ≫ e.hom) = 𝟙 U) : d ≫ t = e.inv := by
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, h, e.inv_hom_id]

private theorem unit_iso_inv_paste {C : Type*} [Category* C]
    {U V W L T : C} (e : L ≅ T) (u : U ⟶ L)
    (s : U ⟶ V) (d : V ⟶ W) (η : W ⟶ T)
    (h : u ≫ e.hom = s ≫ d ≫ η) : s ≫ (d ≫ η ≫ e.inv) = u := by
  simpa only [Category.assoc] using
    comp_iso_inv_of_comp_hom e u (s ≫ d ≫ η) h

private theorem mapped_single_unit {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {U V : C} {W : D} (e : W ≅ F.obj U)
    (d : U ⟶ V) (t : F.obj V ⟶ W) (t₀ : V ⟶ U)
    (ht : t ≫ e.hom = F.map t₀) (hd : d ≫ t₀ = 𝟙 U) :
    F.map d ≫ t = e.inv := by
  apply comp_eq_iso_inv e (F.map d) t
  rw [ht, ← F.map_comp, hd, F.map_id]

private theorem map_unit_factor {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {U V W X : C} {L T : D}
    (d : U ⟶ V) (η : V ⟶ W) (v : W ⟶ X)
    (e : F.obj U ⟶ L) (f : L ⟶ T) (t : T ⟶ F.obj W)
    (h : F.map d ≫ F.map η = e ≫ f ≫ t) :
    F.map (d ≫ η ≫ v) = e ≫ f ≫ (t ≫ F.map v) := by
  rw [F.map_comp, F.map_comp, ← Category.assoc, h]
  simp only [Category.assoc]

private theorem geometric_unit_paste {C D : Type*} [Category* C] [Category* D]
    (S : C ⥤ D) {U V W : C} {P Q L : D}
    (cX : U ⟶ V) (c : V ⟶ W) (cY : U ⟶ W)
    (u : S.obj V ⟶ P) (g : P ⟶ Q) (e : L ≅ Q) (v : S.obj W ⟶ L)
    (hc : cX ≫ c = cY) (hu : u ≫ g ≫ e.inv = S.map c ≫ v) :
    (S.map cX ≫ u) ≫ g = (S.map cY ≫ v) ≫ e.hom := by
  apply (cancel_mono e.inv).mp
  simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [hu, ← Category.assoc, ← S.map_comp, hc]

/-- The original chosen preimage under an additive fully faithful functor is additive. -/
def CategoryTheory.Functor.preimageAddHom
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] (X Y : C) :
    (F.obj X ⟶ F.obj Y) →+ (X ⟶ Y) where
  toFun := F.preimage
  map_zero' := by
    apply F.map_injective
    rw [F.map_preimage, F.map_zero]
  map_add' f g := by
    apply F.map_injective
    rw [F.map_preimage, F.map_add, F.map_preimage, F.map_preimage]

private theorem preimage_source_comp
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y Z : C} (m : X ⟶ Y) (f : F.obj Y ⟶ F.obj Z) (g : F.obj X ⟶ F.obj Z)
    (h : g = F.map m ≫ f) : F.preimage g = m ≫ F.preimage f := by
  apply F.map_injective
  rw [F.map_preimage, F.map_comp, F.map_preimage, h]

private theorem map_comp_eq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) : F.map a ≫ F.map b = F.map c := by
  rw [← F.map_comp, h]

private theorem append_comp_eq {C : Type*} [Category* C]
    {X Y Z T : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (d : Z ⟶ T)
    (h : a ≫ b = c) : a ≫ (b ≫ d) = c ≫ d := by
  rw [← Category.assoc, h]

private theorem coefficient_source_scalar_square
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {A : Type*} [CommRing A] [Linear A C] [Linear A D]
    (F : C ⥤ D) [F.Linear A] {M : D} {N : C} (φ : M ⟶ F.obj N) (a : A) :
    (a • 𝟙 M) ≫ φ = φ ≫ F.map (a • 𝟙 N) := by
  rw [F.map_smul, F.map_id, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Category.comp_id]

private theorem mapped_source_paste {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} {L N : D}
    (t : X ⟶ X) (f g : X ⟶ Y) (c : L ⟶ F.obj X) (d : F.obj Y ⟶ N)
    (b : L ⟶ L) (hf : g = t ≫ f) (hc : b ≫ c = c ≫ F.map t) :
    c ≫ F.map g ≫ d = b ≫ (c ≫ F.map f ≫ d) := by
  rw [hf, F.map_comp]
  calc
    _ = (c ≫ F.map t) ≫ F.map f ≫ d := by simp only [Category.assoc]
    _ = (b ≫ c) ≫ F.map f ≫ d := congrArg (fun k => k ≫ F.map f ≫ d) hc.symm
    _ = _ := by simp only [Category.assoc]

private theorem restricted_scalar_paste {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} {P Q : D} (η : X ⟶ Y) (b : X ⟶ X) (m : Y ⟶ Y)
    (d : P ⟶ F.obj X) (e : F.obj Y ⟶ Q) (b₀ : P ⟶ P) (r : Q ⟶ Q)
    (hd : b₀ ≫ d = d ≫ F.map b) (hη : b ≫ η = η ≫ m)
    (he : F.map m ≫ e = e ≫ r) :
    b₀ ≫ (d ≫ F.map η ≫ e) = (d ≫ F.map η ≫ e) ≫ r := by
  rw [← Category.assoc b₀ d, hd]
  calc
    _ = d ≫ F.map (b ≫ η) ≫ e := by simp only [F.map_comp, Category.assoc]
    _ = d ≫ F.map (η ≫ m) ≫ e := congrArg (fun k => d ≫ F.map k ≫ e) hη
    _ = d ≫ F.map η ≫ (F.map m ≫ e) := by simp only [F.map_comp, Category.assoc]
    _ = _ := by rw [he]; simp only [Category.assoc]

private theorem mapped_pairing_factor {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {U V W : C} {P Q : D} (η : U ⟶ V) (φ : V ⟶ W)
    (a : F.obj U ⟶ P) (b : P ⟶ Q) (c : Q ⟶ F.obj V)
    (h : F.map η = a ≫ b ≫ c) :
    F.map (η ≫ φ) = a ≫ b ≫ (c ≫ F.map φ) := by
  rw [F.map_comp, h]
  simp only [Category.assoc]

private theorem geometric_trace_paste {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y Z : C} {P Q T : D}
    (g : X ⟶ Y) (φ : Y ⟶ Z) (u : P ⟶ Q) (c : Q ⟶ F.obj Y)
    (v : P ⟶ F.obj X) (t : F.obj Z ⟶ T) (h : u ≫ c = v ≫ F.map g) :
    u ≫ (c ≫ F.map φ ≫ t) = v ≫ F.map (g ≫ φ) ≫ t := by
  rw [← Category.assoc u c, h, F.map_comp]
  simp only [Category.assoc]

namespace AlgebraicGeometry.Scheme.Cohomology

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ Y)

/-- The original inverse-adjunction arrow written through its actual single image and counit. -/
def closedEmbeddingCounitInput (Ω : X.Modules) (M : Z.Modules)
    (I : InjectiveResolution Ω) (q : ℕ)
    (s : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj Ω)))⟦(q : ℤ)⟧) :
    (DerivedCategory.singleFunctor X.Modules 0).obj ((pushforward i).obj M) ⟶
      ((DerivedCategory.singleFunctor X.Modules 0).obj Ω)⟦(q : ℤ)⟧ :=
  ((pushforward i).mapDerivedCategorySingleFunctor 0).inv.app M ≫
    ShiftedHom.map s (pushforward i).mapDerivedCategory ≫
      (Adjunction.injectiveResolutionDerivedCounit
        (closedImmersionRightAdjunction i) I)⟦(q : ℤ)⟧'

/-- This is precisely the inverse of the original supplied-resolution adjunction. -/
theorem closedEmbeddingCounitInput_eq (Ω : X.Modules) (M : Z.Modules)
    (I : InjectiveResolution Ω) (q : ℕ)
    (s : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj Ω)))⟦(q : ℤ)⟧) :
    closedEmbeddingCounitInput i Ω M I q s =
      ((closedImmersionRightAdjunction i).singleDerivedHomEquivOfInjectiveResolution
        M I (q : ℤ)).symm s :=
  (Adjunction.singleDerivedHomEquivOfInjectiveResolution_symm_eq_map_counit
    (closedImmersionRightAdjunction i) M I (q : ℤ) s).symm

variable (R : Type u) [CommRing R] (ι : Type u)
  (a : X ⟶ ProjectiveSpace R ι) (f : Y ⟶ Spec (.of R))
  (h : IsPullback a p (toSpec R ι) f) [Y.IsSeparated]

/-- The existing chosen-embedding Serre map is the original counit followed by
original derived pushforward and the installed shifted projective trace. -/
theorem relativeClosedEmbeddingSerreMap_apply_counit
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : Z.Modules) (q : ℕ)
    (I : InjectiveResolution ((relativeTopDifferentialCoefficientsFunctor p n).obj N))
    (s : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(q : ℤ)⟧) :
    relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q s =
      DerivedCategory.Plus.ι.map (relativeClosedEmbeddingPushforwardSingleIso i p M).hom ≫
        (Ext.homEquiv.symm (closedEmbeddingCounitInput i
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N) M I q s)).homPlus.map
            (derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι) ≫
          (relativeProjectiveTrace R ι a p f h n e N)⟦(q : ℤ)⟧' := by
  rw [relativeClosedEmbeddingSerreMap_apply i p R ι a f h n e N M q I,
    relativeProjectiveSerreMap_apply, closedEmbeddingCounitInput_eq]

/-- Degree-zero source naturality uses the original source morphism itself. -/
theorem relativeClosedEmbeddingSerreMap_precomp
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    {M M' : Z.Modules} (m : M ⟶ M') (q : ℕ)
    (s : (DerivedCategory.singleFunctor Z.Modules 0).obj M' ⟶
      (DerivedCategory.Plus.ι.obj ((derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(q : ℤ)⟧) :
    relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q
        ((DerivedCategory.singleFunctor Z.Modules 0).map m ≫ s) =
      (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor Z.Modules 0).map m) ≫
        relativeClosedEmbeddingSerreMap i p R ι a f h n e N M' q s := by
  have hm := relativeClosedEmbeddingSerreMap_comp i p R ι a f h n e N
    (Ext.mk₀ m) s (zero_add q)
  rw [Ext.mk₀_hom, Ext.homPlus_mk₀, ShiftedHom.mk₀_comp] at hm
  erw [ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp] at hm
  exact hm

/-- The actual native shift identification, from a degree-n single shifted by n to degree zero. -/
def relativeClosedEmbeddingTraceTargetIso (n : ℕ) (N : Y.Modules) :
    ((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N)⟦(n : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj N :=
  ((DerivedCategory.singleFunctors Y.Modules).shiftIso (n : ℤ) 0 n (by omega)).app N

/-- The exact original source of the degree-n chosen-embedding comparison. -/
abbrev relativeClosedEmbeddingUnitTraceSource (n : ℕ) (N : Y.Modules) (M : Z.Modules) :=
  (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
    (DerivedCategory.Plus.ι.obj ((derivedClosedImmersionRightAdjointPlus i).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(n : ℤ)⟧

/-- Normalize only the target shift of the original chosen-embedding Serre map. -/
def relativeClosedEmbeddingDegreeZeroSerreMap
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent] (M : Z.Modules) :
    relativeClosedEmbeddingUnitTraceSource i p n N M →+
      (DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (i ≫ p)).obj
        ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)) ⟶
        (DerivedCategory.singleFunctor Y.Modules 0).obj N) where
  toFun s := relativeClosedEmbeddingSerreMap i p R ι a f h n e N M n s ≫
    (relativeClosedEmbeddingTraceTargetIso n N).hom
  map_zero' := by rw [map_zero, Limits.zero_comp]
  map_add' s t := by rw [_root_.map_add, Preadditive.add_comp]

/-- Normalizing the target leaves original source naturality unchanged. -/
theorem relativeClosedEmbeddingDegreeZeroSerreMap_precomp
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    {M M' : Z.Modules} (m : M ⟶ M')
    (s : relativeClosedEmbeddingUnitTraceSource i p n N M') :
    relativeClosedEmbeddingDegreeZeroSerreMap i p R ι a f h n e N M
        ((DerivedCategory.singleFunctor Z.Modules 0).map m ≫ s) =
      (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor Z.Modules 0).map m) ≫
        relativeClosedEmbeddingDegreeZeroSerreMap i p R ι a f h n e N M' s := by
  change relativeClosedEmbeddingSerreMap i p R ι a f h n e N M n
      ((DerivedCategory.singleFunctor Z.Modules 0).map m ≫ s) ≫ _ = _
  rw [relativeClosedEmbeddingSerreMap_precomp]
  exact Category.assoc _ _ _

/-- The scalar acts on the source through its genuine structural action on Z.
There is no scalar map from this new ring into the base coefficient ring. -/
theorem relativeClosedEmbeddingDegreeZeroSerreMap_source_smul
    {A : Type u} [CommRing A] (α : A →+* Γ(Z, ⊤))
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : Z.Modules) (r : A) :
    letI := moduleCategoryLinearOfHom Z α
    ∀ s : relativeClosedEmbeddingUnitTraceSource i p n N M,
      relativeClosedEmbeddingDegreeZeroSerreMap i p R ι a f h n e N M (r • s) =
        (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι).map
            ((DerivedCategory.Plus.singleFunctor Z.Modules 0).map (r • 𝟙 M)) ≫
          relativeClosedEmbeddingDegreeZeroSerreMap i p R ι a f h n e N M s := by
  let := moduleCategoryLinearOfHom Z α
  intro s
  have hm : (DerivedCategory.singleFunctor Z.Modules 0).map (r • 𝟙 M) ≫ s = r • s := by
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
      Linear.smul_comp, Category.id_comp]
  rw [← hm]
  exact relativeClosedEmbeddingDegreeZeroSerreMap_precomp i p R ι a f h n e N (r • 𝟙 M) s

/-- Pasting any original source-unit square with the same Serre map gives the original unit law. -/
theorem relativeClosedEmbeddingDegreeZeroSerreMap_unit_square
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : Z.Modules) (m : M ⟶ M) (U : DerivedCategory Y.Modules)
    (η : U ⟶ DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (i ≫ p)).obj
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M))) (b : U ⟶ U)
    (hη : b ≫ η = η ≫ (derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι).map
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).map m))
    (s : relativeClosedEmbeddingUnitTraceSource i p n N M) :
    η ≫ relativeClosedEmbeddingDegreeZeroSerreMap i p R ι a f h n e N M
        ((DerivedCategory.singleFunctor Z.Modules 0).map m ≫ s) =
      b ≫ η ≫ relativeClosedEmbeddingDegreeZeroSerreMap i p R ι a f h n e N M s := by
  rw [relativeClosedEmbeddingDegreeZeroSerreMap_precomp]
  exact unit_square_paste η b _ _ hη

end AlgebraicGeometry.Scheme.Cohomology

namespace ModuleCat

variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)

/-- The original coinduction adjoint of an actual R-linear trace map. -/
def sourceTraceCoinduced (V : ModuleCat.{u} A)
    (τ : (restrictScalars σ).obj V ⟶ ModuleCat.of R R) :
    V ⟶ (coextendScalars σ).obj (ModuleCat.of R R) :=
  RestrictionCoextensionAdj.HomEquiv.fromRestriction σ τ

/-- Its original functional evaluates at a by applying the original trace to a times the source. -/
theorem sourceTraceCoinduced_apply (V : ModuleCat.{u} A)
    (τ : (restrictScalars σ).obj V ⟶ ModuleCat.of R R) (v : V) (a : A) :
    CoextendScalars.equiv σ (ModuleCat.of R R) (sourceTraceCoinduced σ V τ v) a =
      τ (a • v) := rfl

/-- The source unit square is proved in the genuine A-linear derived category before restriction. -/
theorem restrictDerivedUnit_scalar_square
    [HasDerivedCategory.{dA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{dR} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} A))
    (η : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ C)
    (a : A) :
    (restrictScalars σ).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (a • 𝟙 (ModuleCat.of A A))) ≫
      (restrictScalars σ).mapDerivedCategory.map η =
    (restrictScalars σ).mapDerivedCategory.map η ≫
      (restrictScalars σ).mapDerivedCategory.map (a • 𝟙 C) := by
  have hm : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
      (a • 𝟙 (ModuleCat.of A A)) =
      a • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rw [hm]
  exact map_source_scalar_square (restrictScalars σ).mapDerivedCategory η a


end ModuleCat

private theorem rightDerivedPlusIso_singleUnit
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C] {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w'} D] (F G : C ⥤ D) [F.Additive] [G.Additive]
    (e : F ≅ G) (M : C) :
    F.rightDerivedSingleUnit M ≫ (F.rightDerivedFunctorPlusIso e).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj M) =
      (DerivedCategory.Plus.singleFunctor D 0).map (e.hom.app M) ≫
        G.rightDerivedSingleUnit M := by
  let K := (CochainComplex.singleFunctorPlus C 0).obj M
  let S := CochainComplex.singleFunctorPlus D 0
  let Q : CochainComplex.Plus D ⥤ DerivedCategory.Plus D := DerivedCategory.Plus.Q
  let τF : S.obj (F.obj M) ⟶ F.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let τG : S.obj (G.obj M) ⟶ G.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex G (.up ℤ) 0).inv.app M)
  have hτ : τF ≫ (NatIso.mapCochainComplexPlus e).hom.app K =
      S.map (e.hom.app M) ≫ τG := by
    apply ObjectProperty.hom_ext
    change (singleMapHomologicalComplex F (.up ℤ) 0).inv.app M ≫
        (e.hom.mapHomologicalComplex (.up ℤ)).app
          ((CochainComplex.singleFunctor C 0).obj M) =
      (CochainComplex.singleFunctor D 0).map (e.hom.app M) ≫
        (singleMapHomologicalComplex G (.up ℤ) 0).inv.app M
    rw [natTransMapHomologicalComplex_app_single_obj]
    simp only [Iso.inv_hom_id_app_assoc]
  change (Q.map τF ≫ F.rightDerivedFunctorPlusUnit.app K) ≫
      (F.rightDerivedFunctorPlusIso e).hom.app (DerivedCategory.Plus.Q.obj K) =
    Q.map (S.map (e.hom.app M)) ≫ (Q.map τG ≫ G.rightDerivedFunctorPlusUnit.app K)
  rw [Category.assoc, F.rightDerivedFunctorPlusIso_hom_app e K]
  rw [← Category.assoc, ← Q.map_comp, hτ, Q.map_comp, Category.assoc]

private theorem rightDerivedPlusCompIso_singleUnit
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C] {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w'} D] [EnoughInjectives D]
    {E : Type u''} [Category.{v''} E] [Abelian E] [HasDerivedCategory.{w''} E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [G.PreservesHomology]
    (M : C) :
    (F ⋙ G).rightDerivedSingleUnit M ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj M) =
      G.rightDerivedSingleUnit (F.obj M) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedSingleUnit M) := by
  let K := (CochainComplex.singleFunctorPlus C 0).obj M
  let L := (CochainComplex.singleFunctorPlus D 0).obj (F.obj M)
  let S := CochainComplex.singleFunctorPlus E 0
  let Q : CochainComplex.Plus E ⥤ DerivedCategory.Plus E := DerivedCategory.Plus.Q
  let τF : L ⟶ F.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let τG : S.obj (G.obj (F.obj M)) ⟶ G.mapCochainComplexPlus.obj L :=
    ObjectProperty.homMk ((singleMapHomologicalComplex G (.up ℤ) 0).inv.app (F.obj M))
  let τFG : S.obj (G.obj (F.obj M)) ⟶ (F ⋙ G).mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex (F ⋙ G) (.up ℤ) 0).inv.app M)
  have hτ : τFG = τG ≫ G.mapCochainComplexPlus.map τF := by
    apply ObjectProperty.hom_ext
    exact singleMapHomologicalComplex_comp_inv_app F G (.up ℤ) 0 M
  have hη := G.rightDerivedFunctorPlusUnit.naturality τF
  change Q.map (G.mapCochainComplexPlus.map τF) ≫
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) =
    G.rightDerivedFunctorPlusUnit.app L ≫
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map τF) at hη
  change (Q.map τFG ≫ (F ⋙ G).rightDerivedFunctorPlusUnit.app K) ≫
      (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
        (DerivedCategory.Plus.Q.obj K) =
    (Q.map τG ≫ G.rightDerivedFunctorPlusUnit.app L) ≫
      G.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map τF ≫ F.rightDerivedFunctorPlusUnit.app K)
  rw [Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app,
    hτ, Q.map_comp, G.rightDerivedFunctorPlus.map_comp]
  calc
    _ = Q.map τG ≫ (Q.map (G.mapCochainComplexPlus.map τF) ≫
        G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K)) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
      simp only [Category.assoc]
    _ = Q.map τG ≫ (G.rightDerivedFunctorPlusUnit.app L ≫
        G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map τF)) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by rw [hη]
    _ = _ := by simp only [Category.assoc]

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived category of `R`-modules for the scalar-restriction comparison. -/
local instance traceModuleDerived (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A]
    (X : Scheme.{u}) (σ : R →+* A) (αA : A →+* Γ(X, ⊤))
    (αR : R →+* Γ(X, ⊤)) (hα : αR = αA.comp σ)

/-- The original section carrier, with only native successive scalar restriction. -/
def moduleGlobalSectionsRestrictIso :
    moduleGlobalSectionsFunctorOfHom X αR ≅
      moduleGlobalSectionsFunctorOfHom X αA ⋙ ModuleCat.restrictScalars σ :=
  isoWhiskerLeft (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
      (ModuleCat.restrictScalarsComp' σ αA αR hα) ≪≫
    (associator (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
      (ModuleCat.restrictScalars αA) (ModuleCat.restrictScalars σ)).symm

theorem moduleGlobalSectionsRestrictIso_hom_apply (M : X.Modules)
    (x : (moduleGlobalSectionsFunctorOfHom X αR).obj M) :
    (moduleGlobalSectionsRestrictIso X σ αA αR hα).hom.app M x = x := rfl

/-- Derive that same identity on sections and use exact original restriction. -/
def moduleDerivedGlobalSectionsRestrictIso :
    (moduleGlobalSectionsFunctorOfHom X αR).rightDerivedFunctorPlus ≅
      (moduleGlobalSectionsFunctorOfHom X αA).rightDerivedFunctorPlus ⋙
        (ModuleCat.restrictScalars σ).rightDerivedFunctorPlus :=
  (moduleGlobalSectionsFunctorOfHom X αR).rightDerivedFunctorPlusIso
      (moduleGlobalSectionsRestrictIso X σ αA αR hα) ≪≫
    rightDerivedFunctorPlusCompIsoOfPreservesHomology
      (moduleGlobalSectionsFunctorOfHom X αA) (ModuleCat.restrictScalars σ)

/-- The comparison retains both original single units and the identity on sections. -/
theorem moduleDerivedGlobalSectionsRestrictIso_singleUnit (M : X.Modules) :
    (moduleGlobalSectionsFunctorOfHom X αR).rightDerivedSingleUnit M ≫
        (moduleDerivedGlobalSectionsRestrictIso X σ αA αR hα).hom.app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
          ((moduleGlobalSectionsRestrictIso X σ αA αR hα).hom.app M) ≫
        (ModuleCat.restrictScalars σ).rightDerivedSingleUnit
          ((moduleGlobalSectionsFunctorOfHom X αA).obj M) ≫
        (ModuleCat.restrictScalars σ).rightDerivedFunctorPlus.map
          ((moduleGlobalSectionsFunctorOfHom X αA).rightDerivedSingleUnit M) := by
  let FR := moduleGlobalSectionsFunctorOfHom X αR
  let FA := moduleGlobalSectionsFunctorOfHom X αA
  let U := ModuleCat.restrictScalars σ
  let K := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj M
  let E := FR.rightDerivedFunctorPlusIso
    (moduleGlobalSectionsRestrictIso X σ αA αR hα)
  let T := rightDerivedFunctorPlusCompIsoOfPreservesHomology FA U
  let c := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
    ((moduleGlobalSectionsRestrictIso X σ αA αR hα).hom.app M)
  change FR.rightDerivedSingleUnit M ≫ (E.hom.app K ≫ T.hom.app K) = _
  calc
    _ = (FR.rightDerivedSingleUnit M ≫ E.hom.app K) ≫ T.hom.app K :=
      (Category.assoc _ _ _).symm
    _ = (c ≫ (FA ⋙ U).rightDerivedSingleUnit M) ≫ T.hom.app K :=
      congrArg (fun k => k ≫ T.hom.app K)
        (rightDerivedPlusIso_singleUnit FR (FA ⋙ U)
          (moduleGlobalSectionsRestrictIso X σ αA αR hα) M)
    _ = c ≫ ((FA ⋙ U).rightDerivedSingleUnit M ≫ T.hom.app K) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun k => c ≫ k) (rightDerivedPlusCompIso_singleUnit FA U M)

/-- The original ring map as a map into its genuine restricted regular module. -/
def scalarRestrictionUnitMap : ModuleCat.of R R ⟶
    (ModuleCat.restrictScalars σ).obj (ModuleCat.of A A) := by
  let N : ModuleCat.{u} R := (ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)
  let c : R →ₗ[R] N := {
    toFun := fun r => σ r
    map_add' := σ.map_add
    map_smul' := fun r s => σ.map_mul r s }
  exact ModuleCat.ofHom (X := R) (Y := N) c

/-- The actual structural section maps commute through the original scalar restriction. -/
theorem moduleStructuralSectionsMap_restrict :
    moduleStructuralSectionsMap X αR ≫
        (moduleGlobalSectionsRestrictIso X σ αA αR hα).hom.app
          (SheafOfModules.unit X.ringCatSheaf) =
      scalarRestrictionUnitMap σ ≫
        (ModuleCat.restrictScalars σ).map (moduleStructuralSectionsMap X αA) := by
  apply ConcreteCategory.hom_ext
  intro r
  change αR r = αA (σ r)
  exact congrArg (fun f : R →+* Γ(X, ⊤) => f r) hα

/-- Restricting the actual derived structural unit gives the original base unit. -/
theorem moduleDerivedStructureUnit_restrict :
    moduleDerivedStructureUnit X αR ≫
        (moduleDerivedGlobalSectionsRestrictIso X σ αA αR hα).hom.app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
            (SheafOfModules.unit X.ringCatSheaf)) =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
          (scalarRestrictionUnitMap σ) ≫
        (ModuleCat.restrictScalars σ).rightDerivedSingleUnit (ModuleCat.of A A) ≫
        (ModuleCat.restrictScalars σ).rightDerivedFunctorPlus.map
          (moduleDerivedStructureUnit X αA) := by
  let SR := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0
  let U := ModuleCat.restrictScalars σ
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let FA := moduleGlobalSectionsFunctorOfHom X αA
  let FR := moduleGlobalSectionsFunctorOfHom X αR
  let SA := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0
  let cA : ModuleCat.of A A ⟶ FA.obj O := moduleStructuralSectionsMap X αA
  let cR : ModuleCat.of R R ⟶ FR.obj O := moduleStructuralSectionsMap X αR
  let v : FR.obj O ⟶ U.obj (FA.obj O) :=
    (moduleGlobalSectionsRestrictIso X σ αA αR hα).hom.app O
  have hc : SR.map cR ≫ SR.map v =
      SR.map (scalarRestrictionUnitMap σ) ≫ SR.map (U.map cA) := by
    calc
      _ = SR.map (cR ≫ v) := (SR.map_comp cR v).symm
      _ = SR.map (scalarRestrictionUnitMap σ ≫ U.map cA) :=
        congrArg SR.map (moduleStructuralSectionsMap_restrict X σ αA αR hα)
      _ = _ := SR.map_comp _ _
  exact unit_comparison_paste
    (SR.map cR) (FR.rightDerivedSingleUnit O)
    ((moduleDerivedGlobalSectionsRestrictIso X σ αA αR hα).hom.app
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj O))
    (SR.map (scalarRestrictionUnitMap σ)) (SR.map (U.map cA)) (SR.map v)
    (U.rightDerivedSingleUnit (FA.obj O)) (U.rightDerivedSingleUnit (ModuleCat.of A A))
    (U.rightDerivedFunctorPlus.map (SA.map cA))
    (U.rightDerivedFunctorPlus.map (FA.rightDerivedSingleUnit O))
    (U.rightDerivedFunctorPlus.map (moduleDerivedStructureUnit X αA))
    (moduleDerivedGlobalSectionsRestrictIso_singleUnit X σ αA αR hα O) hc
    (U.rightDerivedSingleUnit_naturality cA)
    (U.rightDerivedFunctorPlus.map_comp (SA.map cA) (FA.rightDerivedSingleUnit O))

private theorem originalGlobalSectionsLinear (A : Type u) [CommRing A]
    (X : Scheme.{u}) (α : A →+* Γ(X, ⊤)) :
    letI := moduleCategoryLinearOfHom X α
    (moduleGlobalSectionsFunctorOfHom X α).Linear A := by
  let := moduleCategoryLinearOfHom X α
  constructor
  intro M N φ a
  apply ConcreteCategory.hom_ext
  intro x
  have h := moduleCategoryLinearOfHom_smul_app X α φ a ⊤ x
  have htop : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := rfl
  rw [htop, X.presheaf.map_id] at h
  exact h

/-- The original A-linear structural unit commutes with the original source multiplication.
Only ordinary sections and single-unit naturality enter this statement. -/
theorem moduleDerivedStructureUnit_source_scalar_square (a : A) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    letI := moduleCategoryLinearOfHom X αA
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).map
        (a • 𝟙 (ModuleCat.of A A)) ≫ moduleDerivedStructureUnit X αA =
      moduleDerivedStructureUnit X αA ≫
        (moduleGlobalSectionsFunctorOfHom X αA).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
            (a • 𝟙 O)) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let := moduleCategoryLinearOfHom X αA
  let : (moduleGlobalSectionsFunctorOfHom X αA).Linear A :=
    originalGlobalSectionsLinear A X αA
  apply (moduleGlobalSectionsFunctorOfHom X αA).rightDerivedSingleUnit_coefficient_naturality
  exact coefficient_source_scalar_square (moduleGlobalSectionsFunctorOfHom X αA)
    (moduleStructuralSectionsMap X αA) a

end AlgebraicGeometry.Scheme.Cohomology

private theorem rightDerivedSingleUnit_acyclic
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C] {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w'} D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (M : C)
    (hM : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M)) :
    F.rightDerivedSingleUnit M ≫ (F.rightDerivedFunctorPlusSingleIsoOfAcyclic M hM).hom =
      𝟙 _ := by
  let E : F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj M) ≅
      (CochainComplex.singleFunctorPlus D 0).obj (F.obj M) :=
    (CochainComplex.plus D).isoMk ((singleMapHomologicalComplex F (.up ℤ) 0).app M)
  exact mapped_iso_unit DerivedCategory.Plus.Q E
    (F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj M))
    (F.rightDerivedFunctorPlusSingleIsoOfAcyclic M hM).hom
    (F.rightDerivedFunctorPlusSingleIsoOfAcyclic_unit M hM)

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived category of `R`-modules for affine target normalization. -/
local instance traceModuleDerived' (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

/-- Native affine sections and the original structural section functor have identical values. -/
def moduleAffineGlobalSectionsIso (B : CommRingCat.{u}) :
    (moduleSpecΓFunctor : (Spec B).Modules ⥤ ModuleCat.{u} B) ≅
      moduleGlobalSectionsFunctorOfHom (Spec B) (ΓSpecIso B).inv.hom :=
  NatIso.ofComponents (moduleTopSectionsIso (Spec B) (ΓSpecIso B).inv.hom)
    (by intro M N f; ext x; rfl)

/-- The target coefficient is the original affine structure module under ΓSpec. -/
def moduleAffineStructureSectionsIso (B : CommRingCat.{u}) :
    (moduleGlobalSectionsFunctorOfHom (Spec B) (ΓSpecIso B).inv.hom).obj
        (SheafOfModules.unit (Spec B).ringCatSheaf) ≅ ModuleCat.of B B := by
  let c := moduleStructuralSectionsMap (Spec B) (ΓSpecIso B).inv.hom
  have hc : Function.Bijective c :=
    (ΓSpecIso B).commRingCatIsoToRingEquiv.symm.bijective
  let : IsIso c := (ConcreteCategory.isIso_iff_bijective c).mpr hc
  exact (asIso c).symm

/-- Its inverse is the original structural section map, rather than a new coefficient map. -/
theorem moduleAffineStructureSectionsIso_inv (B : CommRingCat.{u}) :
    (moduleAffineStructureSectionsIso B).inv =
      moduleStructuralSectionsMap (Spec B) (ΓSpecIso B).inv.hom := rfl

theorem moduleAffineStructureSectionsIso_unit (B : CommRingCat.{u}) :
    moduleStructuralSectionsMap (Spec B) (ΓSpecIso B).inv.hom ≫
        (moduleAffineStructureSectionsIso B).hom = 𝟙 (ModuleCat.of B B) := by
  exact (moduleAffineStructureSectionsIso B).inv_hom_id

/-- Affine quasicoherent acyclicity makes the original structure single unit invertible. -/
theorem affineStructureUnit_isIso (B : CommRingCat.{u}) :
    IsIso ((moduleGlobalSectionsFunctorOfHom (Spec B)
      (ΓSpecIso B).inv.hom).rightDerivedSingleUnit
        (SheafOfModules.unit (Spec B).ringCatSheaf)) := by
  let O : (Spec B).Modules := SheafOfModules.unit (Spec B).ringCatSheaf
  let : O.IsQuasicoherent := isQuasicoherent_unit (Spec B)
  let F := moduleGlobalSectionsFunctorOfHom (Spec B) (ΓSpecIso B).inv.hom
  let G : (Spec B).Modules ⥤ ModuleCat.{u} B := moduleSpecΓFunctor
  let e := (moduleAffineGlobalSectionsIso B).symm
  let hO := fun n => AffineDerived.isZero_rightDerived_globalSections_succ O n
  let t := G.rightDerivedFunctorPlusSingleIsoOfAcyclic O hO
  have hi : IsIso (G.rightDerivedSingleUnit O ≫ t.hom) := by
    rw [rightDerivedSingleUnit_acyclic]
    infer_instance
  have : IsIso (G.rightDerivedSingleUnit O) :=
    IsIso.of_isIso_comp_right _ t.hom
  have he : IsIso (F.rightDerivedSingleUnit O ≫
      (F.rightDerivedFunctorPlusIso e).hom.app
        ((DerivedCategory.Plus.singleFunctor (Spec B).Modules 0).obj O)) := by
    rw [rightDerivedPlusIso_singleUnit]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((F.rightDerivedFunctorPlusIso e).hom.app
      ((DerivedCategory.Plus.singleFunctor (Spec B).Modules 0).obj O))

/-- Affine normalization uses the inverse of the actual single unit and the original ΓSpec map. -/
def affineDerivedStructureTargetIso (B : CommRingCat.{u}) :
    moduleDerivedStructure (Spec B) (ΓSpecIso B).inv.hom ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) := by
  let := affineStructureUnit_isIso B
  exact (asIso ((moduleGlobalSectionsFunctorOfHom (Spec B)
      (ΓSpecIso B).inv.hom).rightDerivedSingleUnit
        (SheafOfModules.unit (Spec B).ringCatSheaf))).symm ≪≫
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} B) 0).mapIso
      (moduleAffineStructureSectionsIso B)

/-- The original affine structural unit is normalized to the identity of the original base. -/
theorem affineDerivedStructureTargetIso_unit (B : CommRingCat.{u}) :
    moduleDerivedStructureUnit (Spec B) (ΓSpecIso B).inv.hom ≫
        (affineDerivedStructureTargetIso B).hom = 𝟙 _ := by
  let F := moduleGlobalSectionsFunctorOfHom (Spec B) (ΓSpecIso B).inv.hom
  let O : (Spec B).Modules := SheafOfModules.unit (Spec B).ringCatSheaf
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} B) 0
  let := affineStructureUnit_isIso B
  change (S.map (moduleStructuralSectionsMap (Spec B) (ΓSpecIso B).inv.hom) ≫
      F.rightDerivedSingleUnit O) ≫
      inv (F.rightDerivedSingleUnit O) ≫ S.map (moduleAffineStructureSectionsIso B).hom = _
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← S.map_comp, moduleAffineStructureSectionsIso_unit, S.map_id]

section GeometricTrace

variable (R : Type u) [CommRing R] (ι : Type u)
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ Spec (.of R)) (a : P ⟶ ProjectiveSpace R ι)
    (h : IsPullback a p (ProjectiveSpace.toSpec R ι) (𝟙 (Spec (.of R))))
    (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- The same original source Hom, with the literal base-unit coefficient. -/
abbrev chosenEmbeddingUnitTraceSource :=
  relativeClosedEmbeddingUnitTraceSource i p n
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)
    (SheafOfModules.unit Z.ringCatSheaf)

/-- The actual structural map from the original projective composite. -/
abbrev chosenEmbeddingBaseScalar : R →+* Γ(Z, ⊤) :=
  (i ≫ p).appTop.hom.comp (ΓSpecIso (.of R)).inv.hom

/-- The degree-zero map is lifted through the fully faithful native bounded-below inclusion. -/
def chosenEmbeddingSerreMapPlus :
    chosenEmbeddingUnitTraceSource R i p n →+
      ((derivedPushforwardPlus (i ≫ p)).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj
            (SheafOfModules.unit Z.ringCatSheaf)) ⟶
        (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj
          (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)) := by
  let OZ : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let OY : (Spec (.of R)).Modules := SheafOfModules.unit (Spec (.of R)).ringCatSheaf
  let U := (derivedPushforwardPlus (i ≫ p)).obj
    ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj OZ)
  let V := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj OY
  exact (DerivedCategory.Plus.ι.preimageAddHom U V).comp
    (relativeClosedEmbeddingDegreeZeroSerreMap i p R ι a (𝟙 _) h n e OY OZ)

/-- The original projective comparison followed by original module-valued derived sections. -/
def chosenEmbeddingModuleSerreMap :
    chosenEmbeddingUnitTraceSource R i p n →+
      (moduleDerivedStructure Z (chosenEmbeddingBaseScalar R i p) ⟶
        (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) := by
  let OZ : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let OY : (Spec (.of R)).Modules := SheafOfModules.unit (Spec (.of R)).ringCatSheaf
  let U := (derivedPushforwardPlus (i ≫ p)).obj
    ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj OZ)
  let V := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj OY
  let F := (moduleGlobalSectionsFunctorOfHom (Spec (.of R))
    (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
  let C := moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ p) (ΓSpecIso (.of R)).inv.hom
  let T := affineDerivedStructureTargetIso (.of R)
  exact (Preadditive.leftComp _ (C.hom.app
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj OZ))).comp
    ((Preadditive.rightComp _ T.hom).comp
      ((F.mapAddHom (X := U) (Y := V)).comp
        (chosenEmbeddingSerreMapPlus R ι i p a h n e)))

/-- The module-valued map still carries the same original source multiplication. -/
theorem chosenEmbeddingModuleSerreMap_precomp
    (m : (SheafOfModules.unit Z.ringCatSheaf : Z.Modules) ⟶
      (SheafOfModules.unit Z.ringCatSheaf : Z.Modules))
    (s : chosenEmbeddingUnitTraceSource R i p n) :
    chosenEmbeddingModuleSerreMap R ι i p a h n e
        ((DerivedCategory.singleFunctor Z.Modules 0).map m ≫ s) =
      (moduleGlobalSectionsFunctorOfHom Z
          (chosenEmbeddingBaseScalar R i p)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor Z.Modules 0).map m) ≫
        chosenEmbeddingModuleSerreMap R ι i p a h n e s := by
  let F := moduleGlobalSectionsFunctorOfHom (Spec (.of R)) (ΓSpecIso (.of R)).inv.hom
  let C := moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ p) (ΓSpecIso (.of R)).inv.hom
  let mD := (DerivedCategory.Plus.singleFunctor Z.Modules 0).map m
  let t := (derivedPushforwardPlus (i ≫ p)).map mD
  let OY : (Spec (.of R)).Modules := SheafOfModules.unit (Spec (.of R)).ringCatSheaf
  let OZ : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let Φ := relativeClosedEmbeddingDegreeZeroSerreMap i p R ι a (𝟙 _) h n e OY OZ
  have ht : chosenEmbeddingSerreMapPlus R ι i p a h n e
      ((DerivedCategory.singleFunctor Z.Modules 0).map m ≫ s) =
      t ≫ chosenEmbeddingSerreMapPlus R ι i p a h n e s :=
    preimage_source_comp
      (Z := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj OY)
      DerivedCategory.Plus.ι t (Φ s)
      (Φ ((DerivedCategory.singleFunctor Z.Modules 0).map m ≫ s))
      (relativeClosedEmbeddingDegreeZeroSerreMap_precomp i p R ι a (𝟙 _) h n e OY m s)
  have hm := C.hom.naturality mD
  change (moduleGlobalSectionsFunctorOfHom Z
      (chosenEmbeddingBaseScalar R i p)).rightDerivedFunctorPlus.map mD ≫ C.hom.app _ =
    C.hom.app _ ≫ F.rightDerivedFunctorPlus.map t at hm
  exact mapped_source_paste F.rightDerivedFunctorPlus t
    (chosenEmbeddingSerreMapPlus R ι i p a h n e s)
    (chosenEmbeddingSerreMapPlus R ι i p a h n e
      ((DerivedCategory.singleFunctor Z.Modules 0).map m ≫ s))
    (C.hom.app ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj OZ))
    (affineDerivedStructureTargetIso (.of R)).hom
    ((moduleGlobalSectionsFunctorOfHom Z
      (chosenEmbeddingBaseScalar R i p)).rightDerivedFunctorPlus.map mD) ht hm

end GeometricTrace

end AlgebraicGeometry.Scheme.Cohomology

private theorem rightDerivedSingleUnit_exact
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C] {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w'} D] (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (M : C) : F.rightDerivedSingleUnit M ≫
      (F.rightDerivedFunctorPlusSingleIso 0).hom.app M = 𝟙 _ := by
  let E : F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj M) ≅
      (CochainComplex.singleFunctorPlus D 0).obj (F.obj M) :=
    (CochainComplex.plus D).isoMk ((singleMapHomologicalComplex F (.up ℤ) 0).app M)
  exact mapped_iso_unit DerivedCategory.Plus.Q E
    (F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj M))
    ((F.rightDerivedFunctorPlusSingleIso 0).hom.app M)
    (F.rightDerivedFunctorPlusSingleIso_unit 0 M)

private theorem unit_natIso_paste {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (T : F ≅ G) {U V : C} (η : U ⟶ V)
    {P : D} (d : P ⟶ F.obj U) (e : P ⟶ G.obj U)
    (hd : d ≫ T.hom.app U = e) :
    d ≫ F.map η = e ≫ G.map η ≫ T.inv.app V := by
  apply (cancel_mono (T.hom.app V)).mp
  simp only [Category.assoc, T.inv_hom_id_app, Category.comp_id]
  rw [T.hom.naturality, ← Category.assoc, hd]

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived category of `R`-modules for the restricted structural unit. -/
local instance traceModuleDerived'' (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A]
    (X : Scheme.{u}) (σ : R →+* A) (αA : A →+* Γ(X, ⊤))
    (αR : R →+* Γ(X, ⊤)) (hα : αR = αA.comp σ)

/-- The actual restricted structural unit, using the original derived restriction comparison. -/
def moduleRestrictedDerivedStructureUnit :
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) ⟶
      moduleDerivedStructure X αR :=
  (ModuleCat.restrictScalars σ).rightDerivedSingleUnit (ModuleCat.of A A) ≫
    (ModuleCat.restrictScalars σ).rightDerivedFunctorPlus.map
      (moduleDerivedStructureUnit X αA) ≫
    (moduleDerivedGlobalSectionsRestrictIso X σ αA αR hα).inv.app
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf))

/-- Precomposing with the original ring map recovers the original base structural unit. -/
theorem moduleRestrictedDerivedStructureUnit_normalization :
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
        (scalarRestrictionUnitMap σ) ≫
      moduleRestrictedDerivedStructureUnit X σ αA αR hα =
    moduleDerivedStructureUnit X αR := by
  let E := moduleDerivedGlobalSectionsRestrictIso X σ αA αR hα
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let M := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj O
  let s := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
    (scalarRestrictionUnitMap σ)
  let d := (ModuleCat.restrictScalars σ).rightDerivedSingleUnit (ModuleCat.of A A)
  let η := (ModuleCat.restrictScalars σ).rightDerivedFunctorPlus.map
    (moduleDerivedStructureUnit X αA)
  exact unit_iso_inv_paste (E.app M) (moduleDerivedStructureUnit X αR) s d η
    (moduleDerivedStructureUnit_restrict X σ αA αR hα)

/-- The literal source multiplication square for the original restricted unit. -/
theorem moduleRestrictedDerivedStructureUnit_source_scalar_square (a : A) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    letI := moduleCategoryLinearOfHom X αA
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
        ((ModuleCat.restrictScalars σ).map (a • 𝟙 (ModuleCat.of A A))) ≫
      moduleRestrictedDerivedStructureUnit X σ αA αR hα =
    moduleRestrictedDerivedStructureUnit X σ αA αR hα ≫
      (moduleGlobalSectionsFunctorOfHom X αR).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
          (a • 𝟙 O)) := by
  let := moduleCategoryLinearOfHom X αA
  let U := ModuleCat.restrictScalars σ
  let FR := (moduleGlobalSectionsFunctorOfHom X αR).rightDerivedFunctorPlus
  let FA := (moduleGlobalSectionsFunctorOfHom X αA).rightDerivedFunctorPlus
  let E := moduleDerivedGlobalSectionsRestrictIso X σ αA αR hα
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let M := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj O
  let m := (DerivedCategory.Plus.singleFunctor X.Modules 0).map (a • 𝟙 O)
  let b := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).map
    (a • 𝟙 (ModuleCat.of A A))
  let bR := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
    (U.map (a • 𝟙 (ModuleCat.of A A)))
  let η := moduleDerivedStructureUnit X αA
  let d := U.rightDerivedSingleUnit (ModuleCat.of A A)
  have hd : bR ≫ d = d ≫ U.rightDerivedFunctorPlus.map b :=
    U.rightDerivedSingleUnit_naturality (a • 𝟙 (ModuleCat.of A A))
  have hη : b ≫ η = η ≫ FA.map m :=
    moduleDerivedStructureUnit_source_scalar_square X αA a
  have hE := E.inv.naturality m
  change U.rightDerivedFunctorPlus.map (FA.map m) ≫ E.inv.app M =
    E.inv.app M ≫ FR.map m at hE
  exact restricted_scalar_paste U.rightDerivedFunctorPlus η b (FA.map m)
    d (E.inv.app M) bR (FR.map m) hd hη hE

/-- The same restriction comparison in the full derived category, with native exact restriction. -/
def moduleDerivedStructureRestrictionIso :
    DerivedCategory.Plus.ι.obj (moduleDerivedStructure X αR) ≅
      (ModuleCat.restrictScalars σ).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj (moduleDerivedStructure X αA)) :=
  DerivedCategory.Plus.ι.mapIso
      ((moduleDerivedGlobalSectionsRestrictIso X σ αA αR hα).app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit X.ringCatSheaf))) ≪≫
    (ModuleCat.restrictScalars σ).rightDerivedFunctorPlusCompιIso.app
      (moduleDerivedStructure X αA)

/-- The exact native single comparison identifies the original single unit after inclusion. -/
theorem restrictScalars_singleUnit_full :
    DerivedCategory.Plus.ι.map
        ((ModuleCat.restrictScalars σ).rightDerivedSingleUnit (ModuleCat.of A A)) ≫
      (ModuleCat.restrictScalars σ).rightDerivedFunctorPlusCompιIso.hom.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) =
      ((ModuleCat.restrictScalars σ).mapDerivedCategorySingleFunctor 0).inv.app
        (ModuleCat.of A A) := by
  let U := ModuleCat.restrictScalars σ
  let e := (U.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A A)
  exact mapped_single_unit DerivedCategory.Plus.ι e
    (U.rightDerivedSingleUnit (ModuleCat.of A A))
    (U.rightDerivedFunctorPlusCompιIso.hom.app
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    ((U.rightDerivedFunctorPlusSingleIso 0).hom.app (ModuleCat.of A A))
    (U.rightDerivedFunctorPlusCompιIso_hom_app_singleFunctor_obj (ModuleCat.of A A))
    (rightDerivedSingleUnit_exact U (ModuleCat.of A A))

/-- This is literally Res of the installed original unit, with all single and restriction
comparisons displayed. No independently chosen unit is used. -/
theorem moduleRestrictedDerivedStructureUnit_full :
    DerivedCategory.Plus.ι.map (moduleRestrictedDerivedStructureUnit X σ αA αR hα) =
      ((ModuleCat.restrictScalars σ).mapDerivedCategorySingleFunctor 0).inv.app
          (ModuleCat.of A A) ≫
        (ModuleCat.restrictScalars σ).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit X αA)) ≫
        (moduleDerivedStructureRestrictionIso X σ αA αR hα).inv := by
  let U := ModuleCat.restrictScalars σ
  let T := U.rightDerivedFunctorPlusCompιIso
  let η := moduleDerivedStructureUnit X αA
  let d := DerivedCategory.Plus.ι.map (U.rightDerivedSingleUnit (ModuleCat.of A A))
  let e := (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A)
  have hd := restrictScalars_singleUnit_full σ
  have h := unit_natIso_paste T η d e hd
  change d ≫ DerivedCategory.Plus.ι.map (U.rightDerivedFunctorPlus.map η) =
    e ≫ U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map η) ≫
      T.inv.app (moduleDerivedStructure X αA) at h
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let M := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj O
  exact map_unit_factor DerivedCategory.Plus.ι
    (U.rightDerivedSingleUnit (ModuleCat.of A A)) (U.rightDerivedFunctorPlus.map η)
    ((moduleDerivedGlobalSectionsRestrictIso X σ αA αR hα).inv.app M)
    e (U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map η))
    (T.inv.app (moduleDerivedStructure X αA)) h

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived category of `R`-modules for the chosen-embedding trace pairing. -/
local instance traceModuleDerived''' (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

variable (R : Type u) [CommRing R] (ι : Type u)
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ Spec (.of R)) (a : P ⟶ ProjectiveSpace R ι)
    (h : IsPullback a p (ProjectiveSpace.toSpec R ι) (𝟙 (Spec (.of R))))
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {A : Type u} [CommRing A] (σ : R →+* A)
    (αA : A →+* Γ(Z, ⊤)) (hα : chosenEmbeddingBaseScalar R i p = αA.comp σ)

/-- The actual restricted unit followed by the original module-valued Serre map. -/
def chosenEmbeddingUnitPairingPlus :
    chosenEmbeddingUnitTraceSource R i p n →+
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) ⟶
        (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) where
  toFun s := moduleRestrictedDerivedStructureUnit Z σ αA (chosenEmbeddingBaseScalar R i p) hα ≫
    chosenEmbeddingModuleSerreMap R ι i p a h n e s
  map_zero' := by rw [map_zero, Limits.comp_zero]
  map_add' s t := by rw [_root_.map_add, Preadditive.comp_add]

/-- Native full faithfulness of the single functor gives the actual R-linear functional on A. -/
def chosenEmbeddingUnitFunctional :
    chosenEmbeddingUnitTraceSource R i p n →+
      ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A) ⟶ ModuleCat.of R R) := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  exact (F.preimageAddHom ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))
      (ModuleCat.of R R)).comp
    (DerivedCategory.Plus.ι.mapAddHom.comp
      (chosenEmbeddingUnitPairingPlus R ι i p a h n e σ αA hα))

/-- The original chosen-embedding trace is the same Serre map after the actual base unit,
evaluated at one through the native fully faithful single functor. -/
def chosenEmbeddingTraceBase : chosenEmbeddingUnitTraceSource R i p n →+ R := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let ev : (ModuleCat.of R R ⟶ ModuleCat.of R R) →+ R := {
    toFun := fun f => f (1 : R)
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  exact ev.comp ((F.preimageAddHom (ModuleCat.of R R) (ModuleCat.of R R)).comp
    (DerivedCategory.Plus.ι.mapAddHom.comp
      ((Preadditive.leftComp _ (moduleDerivedStructureUnit Z
          (chosenEmbeddingBaseScalar R i p))).comp
        (chosenEmbeddingModuleSerreMap R ι i p a h n e))))

/-- The two actual units identify evaluation at one with the original base trace. -/
theorem chosenEmbeddingTraceBase_eq_unitFunctional
    (s : chosenEmbeddingUnitTraceSource R i p n) :
    chosenEmbeddingTraceBase R ι i p a h n e s =
      chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα s (1 : A) := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let β := chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα s
  let γ : ModuleCat.of R R ⟶ ModuleCat.of R R := F.preimage
    (DerivedCategory.Plus.ι.map
      (moduleDerivedStructureUnit Z (chosenEmbeddingBaseScalar R i p) ≫
        chosenEmbeddingModuleSerreMap R ι i p a h n e s))
  let η := moduleRestrictedDerivedStructureUnit Z σ αA (chosenEmbeddingBaseScalar R i p) hα
  let ηR := moduleDerivedStructureUnit Z (chosenEmbeddingBaseScalar R i p)
  let Φ := chosenEmbeddingModuleSerreMap R ι i p a h n e s
  let m := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
    (scalarRestrictionUnitMap σ)
  have hp : m ≫ (η ≫ Φ) = ηR ≫ Φ := append_comp_eq m η ηR Φ
    (moduleRestrictedDerivedStructureUnit_normalization
      Z σ αA (chosenEmbeddingBaseScalar R i p) hα)
  have hh : scalarRestrictionUnitMap σ ≫ β = γ :=
    (preimage_source_comp F (scalarRestrictionUnitMap σ)
      (DerivedCategory.Plus.ι.map (η ≫ Φ)) (DerivedCategory.Plus.ι.map (ηR ≫ Φ))
      (map_comp_eq DerivedCategory.Plus.ι m (η ≫ Φ) (ηR ≫ Φ) hp).symm).symm
  have hv := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R => f (1 : R)) hh
  change β (σ 1) = γ 1 at hv
  rw [map_one] at hv
  exact hv.symm

/-- Source multiplication, the original unit square and the original comparison give
the native functional law before any concentration theorem. -/
theorem chosenEmbeddingUnitFunctional_source_smul
    (r : A) :
    letI := moduleCategoryLinearOfHom Z αA
    ∀ s : chosenEmbeddingUnitTraceSource R i p n,
      chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα (r • s) =
        (ModuleCat.restrictScalars σ).map (r • 𝟙 (ModuleCat.of A A)) ≫
          chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα s := by
  let := moduleCategoryLinearOfHom Z αA
  intro s
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let m : O ⟶ O := r • 𝟙 O
  have hs : (DerivedCategory.singleFunctor Z.Modules 0).map m ≫ s = r • s := by
    change (DerivedCategory.singleFunctor Z.Modules 0).map (r • 𝟙 O) ≫ s = r • s
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
      Linear.smul_comp, Category.id_comp]
  let U := moduleRestrictedDerivedStructureUnit Z σ αA (chosenEmbeddingBaseScalar R i p) hα
  let b := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
    ((ModuleCat.restrictScalars σ).map (r • 𝟙 (ModuleCat.of A A)))
  let t := (moduleGlobalSectionsFunctorOfHom Z
    (chosenEmbeddingBaseScalar R i p)).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).map m)
  have hU : b ≫ U = U ≫ t :=
    moduleRestrictedDerivedStructureUnit_source_scalar_square
      Z σ αA (chosenEmbeddingBaseScalar R i p) hα r
  have hΦ : chosenEmbeddingModuleSerreMap R ι i p a h n e (r • s) =
      t ≫ chosenEmbeddingModuleSerreMap R ι i p a h n e s := by
    rw [← hs]
    exact chosenEmbeddingModuleSerreMap_precomp R ι i p a h n e m s
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let Φ := chosenEmbeddingModuleSerreMap R ι i p a h n e s
  let Φr := chosenEmbeddingModuleSerreMap R ι i p a h n e (r • s)
  have hp : U ≫ Φr = b ≫ (U ≫ Φ) :=
    (congrArg (fun k => U ≫ k) hΦ).trans (unit_square_paste U b t Φ hU)
  have hm : DerivedCategory.Plus.ι.map (U ≫ Φr) =
      DerivedCategory.Plus.ι.map b ≫ DerivedCategory.Plus.ι.map (U ≫ Φ) :=
    (congrArg DerivedCategory.Plus.ι.map hp).trans
      (DerivedCategory.Plus.ι.map_comp b (U ≫ Φ))
  exact preimage_source_comp F ((ModuleCat.restrictScalars σ).map
    (r • 𝟙 (ModuleCat.of A A))) (DerivedCategory.Plus.ι.map (U ≫ Φ))
    (DerivedCategory.Plus.ι.map (U ≫ Φr)) hm

theorem chosenEmbeddingUnitFunctional_source_smul_apply
    (r : A) :
    letI := moduleCategoryLinearOfHom Z αA
    ∀ (s : chosenEmbeddingUnitTraceSource R i p n) (b : A),
      chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα (r • s) b =
        chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα s (r * b) := by
  let := moduleCategoryLinearOfHom Z αA
  intro s b
  have hh := chosenEmbeddingUnitFunctional_source_smul R ι i p a h n e σ αA hα r s
  exact congrArg
    (fun f : (ModuleCat.restrictScalars σ).obj (ModuleCat.of A A) ⟶ ModuleCat.of R R => f b) hh

/-- The original chosen-embedding trace valued in the actual native coinduced coefficient. -/
def chosenEmbeddingTraceCoinduced :
    letI := moduleCategoryLinearOfHom Z αA
    chosenEmbeddingUnitTraceSource R i p n →ₗ[A]
      (ModuleCat.coextendScalars σ).obj (ModuleCat.of R R) := by
  let := moduleCategoryLinearOfHom Z αA
  let E := ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)
  let β := chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα
  refine {
    toFun := fun s => E.symm (β s).hom
    map_add' := ?_
    map_smul' := ?_ }
  · intro s t
    apply E.injective
    apply LinearMap.ext
    intro b
    change β (s + t) b = β s b + β t b
    rw [_root_.map_add]
    rfl
  · intro r s
    apply E.injective
    apply LinearMap.ext
    intro b
    change β (r • s) (show A from b) = β s ((show A from b) * r)
    exact (chosenEmbeddingUnitFunctional_source_smul_apply R ι i p a h n e σ αA hα
      r s (show A from b)).trans (congrArg (β s) (mul_comm r (show A from b)))

/-- The native coinduction action evaluates the original base trace
at the original scalar action. -/
theorem chosenEmbeddingTraceCoinduced_apply
    (r : A) :
    letI := moduleCategoryLinearOfHom Z αA
    ∀ s : chosenEmbeddingUnitTraceSource R i p n,
      ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)
          (chosenEmbeddingTraceCoinduced R ι i p a h n e σ αA hα s) r =
        chosenEmbeddingTraceBase R ι i p a h n e (r • s) := by
  let := moduleCategoryLinearOfHom Z αA
  intro s
  change chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα s r = _
  rw [chosenEmbeddingTraceBase_eq_unitFunctional R ι i p a h n e σ αA hα,
    chosenEmbeddingUnitFunctional_source_smul_apply]
  rw [mul_one]

include hα in
/-- The same base trace is R-linear for the actual action restricted through sigma. -/
theorem chosenEmbeddingTraceBase_restricted_smul (r : R) :
    letI := moduleCategoryLinearOfHom Z αA
    ∀ s : chosenEmbeddingUnitTraceSource R i p n,
      chosenEmbeddingTraceBase R ι i p a h n e (σ r • s) =
        r • chosenEmbeddingTraceBase R ι i p a h n e s := by
  let := moduleCategoryLinearOfHom Z αA
  intro s
  let β := chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα s
  have hr := β.hom.map_smul r (1 : A)
  change β (σ r * (1 : A)) = r * β (1 : A) at hr
  rw [chosenEmbeddingTraceBase_eq_unitFunctional R ι i p a h n e σ αA hα (σ r • s),
    chosenEmbeddingUnitFunctional_source_smul_apply,
    chosenEmbeddingTraceBase_eq_unitFunctional R ι i p a h n e σ αA hα s]
  exact hr

/-- The original base trace as a linear map on the same source with actual restricted scalars. -/
def chosenEmbeddingTraceBaseLinear :
    letI := moduleCategoryLinearOfHom Z αA
    letI := Module.compHom (chosenEmbeddingUnitTraceSource R i p n) σ
    chosenEmbeddingUnitTraceSource R i p n →ₗ[R] R := by
  let := moduleCategoryLinearOfHom Z αA
  let := Module.compHom (chosenEmbeddingUnitTraceSource R i p n) σ
  refine { chosenEmbeddingTraceBase R ι i p a h n e with map_smul' := ?_ }
  intro r s
  exact chosenEmbeddingTraceBase_restricted_smul R ι i p a h n e σ αA hα r s

/-- The module-valued original comparison, expressed on actual restriction of derived A-sections. -/
def chosenEmbeddingModulePhi0 :
    chosenEmbeddingUnitTraceSource R i p n →+
      ((ModuleCat.restrictScalars σ).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj (moduleDerivedStructure Z αA)) ⟶
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) := by
  exact (Preadditive.leftComp _
      (moduleDerivedStructureRestrictionIso Z σ αA (chosenEmbeddingBaseScalar R i p) hα).inv).comp
    (DerivedCategory.Plus.ι.mapAddHom.comp (chosenEmbeddingModuleSerreMap R ι i p a h n e))

/-- The same functional is exactly Phi0 after restriction of the original eta_A,
with the original exact-single normalization displayed. -/
theorem chosenEmbeddingUnitFunctional_map
    (s : chosenEmbeddingUnitTraceSource R i p n) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα s) =
      ((ModuleCat.restrictScalars σ).mapDerivedCategorySingleFunctor 0).inv.app
          (ModuleCat.of A A) ≫
        (ModuleCat.restrictScalars σ).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit Z αA)) ≫
        chosenEmbeddingModulePhi0 R ι i p a h n e σ αA hα s := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let η := moduleRestrictedDerivedStructureUnit Z σ αA (chosenEmbeddingBaseScalar R i p) hα
  let Φ := chosenEmbeddingModuleSerreMap R ι i p a h n e s
  exact (F.map_preimage (DerivedCategory.Plus.ι.map (η ≫ Φ))).trans
    (mapped_pairing_factor DerivedCategory.Plus.ι η Φ
      (((ModuleCat.restrictScalars σ).mapDerivedCategorySingleFunctor 0).inv.app
        (ModuleCat.of A A))
      ((ModuleCat.restrictScalars σ).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit Z αA)))
      (moduleDerivedStructureRestrictionIso Z σ αA (chosenEmbeddingBaseScalar R i p) hα).inv
      (moduleRestrictedDerivedStructureUnit_full
        Z σ αA (chosenEmbeddingBaseScalar R i p) hα))

/-- The chosen-embedding coinduced trace is the actual dual of the same original unit. -/
theorem chosenEmbeddingTraceCoinduced_eq_original_unit (r : A) :
    letI := moduleCategoryLinearOfHom Z αA
    ∀ s : chosenEmbeddingUnitTraceSource R i p n,
      ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)
          (chosenEmbeddingTraceCoinduced R ι i p a h n e σ αA hα s) r =
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).preimage
          (((ModuleCat.restrictScalars σ).mapDerivedCategorySingleFunctor 0).inv.app
              (ModuleCat.of A A) ≫
            (ModuleCat.restrictScalars σ).mapDerivedCategory.map
              (DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit Z αA)) ≫
            chosenEmbeddingModulePhi0 R ι i p a h n e σ αA hα s)) r := by
  let := moduleCategoryLinearOfHom Z αA
  intro s
  change chosenEmbeddingUnitFunctional R ι i p a h n e σ αA hα s r = _
  rw [← chosenEmbeddingUnitFunctional_map R ι i p a h n e σ αA hα s,
    CategoryTheory.Functor.preimage_map]

omit [IsClosedImmersion i] in
/-- The actual geometric triangle derives scalar compatibility from the original ΓSpec maps. -/
theorem chosenEmbeddingBaseScalar_eq_of_triangle
    (g : Z ⟶ Spec (.of A))
    (hg : i ≫ p = g ≫ Spec.map (CommRingCat.ofHom σ)) :
    chosenEmbeddingBaseScalar R i p =
      (g.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom).comp σ := by
  ext r
  have hΓ := ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)
  have hΓr := congrArg
    (fun f : CommRingCat.of R ⟶ Γ(Spec (.of A), ⊤) => f.hom r) hΓ
  change (i ≫ p).appTop ((ΓSpecIso (.of R)).inv r) =
    g.appTop ((ΓSpecIso (.of A)).inv (σ r))
  rw [hg, Scheme.Hom.comp_appTop]
  exact congrArg g.appTop hΓr.symm

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived category of `R`-modules for the geometric structure-unit comparison. -/
local instance traceModuleDerivedFinal (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

/-- The actual geometric structure unit and the original module structural unit agree
under the existing derived global-sections comparison. -/
theorem moduleDerivedStructureUnit_pushforward
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} (g : Y ⟶ X)
    (α : R →+* Γ(X, ⊤)) :
    moduleDerivedStructureUnit X α ≫
        (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          (moduleDerivedPushforwardUnit X g) =
      moduleDerivedStructureUnit Y (g.appTop.hom.comp α) ≫
        (moduleDerivedGlobalSectionsPushforwardCompIso g α).hom.app
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
            (SheafOfModules.unit Y.ringCatSheaf)) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let FX := moduleGlobalSectionsFunctorOfHom X α
  let FY := moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0
  let φ : OX ⟶ (pushforward g).obj OY :=
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  let E := modulePushforwardGlobalSectionsIso g α
  let C := moduleDerivedGlobalSectionsPushforwardCompIso g α
  let K := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY
  have hc : moduleStructuralSectionsMap X α ≫ FX.map φ ≫ E.hom.app OY =
      moduleStructuralSectionsMap Y (g.appTop.hom.comp α) := by
    apply ConcreteCategory.hom_ext
    intro r
    rfl
  exact geometric_unit_paste S (moduleStructuralSectionsMap X α)
    (FX.map φ ≫ E.hom.app OY) (moduleStructuralSectionsMap Y (g.appTop.hom.comp α))
    (FX.rightDerivedSingleUnit OX)
    (FX.rightDerivedFunctorPlus.map (moduleDerivedPushforwardUnit X g))
    (C.app K) (FY.rightDerivedSingleUnit OY) hc
    (moduleDerivedGlobalSectionsPushforwardCompIso_coefficientUnit g α φ)

variable (R : Type u) [CommRing R] (ι : Type u)
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ Spec (.of R)) (a : P ⟶ ProjectiveSpace R ι)
    (h : IsPullback a p (ProjectiveSpace.toSpec R ι) (𝟙 (Spec (.of R))))
    (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- The base-unit trace is the original geometric structure unit followed by the SAME
chosen-embedding Serre map, transported by original derived sections and affine normalization. -/
theorem chosenEmbeddingTraceBase_geometric_unit
    (s : chosenEmbeddingUnitTraceSource R i p n) :
    moduleDerivedStructureUnit Z (chosenEmbeddingBaseScalar R i p) ≫
        chosenEmbeddingModuleSerreMap R ι i p a h n e s =
      (affineDerivedStructureTargetIso (.of R)).inv ≫
        (moduleGlobalSectionsFunctorOfHom (Spec (.of R))
          (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus.map
            (moduleDerivedPushforwardUnit (Spec (.of R)) (i ≫ p) ≫
              chosenEmbeddingSerreMapPlus R ι i p a h n e s) ≫
        (affineDerivedStructureTargetIso (.of R)).hom := by
  let Y := Spec (.of R)
  let α := (ΓSpecIso (.of R)).inv.hom
  let F := moduleGlobalSectionsFunctorOfHom Y α
  let C := moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ p) α
  let T := affineDerivedStructureTargetIso (.of R)
  have hη : moduleDerivedStructureUnit Y α = T.inv := by
    apply (cancel_mono T.hom).mp
    rw [affineDerivedStructureTargetIso_unit, T.inv_hom_id]
  have hcomp := moduleDerivedStructureUnit_pushforward (i ≫ p) α
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let c := C.hom.app ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj O)
  let u := moduleDerivedStructureUnit Z (chosenEmbeddingBaseScalar R i p)
  let g := moduleDerivedPushforwardUnit (Spec (.of R)) (i ≫ p)
  have hh : u ≫ c = T.inv ≫ F.rightDerivedFunctorPlus.map g :=
    hcomp.symm.trans (congrArg (fun η => η ≫ F.rightDerivedFunctorPlus.map g) hη)
  exact geometric_trace_paste F.rightDerivedFunctorPlus g
    (chosenEmbeddingSerreMapPlus R ι i p a h n e s) u c T.inv T.hom hh

end AlgebraicGeometry.Scheme.Cohomology
