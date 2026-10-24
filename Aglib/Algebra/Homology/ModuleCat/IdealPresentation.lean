/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FinitePresentation
public import Aglib.Algebra.Homology.MappingCone.Homology
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# A finite three-term presentation of an ideal quotient

A finite presentation of an ideal gives a complex `P₂ → P₁ → R` in
degrees `-2`, `-1`, and `0`, with the original quotient augmentation to
`R/I`. It is exact at `P₁`, `R`, and `R/I`; no exactness is asserted at
`P₂`. Its augmentation cone is cohomologically at most `-3`.

For every `a ∈ I`, projectivity of `P₁` constructs the original two-stage
identity `a id = d₂ h₁ + h₀ d₁`. This is the part of the homotopy which
annihilates degree-minus-one homology after additive base change.

The current consumer is the original residue-field Hom comparison for a
proper birational normal surface.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Finite free generators and relations for the actual ideal as an `R`-module. -/
structure IdealPresentation (I : Ideal R) where
  /-- Number of original ideal generators. -/
  rank₁ : ℕ
  /-- Number of relations between those generators. -/
  rank₂ : ℕ
  /-- The original surjection onto the ideal. -/
  generators : (Fin rank₁ → R) →ₗ[R] I
  /-- A finite free cover of its kernel. -/
  relations : (Fin rank₂ → R) →ₗ[R] (Fin rank₁ → R)
  /-- Every original ideal element has a generator lift. -/
  generators_surjective : Function.Surjective generators
  /-- Exactness at the first free module only. -/
  exact : Function.Exact relations generators

namespace IdealPresentation

variable {I : Ideal R} (P : IdealPresentation I)

/-- A Noetherian ideal has a finite presentation by the native module theorem. -/
theorem nonempty [IsNoetherianRing R] (I : Ideal R) : Nonempty (IdealPresentation I) := by
  let : Module.FinitePresentation R I := Module.finitePresentation_of_finite R I
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' R I
  exact ⟨⟨n, m, f, g, hf, hg⟩⟩

/-- A chosen actual finite presentation of the ideal. -/
def ofNoetherian [IsNoetherianRing R] (I : Ideal R) : IdealPresentation I :=
  (nonempty I).some

/-- The first differential has the original base ring as its literal target. -/
def firstDifferential : (Fin P.rank₁ → R) →ₗ[R] R := I.subtype.comp P.generators

@[simp]
theorem firstDifferential_apply (x : Fin P.rank₁ → R) :
    P.firstDifferential x = (P.generators x : R) := rfl

/-- The two consecutive original differentials compose to zero. -/
theorem firstDifferential_comp_relations : P.firstDifferential.comp P.relations = 0 := by
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (P.exact.apply_apply_eq_zero x)

/-- Exactness at the first free term is preserved by the original ideal inclusion. -/
theorem exact_firstDifferential : Function.Exact P.relations P.firstDifferential := by
  intro x
  constructor
  · intro hx
    exact (P.exact x).mp (Subtype.ext hx)
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun P.firstDifferential_comp_relations y

/-- The range of the original first differential is precisely the original ideal. -/
theorem range_firstDifferential : LinearMap.range P.firstDifferential = I := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact (P.generators x).property
  · intro ha
    obtain ⟨x, hx⟩ := P.generators_surjective ⟨a, ha⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- Exactness at the original ring and the actual quotient projection. -/
theorem exact_quotient : Function.Exact P.firstDifferential I.mkQ := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, P.range_firstDifferential]

/-- Actual annihilating homotopies in the two degrees needed after additive
base change. No homotopy identity at the bottom free term is claimed. -/
theorem exists_annihilating_homotopy (a : R) (ha : a ∈ I) :
    ∃ (h₀ : R →ₗ[R] (Fin P.rank₁ → R))
      (h₁ : (Fin P.rank₁ → R) →ₗ[R] (Fin P.rank₂ → R)),
      P.firstDifferential.comp h₀ = a • LinearMap.id ∧
      P.relations.comp h₁ + h₀.comp P.firstDifferential = a • LinearMap.id := by
  obtain ⟨v, hv⟩ := P.generators_surjective ⟨a, ha⟩
  have hv' : P.firstDifferential v = a := congrArg Subtype.val hv
  let h₀ : R →ₗ[R] (Fin P.rank₁ → R) := LinearMap.toSpanSingleton R _ v
  have h₀d : P.firstDifferential.comp h₀ = a • LinearMap.id := by
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, h₀, LinearMap.toSpanSingleton_apply,
      map_smul, hv', LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    exact mul_comm r a
  let k : (Fin P.rank₁ → R) →ₗ[R] LinearMap.ker P.firstDifferential :=
    (a • LinearMap.id - h₀.comp P.firstDifferential).codRestrict _ (by
      intro x
      change P.firstDifferential (a • x - P.firstDifferential x • v) = 0
      rw [map_sub, map_smul, map_smul, hv']
      simp only [smul_eq_mul, mul_comm a, sub_self])
  let r : (Fin P.rank₂ → R) →ₗ[R] LinearMap.ker P.firstDifferential :=
    P.relations.codRestrict _ (fun x => LinearMap.congr_fun P.firstDifferential_comp_relations x)
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨y, hy⟩ := (P.exact_firstDifferential x.val).mp x.property
    exact ⟨y, Subtype.ext hy⟩
  obtain ⟨h₁, hh₁⟩ := Module.projective_lifting_property r k hr
  refine ⟨h₀, h₁, h₀d, ?_⟩
  have hrel : P.relations.comp h₁ = a • LinearMap.id - h₀.comp P.firstDifferential := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun l : (Fin P.rank₁ → R) →ₗ[R] LinearMap.ker P.firstDifferential =>
      (l x).val) hh₁
  rw [hrel]
  exact sub_add_cancel _ _

/-- The three literal terms, zero elsewhere. -/
def term : ℤ → ModuleCat.{u} R
  | .ofNat 0 => ModuleCat.of R R
  | .negSucc 0 => ModuleCat.of R (Fin P.rank₁ → R)
  | .negSucc 1 => ModuleCat.of R (Fin P.rank₂ → R)
  | _ => 0

/-- The two original differentials between the literal terms. -/
def differential : ∀ n : ℤ, P.term n ⟶ P.term (n + 1)
  | .negSucc 0 => ModuleCat.ofHom P.firstDifferential
  | .negSucc 1 => ModuleCat.ofHom P.relations
  | .ofNat _ => 0
  | .negSucc (_ + 2) => 0

/-- The literal consecutive differentials of the three-term complex compose to zero. -/
theorem differential_comp (n : ℤ) :
    P.differential n ≫ P.differential (n + 1) = 0 := by
  cases n with
  | ofNat n => simp [differential]
  | negSucc n =>
    cases n with
    | zero => simp [differential]
    | succ n =>
      cases n with
      | zero => exact ModuleCat.hom_ext P.firstDifferential_comp_relations
      | succ n => simp [differential]

/-- The finite three-term cochain complex; this need not resolve the quotient. -/
def cochain : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of P.term P.differential (differential_comp P)

@[simp]
theorem cochain_X_zero : P.cochain.X 0 = ModuleCat.of R R := rfl

@[simp]
theorem cochain_X_neg_one : P.cochain.X (-1) = ModuleCat.of R (Fin P.rank₁ → R) := rfl

@[simp]
theorem cochain_X_neg_two : P.cochain.X (-2) = ModuleCat.of R (Fin P.rank₂ → R) := rfl

@[simp]
theorem cochain_d_neg_one_zero : P.cochain.d (-1) 0 = ModuleCat.ofHom P.firstDifferential := by
  change CochainComplex.of.d P.term P.differential (-1) ((-1 : ℤ) + 1) = _
  rw [CochainComplex.of_d]
  rfl

@[simp]
theorem cochain_d_neg_two_neg_one : P.cochain.d (-2) (-1) = ModuleCat.ofHom P.relations := by
  change CochainComplex.of.d P.term P.differential (-2) ((-2 : ℤ) + 1) = _
  rw [CochainComplex.of_d]
  rfl

/-- Outside the three indicated degrees the actual term is zero. -/
theorem cochain_isZero_X (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ -1) (h₂ : n ≠ -2) :
    IsZero (P.cochain.X n) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact (h₀ rfl).elim
    | succ n =>
      change IsZero (0 : ModuleCat.{u} R)
      exact CategoryTheory.Limits.isZero_zero _
  | negSucc n =>
    cases n with
    | zero => exact (h₁ rfl).elim
    | succ n =>
      cases n with
      | zero => exact (h₂ rfl).elim
      | succ n =>
        change IsZero (0 : ModuleCat.{u} R)
        exact CategoryTheory.Limits.isZero_zero _

instance : P.cochain.IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  exact P.cochain_isZero_X n (by omega) (by omega) (by omega)

instance : P.cochain.IsStrictlyGE (-2) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact P.cochain_isZero_X n (by omega) (by omega) (by omega)

/-- Every actual term is finite free. -/
theorem cochain_finite_free (n : ℤ) :
    Module.Finite R (P.cochain.X n) ∧ Module.Free R (P.cochain.X n) := by
  by_cases h₀ : n = 0
  · subst n
    change Module.Finite R R ∧ Module.Free R R
    exact ⟨inferInstance, inferInstance⟩
  by_cases h₁ : n = -1
  · subst n
    change Module.Finite R (Fin P.rank₁ → R) ∧ Module.Free R (Fin P.rank₁ → R)
    exact ⟨inferInstance, inferInstance⟩
  by_cases h₂ : n = -2
  · subst n
    change Module.Finite R (Fin P.rank₂ → R) ∧ Module.Free R (Fin P.rank₂ → R)
    exact ⟨inferInstance, inferInstance⟩
  let := ModuleCat.subsingleton_of_isZero (P.cochain_isZero_X n h₀ h₁ h₂)
  exact ⟨inferInstance, inferInstance⟩

instance : P.cochain.IsKProjective := by
  let (n : ℤ) : Module.Free R (P.cochain.X n) := (P.cochain_finite_free n).2
  let (n : ℤ) : Projective (P.cochain.X n) := inferInstance
  exact CochainComplex.isKProjective_of_projective _ 0

/-- The original augmentation to the quotient single in degree zero. -/
def augmentation : P.cochain ⟶
    (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R (R ⧸ I)) :=
  HomologicalComplex.mkHomToSingle (ModuleCat.ofHom I.mkQ) (by
    intro i hi
    have hi' : i = -1 := by change i + 1 = 0 at hi; omega
    subst i
    rw [P.cochain_d_neg_one_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero I).mpr (P.generators x).property)

/-- In degree zero the augmentation is the actual quotient projection. -/
@[simp]
theorem augmentation_f_zero : P.augmentation.f 0 = ModuleCat.ofHom I.mkQ := by
  rw [augmentation, HomologicalComplex.mkHomToSingle_f]
  exact Category.comp_id _

/-- The first negative homology vanishes by the original generator relations. -/
theorem cochain_exactAt_neg_one : P.cochain.ExactAt (-1) := by
  rw [HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  change P.firstDifferential x = 0 at hx
  exact (P.exact_firstDifferential x).mp hx

/-- The actual augmentation induces an isomorphism on degree-zero homology. -/
instance augmentation_quasiIsoAt_zero : QuasiIsoAt P.augmentation 0 := by
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  rw [ShortComplex.quasiIso_iff_of_zeros']
  · constructor
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      change I.mkQ x = 0 at hx
      exact (P.exact_quotient x).mp hx
    · change Epi (P.augmentation.f 0)
      rw [P.augmentation_f_zero, ModuleCat.epi_iff_surjective]
      exact Submodule.mkQ_surjective I
  · simp [cochain, CochainComplex.of.d, differential]
  · simp
  · simp

/-- The original augmentation cone has no homology above degree minus three.
This bound does not assert that the augmentation is a quasi-isomorphism. -/
instance augmentation_cone_isLE :
    (CochainComplex.mappingCone P.augmentation).IsLE (-3) := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  by_cases hi₂ : i = -2
  · subst i
    apply (CochainComplex.mappingCone.homologyRightShortComplex_exact P.augmentation (-2)).isZero_X₂
    · exact (isZero_single_obj_homology (.up ℤ) 0
        (ModuleCat.of R (R ⧸ I)) (-2) (by norm_num)).eq_of_src _ _
    · exact P.cochain_exactAt_neg_one.isZero_homology.eq_of_tgt _ _
  by_cases hi₁ : i = -1
  · subst i
    let := HasDerivedCategory.standard (ModuleCat.{u} R)
    apply (CochainComplex.mappingCone.homologyRightShortComplex_exact P.augmentation (-1)).isZero_X₂
    · exact (isZero_single_obj_homology (.up ℤ) 0
        (ModuleCat.of R (R ⧸ I)) (-1) (by norm_num)).eq_of_src _ _
    · change CochainComplex.homologyδOfTriangle
        (CochainComplex.mappingCone.triangle P.augmentation) (-1) 0 = 0
      apply (cancel_mono (homologyMap P.augmentation 0)).mp
      rw [zero_comp]
      exact CochainComplex.homologyδOfTriangle_homologyMap
        (CochainComplex.mappingCone.triangle P.augmentation)
        (DerivedCategory.mappingCone_triangle_distinguished P.augmentation) (-1) 0
  by_cases hi₀ : i = 0
  · subst i
    exact CochainComplex.mappingCone.isZero_homology_of_epi P.augmentation 0
      (P.cochain.exactAt_of_isLE 0 1 (by norm_num)).isZero_homology
  apply (CochainComplex.mappingCone.homologyRightShortComplex_exact P.augmentation i).isZero_X₂
  · exact (isZero_single_obj_homology (.up ℤ) 0
      (ModuleCat.of R (R ⧸ I)) i (by omega)).eq_of_src _ _
  · exact (P.cochain.exactAt_of_isLE 0 (i + 1) (by omega)).isZero_homology.eq_of_tgt _ _

section Derived

universe v

variable [HasDerivedCategory.{v} (ModuleCat.{u} R)]

/-- The original augmentation computes Hom into every object bounded below
by minus one, using the actual cone bound. -/
theorem augmentation_precomp_bijective (K : DerivedCategory (ModuleCat.{u} R))
    [K.IsGE (-1)] :
    Function.Bijective (fun f :
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (R ⧸ I)) ⟶ K =>
        DerivedCategory.Q.map P.augmentation ≫ f) := by
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle P.augmentation)
  have hT : T ∈ distTriang _ :=
    DerivedCategory.mappingCone_triangle_distinguished P.augmentation
  let : T.obj₃.IsLE (-3) := by
    change (DerivedCategory.Q.obj (CochainComplex.mappingCone P.augmentation)).IsLE (-3)
    infer_instance
  constructor
  · intro f g hfg
    change DerivedCategory.Q.map P.augmentation ≫ f =
      DerivedCategory.Q.map P.augmentation ≫ g at hfg
    have hz : T.mor₁ ≫ (f - g) = 0 := by
      change DerivedCategory.Q.map P.augmentation ≫ (f - g) = 0
      rw [Preadditive.comp_sub, hfg, sub_self]
    obtain ⟨d, hd⟩ := T.yoneda_exact₂ hT (f - g) hz
    have hd₀ : d = 0 := DerivedCategory.TStructure.t.zero d (-3) (-1) (by norm_num)
    apply sub_eq_zero.mp
    rw [hd, hd₀, comp_zero]
  · intro f
    let : T.invRotate.obj₁.IsLE (-2) := by
      change (T.obj₃⟦(-1 : ℤ)⟧).IsLE (-2)
      exact DerivedCategory.TStructure.t.isLE_shift T.obj₃ (-3) (-1) (-2) (by norm_num)
    obtain ⟨g, hg⟩ := T.invRotate.yoneda_exact₂
      (CategoryTheory.Pretriangulated.inv_rot_of_distTriang T hT) f
      (DerivedCategory.TStructure.t.zero _ (-2) (-1) (by norm_num))
    exact ⟨g, hg.symm⟩

/-- The additive Hom comparison retains precomposition with the literal
augmentation map, rather than an unspecified model isomorphism. -/
def augmentationHomAddEquiv (K : DerivedCategory (ModuleCat.{u} R)) [K.IsGE (-1)] :
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (R ⧸ I)) ⟶ K) ≃+ (DerivedCategory.Q.obj P.cochain ⟶ K) := by
  let p : ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (R ⧸ I)) ⟶ K) →+ (DerivedCategory.Q.obj P.cochain ⟶ K) := {
    toFun f := DerivedCategory.Q.map P.augmentation ≫ f
    map_zero' := comp_zero
    map_add' f g := Preadditive.comp_add _ _ _ (DerivedCategory.Q.map P.augmentation) f g }
  exact AddEquiv.ofBijective p (P.augmentation_precomp_bijective K)

@[simp]
theorem augmentationHomAddEquiv_apply (K : DerivedCategory (ModuleCat.{u} R))
    [K.IsGE (-1)] (f : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (R ⧸ I)) ⟶ K) :
    P.augmentationHomAddEquiv K f = DerivedCategory.Q.map P.augmentation ≫ f := rfl

end Derived

section AdditiveImage

universe v w

variable {D : Type v} [Category.{w} D] [Abelian D]
  (F : ModuleCat.{u} R ⥤ D) [F.Additive]

/-- Right exactness suffices to retain the degree-zero quotient comparison.
No exactness of the left adjoint is used. -/
theorem map_augmentation_quasiIsoAt_zero [PreservesFiniteColimits F] :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℤ)).map P.augmentation) 0 := by
  let S := ShortComplex.mk (ModuleCat.ofHom P.firstDifferential)
    (ModuleCat.ofHom I.mkQ) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero I).mpr (P.generators x).property)
  have hS : S.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact (P.exact_quotient x).mp hx
  let : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective I)
  have hmap : (S.map F).Exact :=
    hS.map_of_epi_of_preservesCokernel F inferInstance inferInstance
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  rw [ShortComplex.quasiIso_iff_of_zeros']
  · constructor
    · refine ShortComplex.exact_of_iso
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_) hmap
      · change 𝟙 _ ≫ F.map (P.cochain.d (-1) 0) =
          F.map (ModuleCat.ofHom P.firstDifferential) ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id, P.cochain_d_neg_one_zero]
      · change 𝟙 _ ≫ F.map (P.augmentation.f 0) = F.map (ModuleCat.ofHom I.mkQ) ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id, P.augmentation_f_zero]
    · change Epi (F.map (P.augmentation.f 0))
      rw [P.augmentation_f_zero]
      exact inferInstanceAs (Epi (F.map S.g))
  · change F.map (P.cochain.d 0 1) = 0
    simp [cochain, CochainComplex.of.d, differential]
  · change F.map _ = 0
    simp
  · change F.map _ = 0
    simp

/-- Homology in degree zero of the actual termwise image is the image of
the original quotient, through the original augmentation. -/
def mappedHomologyZeroIso [PreservesFiniteColimits F] :
    ((F.mapHomologicalComplex (.up ℤ)).obj P.cochain).homology 0 ≅
      F.obj (ModuleCat.of R (R ⧸ I)) := by
  letI := P.map_augmentation_quasiIsoAt_zero F
  exact asIso (homologyMap ((F.mapHomologicalComplex (.up ℤ)).map P.augmentation) 0) ≪≫
    (HomologicalComplex.homologyFunctor D (.up ℤ) 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app
        (ModuleCat.of R (R ⧸ I))) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 _

variable [CategoryTheory.Linear R D] [F.Linear R]

private theorem shortComplex_scalar_homology_eq_zero (S : ShortComplex D) (a : R)
    (h₀ : S.X₃ ⟶ S.X₂) (h₁ : S.X₂ ⟶ S.X₁)
    (h : a • 𝟙 S.X₂ = S.g ≫ h₀ + h₁ ≫ S.f) : a • 𝟙 S.homology = 0 := by
  apply (cancel_epi S.homologyπ).mp
  apply (cancel_mono S.homologyι).mp
  calc
    (S.homologyπ ≫ (a • 𝟙 S.homology)) ≫ S.homologyι =
        S.iCycles ≫ (a • 𝟙 S.X₂) ≫ S.pOpcycles := by
      simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id,
        Category.id_comp, S.homology_π_ι]
    _ = 0 := by
      rw [h]
      simp only [Preadditive.add_comp, Category.assoc, S.iCycles_g_assoc,
        S.f_pOpcycles, comp_zero, zero_comp, add_zero]
    _ = (S.homologyπ ≫ 0) ≫ S.homologyι := by simp

/-- Every original ideal scalar annihilates degree-minus-one homology after
an arbitrary additive linear functor. The proof uses the actual two-stage
homotopy and imposes no exactness or flatness condition on that functor. -/
theorem mappedHomology_neg_one_scalar_eq_zero (a : R) (ha : a ∈ I) :
    a • 𝟙 (((F.mapHomologicalComplex (.up ℤ)).obj P.cochain).homology (-1)) = 0 := by
  obtain ⟨h₀, h₁, _, h₁eq⟩ := P.exists_annihilating_homotopy a ha
  let K := (F.mapHomologicalComplex (.up ℤ)).obj P.cochain
  let S : ShortComplex D := ShortComplex.mk (F.map (ModuleCat.ofHom P.relations))
    (F.map (ModuleCat.ofHom P.firstDifferential)) (by
      have hz : ModuleCat.ofHom P.relations ≫ ModuleCat.ofHom P.firstDifferential = 0 :=
        ModuleCat.hom_ext P.firstDifferential_comp_relations
      rw [← F.map_comp, hz, F.map_zero])
  have hmid : a • 𝟙 S.X₂ =
      S.g ≫ F.map (ModuleCat.ofHom h₀) + F.map (ModuleCat.ofHom h₁) ≫ S.f := by
    have h : a • 𝟙 (ModuleCat.of R (Fin P.rank₁ → R)) =
        ModuleCat.ofHom P.firstDifferential ≫ ModuleCat.ofHom h₀ +
          ModuleCat.ofHom h₁ ≫ ModuleCat.ofHom P.relations := by
      apply ModuleCat.hom_ext
      change a • LinearMap.id = h₀.comp P.firstDifferential + P.relations.comp h₁
      rw [add_comm]
      exact h₁eq.symm
    change a • 𝟙 (F.obj (ModuleCat.of R (Fin P.rank₁ → R))) =
      F.map (ModuleCat.ofHom P.firstDifferential) ≫ F.map (ModuleCat.ofHom h₀) +
        F.map (ModuleCat.ofHom h₁) ≫ F.map (ModuleCat.ofHom P.relations)
    have hm := congrArg F.map h
    rw [F.map_smul, F.map_id, F.map_add, F.map_comp, F.map_comp] at hm
    exact hm
  have hzero := shortComplex_scalar_homology_eq_zero S a
    (F.map (ModuleCat.ofHom h₀)) (F.map (ModuleCat.ofHom h₁)) hmid
  let es : K.sc' (-2) (-1) 0 ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        change 𝟙 _ ≫ F.map (ModuleCat.ofHom P.relations) =
          F.map (P.cochain.d (-2) (-1)) ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id, P.cochain_d_neg_two_neg_one])
      (by
        change 𝟙 _ ≫ F.map (ModuleCat.ofHom P.firstDifferential) =
          F.map (P.cochain.d (-1) 0) ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id, P.cochain_d_neg_one_zero])
  let e : K.homology (-1) ≅ S.homology :=
    K.homologyIsoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    (ShortComplex.homologyFunctor D).mapIso es
  have htransport := congrArg (fun g : S.homology ⟶ S.homology => (e.hom ≫ g) ≫ e.inv) hzero
  rw [Linear.comp_smul, Category.comp_id, Linear.smul_comp, e.hom_inv_id] at htransport
  simpa only [comp_zero, zero_comp] using htransport

end AdditiveImage

end IdealPresentation

end ModuleCat
