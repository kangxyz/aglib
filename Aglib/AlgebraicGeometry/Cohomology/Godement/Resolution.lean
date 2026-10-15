/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.First
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.SingleHomology

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementResolution.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 387]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The functorial Godement resolution on arbitrary scheme module sheaves

The quotient of the monic natural germ map is an actual exact functor. Its
iterates supply the original Godement terms and quotient/unit differentials.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The actual functorial cokernel of the original product Godement unit. -/
def godementCokernel (X : Scheme.{u}) : X.Modules ⥤ X.Modules where
  obj M := cokernel ((godementFirstProductUnit X).app M)
  map {M N} f := cokernel.map _ _ f ((godementFirstProduct X).map f)
    ((godementFirstProductUnit X).naturality f).symm
  map_id M := by
    apply (cancel_epi (cokernel.π _)).mp
    simp
  map_comp f g := by
    apply (cancel_epi (cokernel.π _)).mp
    simp [Functor.map_comp]

/-- The original quotient map, natural in the module sheaf. -/
def godementQuotient (X : Scheme.{u}) : godementFirstProduct X ⟶ godementCokernel X where
  app M := cokernel.π ((godementFirstProductUnit X).app M)
  naturality f := by simp [godementCokernel]

@[reassoc (attr := simp)]
theorem godementUnit_quotient (X : Scheme.{u}) (M : X.Modules) :
    (godementFirstProductUnit X).app M ≫ (godementQuotient X).app M = 0 :=
  cokernel.condition _

instance godementQuotient_epi (X : Scheme.{u}) (M : X.Modules) :
    Epi ((godementQuotient X).app M) := inferInstanceAs (Epi (cokernel.π _))

instance godementCokernel_additive (X : Scheme.{u}) : (godementCokernel X).Additive where
  map_add {M N} f g := by
    apply (cancel_epi (cokernel.π _)).mp
    simp [godementCokernel, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

/-- The defining short exact sequence is supplied by the actual cokernel. -/
theorem godementUnit_shortExact (X : Scheme.{u}) (M : X.Modules) :
    (ShortComplex.mk ((godementFirstProductUnit X).app M)
      ((godementQuotient X).app M) (godementUnit_quotient X M)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _

/-- The unit gives an actual map of every short complex to its Godement image. -/
def godementUnitRow (X : Scheme.{u}) (S : ShortComplex X.Modules) :
    S ⟶ S.map (godementFirstProduct X) where
  τ₁ := (godementFirstProductUnit X).app S.X₁
  τ₂ := (godementFirstProductUnit X).app S.X₂
  τ₃ := (godementFirstProductUnit X).app S.X₃
  comm₁₂ := ((godementFirstProductUnit X).naturality S.f).symm
  comm₂₃ := ((godementFirstProductUnit X).naturality S.g).symm

/-- The quotient gives an actual map from the Godement row to the cokernel row. -/
def godementQuotientRow (X : Scheme.{u}) (S : ShortComplex X.Modules) :
    S.map (godementFirstProduct X) ⟶ S.map (godementCokernel X) where
  τ₁ := (godementQuotient X).app S.X₁
  τ₂ := (godementQuotient X).app S.X₂
  τ₃ := (godementQuotient X).app S.X₃
  comm₁₂ := ((godementQuotient X).naturality S.f).symm
  comm₂₃ := ((godementQuotient X).naturality S.g).symm

@[simp]
theorem godementUnitRow_quotientRow (X : Scheme.{u}) (S : ShortComplex X.Modules) :
    godementUnitRow X S ≫ godementQuotientRow X S = 0 := by
  ext1 <;> exact godementUnit_quotient X _

instance godementUnitRow_mono (X : Scheme.{u}) (S : ShortComplex X.Modules) :
    Mono (godementUnitRow X S) where
  right_cancellation {T} f g h := by
    ext1
    · apply (cancel_mono ((godementFirstProductUnit X).app S.X₁)).mp
      exact congrArg ShortComplex.Hom.τ₁ h
    · apply (cancel_mono ((godementFirstProductUnit X).app S.X₂)).mp
      exact congrArg ShortComplex.Hom.τ₂ h
    · apply (cancel_mono ((godementFirstProductUnit X).app S.X₃)).mp
      exact congrArg ShortComplex.Hom.τ₃ h

/-- The cokernel of the unit row is the row of the actual objectwise cokernels. -/
def godementQuotientRowIsCokernel (X : Scheme.{u}) (S : ShortComplex X.Modules) :
    IsColimit (CokernelCofork.ofπ (godementQuotientRow X S)
      (godementUnitRow_quotientRow X S)) := by
  apply ShortComplex.isColimitOfIsColimitπ
  · refine (CokernelCofork.isColimitMapCoconeEquiv _ ShortComplex.π₁).symm ?_
    exact cokernelIsCokernel _
  · refine (CokernelCofork.isColimitMapCoconeEquiv _ ShortComplex.π₂).symm ?_
    exact cokernelIsCokernel _
  · refine (CokernelCofork.isColimitMapCoconeEquiv _ ShortComplex.π₃).symm ?_
    exact cokernelIsCokernel _

/-- The actual snake diagram for an original short exact sequence and its Godement image. -/
def godementSnake (X : Scheme.{u}) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    ShortComplex.SnakeInput X.Modules where
  L₀ := kernel (godementUnitRow X S)
  L₁ := S
  L₂ := S.map (godementFirstProduct X)
  L₃ := S.map (godementCokernel X)
  v₀₁ := kernel.ι (godementUnitRow X S)
  v₁₂ := godementUnitRow X S
  v₂₃ := godementQuotientRow X S
  w₀₂ := kernel.condition _
  w₁₃ := godementUnitRow_quotientRow X S
  h₀ := kernelIsKernel _
  h₃ := godementQuotientRowIsCokernel X S
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := godementFirstProduct_map_exact S hS.exact
  mono_L₂_f := by
    have := hS.mono_f
    exact inferInstanceAs (Mono ((godementFirstProduct X).map S.f))

/-- No exactness of arbitrary sheaf products is used: this is the cokernel row of the
actual diagram of original and Godement short exact sequences. -/
theorem godementCokernel_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (godementCokernel X)).ShortExact := by
  let D := godementSnake X S hS
  have hzero : IsZero D.L₀.X₃ := by
    exact ShortComplex.π₃.map_isZero (isZero_kernel_of_mono (godementUnitRow X S))
  have hδ : D.δ = 0 := hzero.eq_of_src _ _
  refine { exact := D.L₃_exact, mono_f := ?_, epi_g := ?_ }
  · exact (D.L₂'.exact_iff_mono hδ).mp D.L₂'_exact
  · have := hS.epi_g
    have : Epi D.L₂.g := inferInstanceAs (Epi ((godementFirstProduct X).map S.g))
    exact D.epi_L₃_g

instance godementCokernel_preservesHomology (X : Scheme.{u}) :
    (godementCokernel X).PreservesHomology :=
  ((CategoryTheory.Functor.exact_tfae (godementCokernel X)).out 1 3).mp
    (fun _ hS => godementCokernel_shortExact hS)

instance godementCokernel_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (godementCokernel X) :=
  CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology _

instance godementCokernel_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (godementCokernel X) :=
  CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology _

/-- The actual exact cokernel functor for the standard module-sheaf exact structure. -/
def godementCokernelExactFunctor (X : Scheme.{u}) :
    ExactFunctor (sheafExactStructure X) (sheafExactStructure X) where
  toFunctor := godementCokernel X
  map_conflation _ hS := godementCokernel_shortExact hS


/-- The actual successive cokernel functors, starting with the identity. -/
def godementIterate (X : Scheme.{u}) : ℕ → (X.Modules ⥤ X.Modules)
  | 0 => 𝟭 _
  | n + 1 => godementIterate X n ⋙ godementCokernel X

instance godementIterate_additive (X : Scheme.{u}) (n : ℕ) :
    (godementIterate X n).Additive := by
  induction n with
  | zero => change (𝟭 X.Modules).Additive; infer_instance
  | succ n _ => change (godementIterate X n ⋙ godementCokernel X).Additive; infer_instance

instance godementIterate_preservesFiniteLimits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (godementIterate X n) := by
  induction n with
  | zero => change PreservesFiniteLimits (𝟭 X.Modules); infer_instance
  | succ n ih =>
    let : PreservesFiniteLimits (godementIterate X n) := ih
    change PreservesFiniteLimits (godementIterate X n ⋙ godementCokernel X)
    infer_instance

instance godementIterate_preservesFiniteColimits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (godementIterate X n) := by
  induction n with
  | zero => change PreservesFiniteColimits (𝟭 X.Modules); infer_instance
  | succ n ih =>
    let : PreservesFiniteColimits (godementIterate X n) := ih
    change PreservesFiniteColimits (godementIterate X n ⋙ godementCokernel X)
    infer_instance

instance godementIterate_preservesHomology (X : Scheme.{u}) (n : ℕ) :
    (godementIterate X n).PreservesHomology := inferInstance

/-- The `n`-th original Godement term is `G(C^n M)`. -/
def godementResolutionTerm (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ X.Modules :=
  godementIterate X n ⋙ godementFirstProduct X

instance godementResolutionTerm_additive (X : Scheme.{u}) (n : ℕ) :
    (godementResolutionTerm X n).Additive :=
  inferInstanceAs (godementIterate X n ⋙ godementFirstProduct X).Additive

instance godementResolutionTerm_preservesFiniteLimits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (godementResolutionTerm X n) :=
  inferInstanceAs (PreservesFiniteLimits (godementIterate X n ⋙ godementFirstProduct X))

instance godementResolutionTerm_preservesFiniteColimits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (godementResolutionTerm X n) :=
  inferInstanceAs (PreservesFiniteColimits (godementIterate X n ⋙ godementFirstProduct X))

instance godementResolutionTerm_preservesHomology (X : Scheme.{u}) (n : ℕ) :
    (godementResolutionTerm X n).PreservesHomology := inferInstance

/-- The differential is the actual quotient followed by the next germ unit. -/
def godementResolutionDifferential (X : Scheme.{u}) (n : ℕ) :
    godementResolutionTerm X n ⟶ godementResolutionTerm X (n + 1) :=
  CategoryTheory.Functor.whiskerLeft (godementIterate X n) (godementQuotient X) ≫
    CategoryTheory.Functor.whiskerLeft (godementIterate X (n + 1)) (godementFirstProductUnit X)

@[reassoc (attr := simp)]
theorem godementResolutionDifferential_comp (X : Scheme.{u}) (n : ℕ) (M : X.Modules) :
    (godementResolutionDifferential X n).app M ≫
      (godementResolutionDifferential X (n + 1)).app M = 0 := by
  change ((godementQuotient X).app ((godementIterate X n).obj M) ≫
    (godementFirstProductUnit X).app ((godementIterate X (n + 1)).obj M)) ≫
    ((godementQuotient X).app ((godementIterate X (n + 1)).obj M) ≫
      (godementFirstProductUnit X).app ((godementIterate X (n + 2)).obj M)) = 0
  rw [Category.assoc,
    ← Category.assoc ((godementFirstProductUnit X).app ((godementIterate X (n + 1)).obj M)),
    godementUnit_quotient, zero_comp, comp_zero]

/-- The original cochain complex of Godement terms, natural on actual sheaf maps. -/
def godementResolution (X : Scheme.{u}) : X.Modules ⥤ CochainComplex X.Modules ℕ where
  obj M := CochainComplex.of (fun n => (godementResolutionTerm X n).obj M)
    (fun n => (godementResolutionDifferential X n).app M)
    (fun n => godementResolutionDifferential_comp X n M)
  map f := CochainComplex.ofHom (fun n => (godementResolutionTerm X n).map f)
    (fun n => by
      simp only [CochainComplex.of_d]
      exact (godementResolutionDifferential X n).naturality f)
  map_id M := by ext1 n; exact (godementResolutionTerm X n).map_id M
  map_comp f g := by ext1 n; exact (godementResolutionTerm X n).map_comp f g

@[simp]
theorem godementResolution_X (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    ((godementResolution X).obj M).X n =
      (godementFirstProduct X).obj ((godementIterate X n).obj M) := rfl

@[simp]
theorem godementResolution_d (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    ((godementResolution X).obj M).d n (n + 1) =
      (godementQuotient X).app ((godementIterate X n).obj M) ≫
        (godementFirstProductUnit X).app ((godementIterate X (n + 1)).obj M) :=
by
  dsimp only [godementResolution]
  rw [CochainComplex.of_d]
  rfl

@[simp]
theorem godementResolution_map_f {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    ((godementResolution X).map f).f n =
      (godementFirstProduct X).map ((godementIterate X n).map f) := rfl

instance godementResolution_isFlasque (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    TopCat.Presheaf.IsFlasque (((godementResolution X).obj M).X n).presheaf :=
  godementFirstProduct_isFlasque X _

/-- Precomposing by an epi and postcomposing by a mono preserves middle exactness. -/
theorem godement_splice_exact {X : Scheme.{u}} {A B C D E : X.Modules}
    {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).Exact) (p : D ⟶ A) (q : C ⟶ E) [Epi p] [Mono q] :
    (ShortComplex.mk (p ≫ f) (g ≫ q)
      (by simp only [Category.assoc, reassoc_of% w, zero_comp, comp_zero])).Exact := by
  let T := ShortComplex.mk f (g ≫ q) (by rw [← Category.assoc, w, zero_comp])
  let φ : ShortComplex.mk f g w ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := q
      comm₁₂ := by simp [T]
      comm₂₃ := by simp [T] }
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp h
  let ψ : ShortComplex.mk (p ≫ f) (g ≫ q)
      (by simp only [Category.assoc, reassoc_of% w, zero_comp, comp_zero]) ⟶ T :=
    { τ₁ := p
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T]
      comm₂₃ := by simp [T] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hT

/-- The original germ augmentation is exact at the first Godement term. -/
theorem godementResolution_exact_zero (X : Scheme.{u}) (M : X.Modules) :
    (ShortComplex.mk ((godementFirstProductUnit X).app M)
      (((godementResolution X).obj M).d 0 1)
      (by simp [godementIterate])).Exact := by
  simpa only [godementResolution_d, godementIterate, Functor.id_obj, Functor.comp_obj,
    Category.id_comp] using godement_splice_exact (godementUnit_quotient X M)
      (godementUnit_shortExact X M).exact (𝟙 M)
      ((godementFirstProductUnit X).app ((godementCokernel X).obj M))

/-- Exactness in every positive degree is obtained from the actual successive
short exact cokernel sequences, with epi quotients and monic germ units. -/
theorem godementResolution_exactAt_succ (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    ((godementResolution X).obj M).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  change (ShortComplex.mk _ _ _).Exact
  simpa only [godementResolution_d] using
    godement_splice_exact (godementUnit_quotient X ((godementIterate X (n + 1)).obj M))
      (godementUnit_shortExact X ((godementIterate X (n + 1)).obj M)).exact
      ((godementQuotient X).app ((godementIterate X n).obj M))
      ((godementFirstProductUnit X).app ((godementIterate X (n + 1 + 1)).obj M))

instance godementResolution_additive (X : Scheme.{u}) : (godementResolution X).Additive where
  map_add {M N} f g := by
    ext1 n
    exact (godementResolutionTerm X n).map_add

/-- Each term of the resolution sends every original short exact sequence to a short
exact sequence in the standard sheaf exact structure. -/
theorem godementResolutionTerm_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (n : ℕ) : (S.map (godementResolutionTerm X n)).ShortExact :=
  hS.map_of_exact _

/-- The entire cochain resolution functor is exact, as witnessed degree by degree. -/
theorem godementResolution_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (godementResolution X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  change (S.map (godementResolutionTerm X n)).ShortExact
  exact godementResolutionTerm_shortExact hS n

instance godementResolution_preservesHomology (X : Scheme.{u}) :
    (godementResolution X).PreservesHomology :=
  ((CategoryTheory.Functor.exact_tfae (godementResolution X)).out 1 3).mp
    (fun _ hS => godementResolution_shortExact hS)

/-- The construction retains zero objects in every degree. -/
theorem godementResolution_isZero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M) (n : ℕ) :
    IsZero (((godementResolution X).obj M).X n) :=
  (godementResolutionTerm X n).map_isZero hM

/-- The augmentation is the original germ map in degree zero. -/
def godementResolutionUnit (X : Scheme.{u}) :
    CochainComplex.single₀ X.Modules ⟶ godementResolution X where
  app M := (CochainComplex.fromSingle₀Equiv _ M).symm
    ⟨(godementFirstProductUnit X).app M, by simp [godementIterate]⟩
  naturality {M N} f := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
      CochainComplex.fromSingle₀Equiv_symm_apply_f_zero, godementResolution_map_f,
      godementIterate, Functor.id_map]
    exact (godementFirstProductUnit X).naturality f

@[simp]
theorem godementResolutionUnit_f_zero (X : Scheme.{u}) (M : X.Modules) :
    ((godementResolutionUnit X).app M).f 0 = (godementFirstProductUnit X).app M := by
  dsimp only [godementResolutionUnit]
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The actual natural augmentation is a quasi-isomorphism to the original sheaf
concentrated in degree zero; no exactness or resolution is passed as an assumption. -/
instance godementResolutionUnit_quasiIso (X : Scheme.{u}) (M : X.Modules) :
    QuasiIso ((godementResolutionUnit X).app M) where
  quasiIsoAt n := by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · change (ShortComplex.mk (((godementResolutionUnit X).app M).f 0)
          (((godementResolution X).obj M).d 0 1) _).Exact ∧
            Mono (((godementResolutionUnit X).app M).f 0)
        simpa only [godementResolutionUnit_f_zero] using
          And.intro (godementResolution_exact_zero X M)
            (inferInstance : Mono ((godementFirstProductUnit X).app M))
      · rfl
      · rfl
      · rfl
    | succ n =>
      exact (quasiIsoAt_iff_exactAt _ (n + 1)
        (CochainComplex.exactAt_succ_single_obj _ _)).mpr
          (godementResolution_exactAt_succ X M n)

end AlgebraicGeometry.Scheme.Modules.Godement
