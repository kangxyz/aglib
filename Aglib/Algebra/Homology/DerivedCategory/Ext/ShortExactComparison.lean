/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Exact and colimit stability of the original Ext comparison

The comparison uses the actual exact-functor Ext map and source precomposition.
Its bijectivity is stable under short exact extensions. The degree-zero case
uses the native left exact sequence; positive degrees use the original
connecting extension classes. When both actual Ext functors preserve the
specified colimit, bijective comparisons at its stages give bijectivity at
the colimit. No injective-preservation premise is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : C} {A : D} (a : A ⟶ F.obj X)

/-- The original coefficient square of the exact-functor comparison. -/
theorem Functor.extPrecompMap_postcomp {Y Z : C} (q : Y ⟶ Z) (n : ℕ) :
    ((Ext.mk₀ (F.map q)).postcomp A (Nat.add_zero n)).comp
        (F.extPrecompMap a Y n) =
      (F.extPrecompMap a Z n).comp
        ((Ext.mk₀ q).postcomp X (Nat.add_zero n)) := by
  ext x
  change (F.extPrecompMap a Y n x).comp (Ext.mk₀ (F.map q)) (Nat.add_zero n) =
    F.extPrecompMap a Z n (x.comp (Ext.mk₀ q) (Nat.add_zero n))
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]

/-- The comparison square retains the native connecting extension class. -/
theorem Functor.extPrecompMap_connecting (S : ShortComplex C) (hS : S.ShortExact)
    (n : ℕ) :
    ((hS.map_of_exact F).extClass.postcomp A (show n + 1 = n + 1 from rfl)).comp
        (F.extPrecompMap a S.X₃ n) =
      (F.extPrecompMap a S.X₁ (n + 1)).comp
        (hS.extClass.postcomp X (show n + 1 = n + 1 from rfl)) := by
  ext x
  change (F.extPrecompMap a S.X₃ n x).comp (hS.map_of_exact F).extClass rfl =
    F.extPrecompMap a S.X₁ (n + 1) (x.comp hS.extClass rfl)
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_extClass]

private theorem exact_zero_of_injective {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (q : M →+ N) (hq : Function.Injective q) : Function.Exact (0 : Unit →+ M) q := by
  intro y
  constructor
  · intro hy
    have hy' : y = 0 := hq (by simpa using hy)
    exact ⟨Unit.unit, by simpa using hy'.symm⟩
  · rintro ⟨z, rfl⟩
    simp

/-- Bijectivity of the original comparison is closed under short exact extensions. -/
theorem Functor.extPrecompMap_bijective_of_shortExact
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₁ : ∀ n, Function.Bijective (F.extPrecompMap a S.X₁ n))
    (h₃ : ∀ n, Function.Bijective (F.extPrecompMap a S.X₃ n)) (n : ℕ) :
    Function.Bijective (F.extPrecompMap a S.X₂ n) := by
  let : Mono S.f := hS.mono_f
  let : Mono (F.map S.f) := (hS.map_of_exact F).mono_f
  cases n with
  | zero =>
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (0 : Unit →+ Ext X S.X₁ 0)
      ((Ext.mk₀ S.f).postcomp X (Nat.add_zero 0))
      ((Ext.mk₀ S.g).postcomp X (Nat.add_zero 0))
      (hS.extClass.postcomp X (show 0 + 1 = 1 from rfl))
      (0 : Unit →+ Ext A (F.obj S.X₁) 0)
      ((Ext.mk₀ (F.map S.f)).postcomp A (Nat.add_zero 0))
      ((Ext.mk₀ (F.map S.g)).postcomp A (Nat.add_zero 0))
      ((hS.map_of_exact F).extClass.postcomp A (show 0 + 1 = 1 from rfl))
      (0 : Unit →+ Unit) (F.extPrecompMap a S.X₁ 0)
      (F.extPrecompMap a S.X₂ 0) (F.extPrecompMap a S.X₃ 0)
      (F.extPrecompMap a S.X₁ 1) (by ext; simp)
      (F.extPrecompMap_postcomp a S.f 0) (F.extPrecompMap_postcomp a S.g 0)
      (F.extPrecompMap_connecting a S hS 0)
      (exact_zero_of_injective _ (Ext.postcomp_mk₀_injective_of_mono X S.f))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₂' X hS 0))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS 0 1 rfl))
      (exact_zero_of_injective _
        (Ext.postcomp_mk₀_injective_of_mono A (F.map S.f)))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₂' A (hS.map_of_exact F) 0))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map_of_exact F) 0 1 rfl))
      (fun _ => ⟨Unit.unit, rfl⟩) (h₁ 0) (h₃ 0) (h₁ 1).injective
  | succ n =>
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (hS.extClass.postcomp X (show n + 1 = n + 1 from rfl))
      ((Ext.mk₀ S.f).postcomp X (Nat.add_zero (n + 1)))
      ((Ext.mk₀ S.g).postcomp X (Nat.add_zero (n + 1)))
      (hS.extClass.postcomp X (show n + 1 + 1 = n + 1 + 1 from rfl))
      ((hS.map_of_exact F).extClass.postcomp A (show n + 1 = n + 1 from rfl))
      ((Ext.mk₀ (F.map S.f)).postcomp A (Nat.add_zero (n + 1)))
      ((Ext.mk₀ (F.map S.g)).postcomp A (Nat.add_zero (n + 1)))
      ((hS.map_of_exact F).extClass.postcomp A (show n + 1 + 1 = n + 1 + 1 from rfl))
      (F.extPrecompMap a S.X₃ n) (F.extPrecompMap a S.X₁ (n + 1))
      (F.extPrecompMap a S.X₂ (n + 1)) (F.extPrecompMap a S.X₃ (n + 1))
      (F.extPrecompMap a S.X₁ (n + 1 + 1))
      (F.extPrecompMap_connecting a S hS n)
      (F.extPrecompMap_postcomp a S.f (n + 1))
      (F.extPrecompMap_postcomp a S.g (n + 1))
      (F.extPrecompMap_connecting a S hS (n + 1))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₁' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₂' X hS (n + 1)))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS (n + 1) (n + 1 + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₁' A (hS.map_of_exact F) n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₂' A (hS.map_of_exact F) (n + 1)))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map_of_exact F) (n + 1) (n + 1 + 1) rfl))
      (h₃ n).surjective (h₁ (n + 1)) (h₃ (n + 1)) (h₁ (n + 1 + 1)).injective

private theorem ext_eq_zero_of_isZero {Y : C} (hY : IsZero Y) {n : ℕ}
    (x : Ext X Y n) : x = 0 := by
  have h := congrArg (fun q : Y ⟶ Y => x.comp (Ext.mk₀ q) (Nat.add_zero n))
    (hY.eq_of_tgt (𝟙 Y) 0)
  simpa using h

/-- A zero coefficient has bijective original comparison in every degree. -/
theorem Functor.extPrecompMap_bijective_of_isZero (Y : C) (hY : IsZero Y) (n : ℕ) :
    Function.Bijective (F.extPrecompMap a Y n) := by
  let : Subsingleton (Ext X Y n) :=
    subsingleton_of_forall_eq 0 (ext_eq_zero_of_isZero hY)
  let : Subsingleton (Ext A (F.obj Y) n) :=
    subsingleton_of_forall_eq 0 (ext_eq_zero_of_isZero (F.map_isZero hY))
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- An actual coefficient isomorphism preserves bijectivity of the original comparison. -/
theorem Functor.extPrecompMap_bijective_of_iso {Y Z : C} (e : Y ≅ Z) (n : ℕ)
    (hY : Function.Bijective (F.extPrecompMap a Y n)) :
    Function.Bijective (F.extPrecompMap a Z n) := by
  have hsource : Function.Bijective ((Ext.mk₀ e.hom).postcomp X (Nat.add_zero n)) :=
    ((extFunctorObj X n).mapIso e).addCommGroupIsoToAddEquiv.bijective
  have htarget : Function.Bijective
      ((Ext.mk₀ (F.map e.hom)).postcomp A (Nat.add_zero n)) :=
    ((extFunctorObj A n).mapIso (F.mapIso e)).addCommGroupIsoToAddEquiv.bijective
  apply (Function.Bijective.of_comp_iff (F.extPrecompMap a Z n) hsource).mp
  change Function.Bijective ((F.extPrecompMap a Z n).comp
    ((Ext.mk₀ e.hom).postcomp X (Nat.add_zero n)))
  rw [← F.extPrecompMap_postcomp a e.hom n]
  exact htarget.comp hY

/-- Original comparisons, explicitly lifted to a common value universe. -/
def Functor.extPrecompNatTrans (n : ℕ) :
    extFunctorObj X n ⋙ AddCommGrpCat.uliftFunctor.{w', w} ⟶
      (F ⋙ extFunctorObj A n) ⋙ AddCommGrpCat.uliftFunctor.{w, w'} where
  app Y := AddCommGrpCat.ofHom
    ((AddEquiv.ulift.symm : Ext A (F.obj Y) n ≃+
      ULift.{w} (Ext A (F.obj Y) n)).toAddMonoidHom.comp
        ((F.extPrecompMap a Y n).comp
          (AddEquiv.ulift : ULift.{w'} (Ext X Y n) ≃+ Ext X Y n).toAddMonoidHom))
  naturality {Y Z} q := by
    ext x
    let x' : Ext X Y n := x.down
    have h : F.extPrecompMap a Z n (x'.comp (Ext.mk₀ q) (Nat.add_zero n)) =
        (F.extPrecompMap a Y n x').comp (Ext.mk₀ (F.map q)) (Nat.add_zero n) := by
      rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
    exact congrArg (fun z : Ext A (F.obj Z) n => (ULift.up z : ULift.{w} _)) h

/-- Universe transport leaves the original comparison as its literal down/up formula. -/
theorem Functor.extPrecompNatTrans_app_apply (Y : C) (n : ℕ) (x : Ext X Y n) :
    (F.extPrecompNatTrans a n).app Y (ULift.up x) =
      ULift.up (F.extPrecompMap a Y n x) := rfl

/-- Actual colimit preservation supplies comparison stability at the original cocone point. -/
theorem Functor.extPrecompMap_bijective_of_isColimit
    {I : Type*} [Category I] (K : I ⥤ C) (c : Cocone K) (hc : IsColimit c) (n : ℕ)
    [PreservesColimit K (extFunctorObj X n)]
    [PreservesColimit K (F ⋙ extFunctorObj A n)]
    (hK : ∀ i, Function.Bijective (F.extPrecompMap a (K.obj i) n)) :
    Function.Bijective (F.extPrecompMap a c.pt n) := by
  let α := F.extPrecompNatTrans a n
  have (i : I) : IsIso ((whiskerLeft K α).app i) := by
    let eSource : Ext X (K.obj i) n ≃+ ULift.{w'} (Ext X (K.obj i) n) := AddEquiv.ulift.symm
    let eTarget : Ext A (F.obj (K.obj i)) n ≃+
        ULift.{w} (Ext A (F.obj (K.obj i)) n) := AddEquiv.ulift.symm
    let e := (eSource.symm.trans
      (AddEquiv.ofBijective (F.extPrecompMap a (K.obj i) n) (hK i))).trans eTarget
    let eIso : AddCommGrpCat.of (ULift.{w'} (Ext X (K.obj i) n)) ≅
        AddCommGrpCat.of (ULift.{w} (Ext A (F.obj (K.obj i)) n)) := e.toAddCommGrpIso
    exact inferInstanceAs (IsIso eIso.hom)
  have : IsIso (whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  have : IsIso (α.app c.pt) := isIso_app_coconePt_of_preservesColimit K α c hc
  let eSource : Ext X c.pt n ≃+ ULift.{w'} (Ext X c.pt n) := AddEquiv.ulift.symm
  let eTarget : Ext A (F.obj c.pt) n ≃+ ULift.{w} (Ext A (F.obj c.pt) n) := AddEquiv.ulift.symm
  exact eTarget.symm.bijective.comp
    ((asIso (α.app c.pt)).addCommGroupIsoToAddEquiv.bijective.comp eSource.bijective)

end CategoryTheory
