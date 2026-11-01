/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Effacement
public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# External Ext classes through a biexact functor

The external class is the original Ext composition of the two original
`mapExactFunctor` images. The degree-one sign comes from the actual
pullback and signed-biproduct short exact sequences of a 3-by-3 diagram.
Classwise epimorphic effacement propagates that sign to all degrees.
The three Ext universes are independent; no injective/projective supply,
chosen resolution, or additional derived model is public.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Abelian

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃

namespace CategoryTheory.Abelian.Ext

variable {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]

private theorem comp_zsmul {X Y Z : E} {p q n : ℕ}
    (x : Ext X Y p) (y : Ext Y Z q) (h : p + q = n) (a : ℤ) :
    x.comp (a • y) h = a • x.comp y h :=
  _root_.map_zsmul (x.precomp Z h) a y

private theorem zsmul_comp {X Y Z : E} {p q n : ℕ}
    (x : Ext X Y p) (y : Ext Y Z q) (h : p + q = n) (a : ℤ) :
    (a • x).comp y h = a • x.comp y h :=
  _root_.map_zsmul (y.postcomp X h) a x

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]
  (F : C ⥤ D ⥤ E) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ X, PreservesFiniteLimits (F.obj X)] [∀ X, PreservesFiniteColimits (F.obj X)]
  [∀ Y, PreservesFiniteLimits (F.flip.obj Y)]
  [∀ Y, PreservesFiniteColimits (F.flip.obj Y)]

local instance (Y : D) : (F.flip.obj Y).Additive := { }

/-- The original external Ext class: first the first-variable class at the
original second source, then the second-variable class at the first target. -/
def extBifunctor {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    Ext.{w₃} ((F.obj X₀).obj Y₀) ((F.obj X₁).obj Y₁) n :=
  (x.mapExactFunctor (F.flip.obj Y₀)).comp (y.mapExactFunctor (F.obj X₁)) h

/-- The same external class as a biadditive map on the original Ext groups. -/
def extBifunctorHom (X₀ X₁ : C) (Y₀ Y₁ : D) (p q n : ℕ) (h : p + q = n) :
    Ext.{w₁} X₀ X₁ p →+
      Ext.{w₂} Y₀ Y₁ q →+ Ext.{w₃} ((F.obj X₀).obj Y₀) ((F.obj X₁).obj Y₁) n :=
  ((Ext.bilinearComp ((F.obj X₀).obj Y₀) ((F.obj X₁).obj Y₀)
    ((F.obj X₁).obj Y₁) p q n h).compl₂ ((F.obj X₁).mapExtAddHom Y₀ Y₁ q)).comp
      ((F.flip.obj Y₀).mapExtAddHom X₀ X₁ p)

@[simp]
theorem extBifunctorHom_apply_apply (X₀ X₁ : C) (Y₀ Y₁ : D) (p q n : ℕ)
    (h : p + q = n) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    extBifunctorHom F X₀ X₁ Y₀ Y₁ p q n h x y = extBifunctor F x y h := rfl

/-- In degree zero this is the original bifunctor action on the two maps. -/
theorem extBifunctor_mk₀_mk₀ {X₀ X₁ : C} {Y₀ Y₁ : D}
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) :
    extBifunctor F (Ext.mk₀ f) (Ext.mk₀ g) (zero_add 0) =
      Ext.mk₀ ((F.map f).app Y₀ ≫ (F.obj X₁).map g) := by
  rw [extBifunctor, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀]
  rfl

/-- Original degree-zero naturality in the first variable, with no sign. -/
theorem extBifunctor_mk₀_left {X₀ X₁ : C} {Y₀ Y₁ : D} {q : ℕ}
    (f : X₀ ⟶ X₁) (y : Ext.{w₂} Y₀ Y₁ q) :
    extBifunctor F (Ext.mk₀ f) y (zero_add q) =
      (y.mapExactFunctor (F.obj X₀)).comp (Ext.mk₀ ((F.map f).app Y₁)) (add_zero q) := by
  rw [extBifunctor, Ext.mapExactFunctor_mk₀]
  exact (Ext.mapExactFunctor_comp_mk₀_natTransApp y (F.map f)).symm

/-- Original degree-zero naturality in the second variable, with no sign. -/
theorem extBifunctor_mk₀_right {X₀ X₁ : C} {Y₀ Y₁ : D} {p : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (g : Y₀ ⟶ Y₁) :
    extBifunctor F x (Ext.mk₀ g) (add_zero p) =
      (Ext.mk₀ ((F.obj X₀).map g)).comp
        (x.mapExactFunctor (F.flip.obj Y₁)) (zero_add p) := by
  rw [extBifunctor, Ext.mapExactFunctor_mk₀]
  exact Ext.mapExactFunctor_comp_mk₀_natTransApp x (F.flip.map g)

end CategoryTheory.Functor

namespace CategoryTheory.ShortComplex

variable {E : Type u₃} [Category.{v₃} E] [Abelian E]

private def pullbackShortComplex (S : ShortComplex E) {T : E} (f : T ⟶ S.X₃) :
    ShortComplex E :=
  ShortComplex.mk (pullback.lift (0 : S.X₁ ⟶ T) S.f (by simp))
    (pullback.fst f S.g) (by simp)

private theorem shortExact_pullbackShortComplex {S : ShortComplex E} (hS : S.ShortExact)
    {T : E} (f : T ⟶ S.X₃) : (pullbackShortComplex S f).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  let i : S.X₁ ⟶ pullback f S.g := pullback.lift 0 S.f (by simp)
  have hi : i ≫ pullback.snd f S.g = S.f := by simp [i]
  have hiMono : Mono (pullbackShortComplex S f).f := mono_of_mono_fac hi
  refine
    { mono_f := hiMono
      epi_g := inferInstanceAs (Epi (pullback.fst f S.g))
      exact := ?_ }
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro A z hz
  change A ⟶ pullback f S.g at z
  change z ≫ pullback.fst f S.g = 0 at hz
  have hzero : (z ≫ pullback.snd f S.g) ≫ S.g = 0 := by
    rw [assoc, ← pullback.condition, ← assoc, hz, zero_comp]
  refine ⟨hS.exact.lift (z ≫ pullback.snd f S.g) hzero, ?_⟩
  apply pullback.hom_ext
  · simpa only [pullbackShortComplex, assoc, pullback.lift_fst,
      comp_zero] using hz.symm
  · simp only [pullbackShortComplex, assoc, pullback.lift_snd,
      Exact.lift_f]

end CategoryTheory.ShortComplex

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]
  (F : C ⥤ D ⥤ E) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ X, PreservesFiniteLimits (F.obj X)] [∀ X, PreservesFiniteColimits (F.obj X)]
  [∀ Y, PreservesFiniteLimits (F.flip.obj Y)]
  [∀ Y, PreservesFiniteColimits (F.flip.obj Y)]

local instance (Y : D) : (F.flip.obj Y).Additive := { }

/-- The degree-one sign is the actual 3-by-3 short-exact-sequence sign.
Its proof constructs the central pullback extension and the signed
biproduct extension, then uses ordinary original Ext-class naturality. -/
theorem extBifunctor_extClass_extClass {S : ShortComplex C} {T : ShortComplex D}
    (hS : S.ShortExact) (hT : T.ShortExact) :
    extBifunctor F hS.extClass hT.extClass (show 1 + 1 = 2 from rfl) =
      -((hT.extClass.mapExactFunctor (F.obj S.X₃)).comp
        (hS.extClass.mapExactFunctor (F.flip.obj T.X₁)) (show 1 + 1 = 2 from rfl)) := by
  let row (Y : D) := S.map (F.flip.obj Y)
  let col (X : C) := T.map (F.obj X)
  have hrow (Y : D) : (row Y).ShortExact := hS.map_of_exact (F.flip.obj Y)
  have hcol (X : C) : (col X).ShortExact := hT.map_of_exact (F.obj X)
  let q := (F.obj S.X₃).map T.g
  let r := (F.map S.g).app T.X₃
  let P := pullback q r
  let e : (F.obj S.X₂).obj T.X₂ ⟶ P :=
    pullback.lift ((F.map S.g).app T.X₂) ((F.obj S.X₂).map T.g)
      ((F.map S.g).naturality T.g).symm
  have efst : e ≫ pullback.fst q r = (F.map S.g).app T.X₂ := by simp [e, q, r]
  have esnd : e ≫ pullback.snd q r = (F.obj S.X₂).map T.g := by simp [e, q, r]
  let a : (F.obj S.X₁).obj T.X₁ ⟶ (F.obj S.X₂).obj T.X₂ :=
    (F.obj S.X₁).map T.f ≫ (F.map S.f).app T.X₂
  let iC : (F.obj S.X₃).obj T.X₁ ⟶ P :=
    pullback.lift ((F.obj S.X₃).map T.f) 0 (by simp [q, ← Functor.map_comp])
  let iG : (F.obj S.X₁).obj T.X₃ ⟶ P :=
    pullback.lift 0 ((F.map S.f).app T.X₃) (by
      simp [r, ← NatTrans.comp_app, ← Functor.map_comp])
  let pb := ShortComplex.pullbackShortComplex (row T.X₃) q
  have hpb : pb.ShortExact := ShortComplex.shortExact_pullbackShortComplex (hrow T.X₃) q
  let φ : row T.X₂ ⟶ pb := ShortComplex.homMk ((F.obj S.X₁).map T.g) e (𝟙 _)
    (by
      apply pullback.hom_ext
      · simp [pb, ShortComplex.pullbackShortComplex, e, row, q, r,
          ← NatTrans.comp_app, ← Functor.map_comp]
      · simp [pb, ShortComplex.pullbackShortComplex, e, row, q, r])
    (by simp [pb, ShortComplex.pullbackShortComplex, e, row, q, r])
  have : Epi (row T.X₂).g := (hrow T.X₂).epi_g
  have : Epi pb.g := hpb.epi_g
  have : Epi φ.τ₁ := (hcol S.X₁).epi_g
  have : Epi φ.τ₃ := inferInstanceAs (Epi (𝟙 ((F.obj S.X₃).obj T.X₂)))
  have he : Epi e := ShortComplex.epi_τ₂_of_exact_of_epi φ hpb.exact
  have : Mono (col S.X₁).f := (hcol S.X₁).mono_f
  have : Mono (row T.X₂).f := (hrow T.X₂).mono_f
  have : Mono (row T.X₃).f := (hrow T.X₃).mono_f
  have ha : Mono a := inferInstanceAs (Mono ((col S.X₁).f ≫ (row T.X₂).f))
  have hae : a ≫ e = 0 := by
    apply pullback.hom_ext
    · rw [assoc, efst, zero_comp]
      change ((col S.X₁).f ≫ (row T.X₂).f) ≫ (row T.X₂).g = 0
      rw [assoc, ShortComplex.zero, comp_zero]
    · rw [assoc, esnd, zero_comp]
      dsimp only [a]
      rw [assoc, ← (F.map S.f).naturality T.g, ← assoc]
      change ((col S.X₁).f ≫ (col S.X₁).g) ≫ (row T.X₃).f = 0
      rw [ShortComplex.zero, zero_comp]
  let central := ShortComplex.mk a e hae
  have hcentral : central.ShortExact := by
    refine { mono_f := ha, epi_g := he, exact := ?_ }
    apply ShortComplex.exact_of_f_is_kernel
    apply KernelFork.IsLimit.ofι'
    intro A z hz
    have hzq : z ≫ (row T.X₂).g = 0 := by
      change z ≫ (F.map S.g).app T.X₂ = 0
      simpa only [central, assoc, efst, zero_comp] using
        congrArg (fun m => m ≫ pullback.fst q r) hz
    let d := (hrow T.X₂).exact.lift z hzq
    have hd : d ≫ (F.map S.f).app T.X₂ = z := (hrow T.X₂).exact.lift_f z hzq
    have hdz : d ≫ (col S.X₁).g = 0 := by
      apply (cancel_mono (row T.X₃).f).mp
      have hz' : z ≫ (F.obj S.X₂).map T.g = 0 := by
        simpa only [central, assoc, esnd, zero_comp] using
          congrArg (fun m => m ≫ pullback.snd q r) hz
      change (d ≫ (F.obj S.X₁).map T.g) ≫ (F.map S.f).app T.X₃ = 0 ≫ _
      rw [assoc, (F.map S.f).naturality, ← assoc, hd, hz', zero_comp]
    refine ⟨(hcol S.X₁).exact.lift d hdz, ?_⟩
    have hl : (hcol S.X₁).exact.lift d hdz ≫ (F.obj S.X₁).map T.f = d :=
      (hcol S.X₁).exact.lift_f d hdz
    change (hcol S.X₁).exact.lift d hdz ≫
      ((F.obj S.X₁).map T.f ≫ (F.map S.f).app T.X₂) = z
    rw [← assoc, hl, hd]
  let sq := IsPullback.of_hasPullback q r
  let B := sq.shortComplex'
  have : Epi q := (hcol S.X₃).epi_g
  have hB : B.ShortExact := by
    refine
      { exact := sq.exact_shortComplex'
        mono_f := sq.mono_shortComplex'_f
        epi_g := ?_ }
    exact epi_of_epi_fac (show biprod.inl ≫ B.g = q by simp [B])
  let top : row T.X₁ ⟶ central := ShortComplex.homMk (𝟙 _)
    ((F.obj S.X₂).map T.f) iC
    (by simp [central, a, row])
    (by
      apply pullback.hom_ext
      · simp [central, e, iC, row, q, r]
      · simp [central, e, iC, row, ← Functor.map_comp])
  let left : col S.X₁ ⟶ central := ShortComplex.homMk (𝟙 _)
    ((F.map S.f).app T.X₂) iG
    (by simp [central, a, col])
    (by simpa [φ, pb, ShortComplex.pullbackShortComplex, central, iG, col, row] using
      φ.comm₁₂.symm)
  let right : col S.X₃ ⟶ B := ShortComplex.homMk iC biprod.inl (𝟙 _)
    (by
      change iC ≫ biprod.lift (pullback.fst q r) (pullback.snd q r) =
        (F.obj S.X₃).map T.f ≫ biprod.inl
      apply biprod.hom_ext <;> simp [iC, q, r])
    (by simp [B, col, q])
  let bottom : row T.X₃ ⟶ B := ShortComplex.homMk iG biprod.inr (-𝟙 _)
    (by
      change iG ≫ biprod.lift (pullback.fst q r) (pullback.snd q r) =
        (F.map S.f).app T.X₃ ≫ biprod.inr
      apply biprod.hom_ext <;> simp [iG, q, r])
    (by simp [B, row, r])
  have htop : (hrow T.X₁).extClass =
      (Ext.mk₀ iC).comp hcentral.extClass (zero_add 1) := by
    simpa [top] using (hrow T.X₁).extClass_naturality hcentral top
  have hleft : (hcol S.X₁).extClass =
      (Ext.mk₀ iG).comp hcentral.extClass (zero_add 1) := by
    simpa [left] using (hcol S.X₁).extClass_naturality hcentral left
  have hright : (hcol S.X₃).extClass.comp (Ext.mk₀ iC) (add_zero 1) = hB.extClass := by
    simpa [right] using (hcol S.X₃).extClass_naturality hB right
  have hbottom : (hrow T.X₃).extClass.comp (Ext.mk₀ iG) (add_zero 1) = -hB.extClass := by
    simpa [bottom] using (hrow T.X₃).extClass_naturality hB bottom
  rw [extBifunctor, Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass,
    Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass]
  change (hrow T.X₃).extClass.comp (hcol S.X₁).extClass rfl =
    -((hcol S.X₃).extClass.comp (hrow T.X₁).extClass rfl)
  rw [hleft, htop, ← Ext.comp_assoc_of_second_deg_zero,
    ← Ext.comp_assoc_of_second_deg_zero, hbottom, hright, Ext.neg_comp]

/-- Moving an original degree-one extension class past an arbitrary class
contributes one minus sign for each degree of that class. Classwise
epimorphic effacement supplies every inductive step. -/
theorem extBifunctor_extClass_left {S : ShortComplex C} (hS : S.ShortExact)
    {Y₀ Y₁ : D} {q : ℕ} (y : Ext.{w₂} Y₀ Y₁ q) :
    extBifunctor F hS.extClass y rfl = ((-1 : ℤ) ^ q) •
      (y.mapExactFunctor (F.obj S.X₃)).comp
        (hS.extClass.mapExactFunctor (F.flip.obj Y₁)) (Nat.add_comm q 1) := by
  induction q generalizing Y₀ Y₁ with
  | zero =>
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective Y₀ Y₁).surjective y
    simpa only [Ext.mapExactFunctor_mk₀, pow_zero, one_smul] using
      extBifunctor_mk₀_right F hS.extClass g
  | succ q ih =>
    obtain ⟨M, f, hf, hz⟩ := Ext.exists_epi_mk₀_comp_eq_zero y
    let := hf
    let T := ShortComplex.kernelSequence f
    have hT : T.ShortExact := { exact := ShortComplex.kernelSequence_exact f, epi_g := hf }
    obtain ⟨y', rfl⟩ := Ext.contravariant_sequence_exact₃ hT Y₁ y hz (Nat.add_comm 1 q)
    let ax (Y : D) := hS.extClass.mapExactFunctor (F.flip.obj Y)
    let b₀ := hT.extClass.mapExactFunctor (F.obj S.X₃)
    let b₁ := hT.extClass.mapExactFunctor (F.obj S.X₁)
    let c₀ := y'.mapExactFunctor (F.obj S.X₃)
    let c₁ := y'.mapExactFunctor (F.obj S.X₁)
    have hfirst : (ax Y₀).comp b₁ rfl = -(b₀.comp (ax (Limits.kernel f)) rfl) :=
      extBifunctor_extClass_extClass F hS hT
    have hrest : (ax (Limits.kernel f)).comp c₁ rfl = ((-1 : ℤ) ^ q) •
        c₀.comp (ax Y₁) (Nat.add_comm q 1) := ih y'
    simp only [extBifunctor, Ext.mapExactFunctor_comp]
    change (ax Y₀).comp (b₁.comp c₁ (Nat.add_comm 1 q)) rfl =
      ((-1 : ℤ) ^ (q + 1)) •
        (b₀.comp c₀ (Nat.add_comm 1 q)).comp (ax Y₁) (Nat.add_comm (q + 1) 1)
    calc
      _ = ((ax Y₀).comp b₁ rfl).comp c₁ (by omega) :=
        (Ext.comp_assoc _ _ _ rfl (Nat.add_comm 1 q) (by omega)).symm
      _ = -(b₀.comp ((ax (Limits.kernel f)).comp c₁ rfl) (by omega)) := by
        rw [hfirst, Ext.neg_comp, Ext.comp_assoc _ _ _ rfl rfl (by omega)]
      _ = -(b₀.comp (((-1 : ℤ) ^ q) •
          c₀.comp (ax Y₁) (Nat.add_comm q 1)) (by omega)) := by rw [hrest]
      _ = _ := by
        rw [Ext.comp_zsmul,
          ← Ext.comp_assoc _ _ _ (Nat.add_comm 1 q) (Nat.add_comm q 1) (by omega)]
        simp only [pow_succ, mul_neg, mul_one, neg_smul]

private theorem extBifunctor_mk₀_comm_of_degree
    {X₀ X₁ : C} {Y₀ Y₁ : D} {q n : ℕ}
    (f : X₀ ⟶ X₁) (y : Ext.{w₂} Y₀ Y₁ q) (h : 0 + q = n) :
    extBifunctor F (Ext.mk₀ f) y h =
      (y.mapExactFunctor (F.obj X₀)).comp
        ((Ext.mk₀ f).mapExactFunctor (F.flip.obj Y₁)) (by omega) := by
  obtain rfl : n = q := h.symm.trans (Nat.zero_add q)
  simpa only [Ext.mapExactFunctor_mk₀, Functor.flip_obj_map] using
    extBifunctor_mk₀_left F f y

private theorem extBifunctor_comm_aux {X₀ X₁ : C} {Y₀ Y₁ : D} {p q : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    extBifunctor F x y rfl = ((-1 : ℤ) ^ (p * q)) •
      (y.mapExactFunctor (F.obj X₀)).comp
        (x.mapExactFunctor (F.flip.obj Y₁)) (Nat.add_comm q p) := by
  induction p generalizing X₀ X₁ with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X₀ X₁).surjective x
    simp only [zero_mul, pow_zero, one_smul]
    exact extBifunctor_mk₀_comm_of_degree F f y rfl
  | succ p ih =>
    obtain ⟨M, f, hf, hz⟩ := Ext.exists_epi_mk₀_comp_eq_zero x
    let := hf
    let S := ShortComplex.kernelSequence f
    have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact f, epi_g := hf }
    obtain ⟨x', rfl⟩ := Ext.contravariant_sequence_exact₃ hS X₁ x hz (Nat.add_comm 1 p)
    let a₀ := hS.extClass.mapExactFunctor (F.flip.obj Y₀)
    let a₁ := hS.extClass.mapExactFunctor (F.flip.obj Y₁)
    let b₀ := x'.mapExactFunctor (F.flip.obj Y₀)
    let b₁ := x'.mapExactFunctor (F.flip.obj Y₁)
    let c₀ := y.mapExactFunctor (F.obj X₀)
    let cM := y.mapExactFunctor (F.obj (Limits.kernel f))
    let c₁ := y.mapExactFunctor (F.obj X₁)
    have hfirst : a₀.comp cM rfl = ((-1 : ℤ) ^ q) •
        c₀.comp a₁ (Nat.add_comm q 1) := extBifunctor_extClass_left F hS y
    have hrest : b₀.comp c₁ rfl = ((-1 : ℤ) ^ (p * q)) •
        cM.comp b₁ (Nat.add_comm q p) := ih x'
    simp only [extBifunctor, Ext.mapExactFunctor_comp]
    change (a₀.comp b₀ (Nat.add_comm 1 p)).comp c₁ rfl =
      ((-1 : ℤ) ^ ((p + 1) * q)) •
        c₀.comp (a₁.comp b₁ (Nat.add_comm 1 p)) (Nat.add_comm q (p + 1))
    calc
      _ = a₀.comp (b₀.comp c₁ rfl) (by omega) :=
        Ext.comp_assoc _ _ _ (Nat.add_comm 1 p) rfl (by omega)
      _ = ((-1 : ℤ) ^ (p * q)) •
          ((a₀.comp cM rfl).comp b₁ (by omega)) := by
        rw [hrest, Ext.comp_zsmul,
          ← Ext.comp_assoc _ _ _ rfl (Nat.add_comm q p) (by omega)]
      _ = ((-1 : ℤ) ^ (p * q)) • (((-1 : ℤ) ^ q) •
          c₀.comp (a₁.comp b₁ (Nat.add_comm 1 p)) (by omega)) := by
        rw [hfirst, Ext.zsmul_comp,
          Ext.comp_assoc _ _ _ (Nat.add_comm q 1) (Nat.add_comm 1 p) (by omega)]
      _ = _ := by simp only [Nat.add_mul, Nat.one_mul, pow_add, mul_smul]

/-- Signed interchange for the original maps through an actual biexact
functor. The opposite order retains its explicit sum-degree transport.
No injective/projective supply, extra interchange datum or invertibility of
two is assumed. -/
theorem extBifunctor_comm {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    extBifunctor F x y h = ((-1 : ℤ) ^ (p * q)) •
      (y.mapExactFunctor (F.obj X₀)).comp
        (x.mapExactFunctor (F.flip.obj Y₁)) ((Nat.add_comm q p).trans h) := by
  subst n
  exact extBifunctor_comm_aux F x y

@[simp]
theorem extBifunctor_add_left {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (x x' : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    extBifunctor F (x + x') y h = extBifunctor F x y h + extBifunctor F x' y h := by
  simp only [extBifunctor, Ext.mapExactFunctor_add, Ext.add_comp]

@[simp]
theorem extBifunctor_add_right {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y y' : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    extBifunctor F x (y + y') h = extBifunctor F x y h + extBifunctor F x y' h := by
  simp only [extBifunctor, Ext.mapExactFunctor_add, Ext.comp_add]

theorem extBifunctor_zsmul_left {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (a : ℤ) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    extBifunctor F (a • x) y h = a • extBifunctor F x y h :=
  _root_.map_zsmul ((extBifunctorHom F X₀ X₁ Y₀ Y₁ p q n h).flip y) a x

theorem extBifunctor_zsmul_right {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (a : ℤ) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    extBifunctor F x (a • y) h = a • extBifunctor F x y h :=
  _root_.map_zsmul (extBifunctorHom F X₀ X₁ Y₀ Y₁ p q n h x) a y

/-- Naturality in the original first source. -/
theorem extBifunctor_mk₀_comp_left {X' X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (f : X' ⟶ X₀) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (h : p + q = n) :
    extBifunctor F ((Ext.mk₀ f).comp x (zero_add p)) y h =
      (Ext.mk₀ ((F.map f).app Y₀)).comp (extBifunctor F x y h) (zero_add n) := by
  simp only [extBifunctor, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact Ext.comp_assoc _ _ _ (zero_add p) h (by omega)

/-- Naturality in the original first target. -/
theorem extBifunctor_comp_mk₀_left {X₀ X₁ X' : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (f : X₁ ⟶ X') (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (h : p + q = n) :
    extBifunctor F (x.comp (Ext.mk₀ f) (add_zero p)) y h =
      (extBifunctor F x y h).comp (Ext.mk₀ ((F.map f).app Y₁)) (add_zero n) := by
  have hy := Ext.mapExactFunctor_comp_mk₀_natTransApp y (F.map f)
  simp only [extBifunctor, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Functor.flip_obj_map]
  rw [Ext.comp_assoc_of_second_deg_zero, ← hy, ← Ext.comp_assoc_of_third_deg_zero]

/-- Naturality in the original second source. -/
theorem extBifunctor_mk₀_comp_right {X₀ X₁ : C} {Y' Y₀ Y₁ : D} {p q n : ℕ}
    (g : Y' ⟶ Y₀) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (h : p + q = n) :
    extBifunctor F x ((Ext.mk₀ g).comp y (zero_add q)) h =
      (Ext.mk₀ ((F.obj X₀).map g)).comp (extBifunctor F x y h) (zero_add n) := by
  have hx := Ext.mapExactFunctor_comp_mk₀_natTransApp x (F.flip.map g)
  simp only [Functor.flip_map_app] at hx
  simp only [extBifunctor, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc_of_second_deg_zero, hx,
    Ext.comp_assoc _ _ _ (zero_add p) h (by omega)]

/-- Naturality in the original second target. -/
theorem extBifunctor_comp_mk₀_right {X₀ X₁ : C} {Y₀ Y₁ Y' : D} {p q n : ℕ}
    (g : Y₁ ⟶ Y') (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (h : p + q = n) :
    extBifunctor F x (y.comp (Ext.mk₀ g) (add_zero q)) h =
      (extBifunctor F x y h).comp (Ext.mk₀ ((F.obj X₁).map g)) (add_zero n) := by
  simp only [extBifunctor, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ h).symm

/-- Whole naturality for an actual natural transformation of biexact
bifunctors, on the original external classes and all four endpoints. -/
theorem extBifunctor_natTrans
    (G : C ⥤ D ⥤ E) [G.Additive] [∀ X, (G.obj X).Additive]
    [∀ X, PreservesFiniteLimits (G.obj X)] [∀ X, PreservesFiniteColimits (G.obj X)]
    [∀ Y, PreservesFiniteLimits (G.flip.obj Y)]
    [∀ Y, PreservesFiniteColimits (G.flip.obj Y)]
    (τ : F ⟶ G) {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    (extBifunctor F x y h).comp (Ext.mk₀ ((τ.app X₁).app Y₁)) (add_zero n) =
      (Ext.mk₀ ((τ.app X₀).app Y₀)).comp (extBifunctor G x y h) (zero_add n) := by
  have hx := Ext.mapExactFunctor_comp_mk₀_natTransApp x (τ.flipApp Y₀)
  simp only [NatTrans.flipApp, flipFunctor] at hx
  have hy := Ext.mapExactFunctor_comp_mk₀_natTransApp y (τ.app X₁)
  simp only [extBifunctor]
  rw [Ext.comp_assoc_of_third_deg_zero, hy, ← Ext.comp_assoc_of_second_deg_zero,
    hx, Ext.comp_assoc _ _ _ (zero_add p) h (by omega)]

/-- The unsigned source connecting class in the first variable is the
original source connecting class of the external pairing, with sign +1. -/
theorem extBifunctor_extClass_comp_left {S : ShortComplex C} (hS : S.ShortExact)
    {X₁ : C} {Y₀ Y₁ : D} {p p' q n n' : ℕ}
    (x : Ext.{w₁} S.X₁ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (hp : 1 + p = p') (h : p + q = n) (h' : p' + q = n') :
    extBifunctor F (hS.extClass.comp x hp) y h' =
      (hS.map_of_exact (F.flip.obj Y₀)).extClass.comp
        (extBifunctor F x y h) (by omega) := by
  simp only [extBifunctor, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact Ext.comp_assoc _ _ _ hp h (by omega)

/-- The unsigned source connecting class in the second variable crosses
the degree-p first-variable class and therefore has sign (-1)^p. -/
theorem extBifunctor_extClass_comp_right {T : ShortComplex D} (hT : T.ShortExact)
    {X₀ X₁ : C} {Y₁ : D} {p q q' n n' : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} T.X₁ Y₁ q)
    (hq : 1 + q = q') (h : p + q = n) (h' : p + q' = n') :
    extBifunctor F x (hT.extClass.comp y hq) h' = ((-1 : ℤ) ^ p) •
      (hT.map_of_exact (F.obj X₀)).extClass.comp (extBifunctor F x y h) (by omega) := by
  have hc := extBifunctor_comm F x hT.extClass rfl
  simp only [extBifunctor, Nat.mul_one] at hc
  simp only [extBifunctor, Ext.mapExactFunctor_comp]
  rw [← Ext.comp_assoc _ _ _ rfl hq (by omega), hc, Ext.zsmul_comp,
    Ext.comp_assoc _ _ _ (Nat.add_comm 1 p) h (by omega), Ext.mapExactFunctor_extClass]

/-- Compatibility with the native signed contravariant connecting map
in the first source. Its extra factor is (-1)^q under Mathlib's δ convention. -/
theorem extBifunctor_δ_left {S : ShortComplex C} (hS : S.ShortExact)
    {X₁ : C} {Y₀ Y₁ : D} {p p' q n n' : ℕ}
    (x : Ext.{w₁} S.X₁ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (hp : p + 1 = p') (h : p + q = n) (h' : p' + q = n') :
    extBifunctor F (Ext.δ hS p p' hp x) y h' = ((-1 : ℤ) ^ q) •
      Ext.δ (hS.map_of_exact (F.flip.obj Y₀)) n n' (by omega) (extBifunctor F x y h) := by
  rw [Ext.δ_apply, Units.smul_def, Int.coe_negOnePow_natCast,
    extBifunctor_zsmul_left, extBifunctor_extClass_comp_left F hS x y (by omega) h h',
    Ext.δ_apply, Units.smul_def, Int.coe_negOnePow_natCast, smul_smul, ← pow_add]
  have hs : (-1 : ℤ) ^ (q + n') = (-1) ^ p' := by
    rw [show q + n' = p' + 2 * q by omega, pow_add, pow_mul]
    norm_num
  rw [hs]

/-- Compatibility with the native signed contravariant connecting map
in the second source. The interchange sign cancels the total-degree δ sign. -/
theorem extBifunctor_δ_right {T : ShortComplex D} (hT : T.ShortExact)
    {X₀ X₁ : C} {Y₁ : D} {p q q' n n' : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} T.X₁ Y₁ q)
    (hq : q + 1 = q') (h : p + q = n) (h' : p + q' = n') :
    extBifunctor F x (Ext.δ hT q q' hq y) h' =
      Ext.δ (hT.map_of_exact (F.obj X₀)) n n' (by omega) (extBifunctor F x y h) := by
  rw [Ext.δ_apply, Units.smul_def, Int.coe_negOnePow_natCast,
    extBifunctor_zsmul_right, extBifunctor_extClass_comp_right F hT x y (by omega) h h',
    Ext.δ_apply, Units.smul_def, Int.coe_negOnePow_natCast, smul_smul, ← pow_add]
  rw [show q' + p = n' by omega]

end CategoryTheory.Functor
