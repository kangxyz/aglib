/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Effacement
public import Mathlib.CategoryTheory.Abelian.CommSq

/-! Signed Ext interchange for one original natural short exact row of exact functors. -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Abelian

universe u v u' v' w w'

namespace CategoryTheory.Abelian.Ext

variable {E : Type u'} [Category.{v'} E] [Abelian E] [HasExt.{w'} E]

private theorem comp_zsmul {X Y Z : E} {p q n : ℕ}
    (x : Ext X Y p) (y : Ext Y Z q) (h : p + q = n) (a : ℤ) :
    x.comp (a • y) h = a • x.comp y h :=
  _root_.map_zsmul (x.precomp Z h) a y

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.ShortComplex

variable {E : Type u'} [Category.{v'} E] [Abelian E]

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

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (F₁ F₂ F₃ : C ⥤ D)
  [F₁.Additive] [F₂.Additive] [F₃.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
  (i : F₁ ⟶ F₂) (j : F₂ ⟶ F₃)
  (hij : ∀ X : C, i.app X ≫ j.app X = 0)
  (hS : ∀ X : C, (ShortComplex.mk (i.app X) (j.app X) (hij X)).ShortExact)

/-- The degree-one sign for one natural short exact row of exact functors. -/
private theorem exactFunctorRow_extClass_extClass {T : ShortComplex C} (hT : T.ShortExact) :
    ((hS T.X₃).extClass).comp (hT.extClass.mapExactFunctor F₁) rfl =
      -((hT.extClass.mapExactFunctor F₃).comp (hS T.X₁).extClass rfl) := by
  let row (Y : C) := ShortComplex.mk (i.app Y) (j.app Y) (hij Y)
  let col₁ := T.map F₁
  let col₃ := T.map F₃
  have hrow (Y : C) : (row Y).ShortExact := hS Y
  have hcol₁ : col₁.ShortExact := hT.map_of_exact F₁
  have hcol₃ : col₃.ShortExact := hT.map_of_exact F₃
  let q := F₃.map T.g
  let r := j.app T.X₃
  let P := pullback q r
  let e : F₂.obj T.X₂ ⟶ P :=
    pullback.lift (j.app T.X₂) (F₂.map T.g)
      (j.naturality T.g).symm
  have efst : e ≫ pullback.fst q r = j.app T.X₂ := by simp [e, q, r]
  have esnd : e ≫ pullback.snd q r = F₂.map T.g := by simp [e, q, r]
  let a : F₁.obj T.X₁ ⟶ F₂.obj T.X₂ :=
    F₁.map T.f ≫ i.app T.X₂
  let iC : F₃.obj T.X₁ ⟶ P :=
    pullback.lift (F₃.map T.f) 0 (by simp [q, ← Functor.map_comp])
  let iG : F₁.obj T.X₃ ⟶ P :=
    pullback.lift 0 (i.app T.X₃) (by
      simp [r, hij])
  let pb := ShortComplex.pullbackShortComplex (row T.X₃) q
  have hpb : pb.ShortExact := ShortComplex.shortExact_pullbackShortComplex (hrow T.X₃) q
  let φ : row T.X₂ ⟶ pb := ShortComplex.homMk (F₁.map T.g) e (𝟙 _)
    (by
      apply pullback.hom_ext
      · simp [pb, ShortComplex.pullbackShortComplex, e, row, q, r,
          hij]
      · simp [pb, ShortComplex.pullbackShortComplex, e, row, q, r])
    (by simp [pb, ShortComplex.pullbackShortComplex, e, row, q, r])
  have : Epi (row T.X₂).g := (hrow T.X₂).epi_g
  have : Epi pb.g := hpb.epi_g
  have : Epi φ.τ₁ := hcol₁.epi_g
  have : Epi φ.τ₃ := inferInstanceAs (Epi (𝟙 (F₃.obj T.X₂)))
  have he : Epi e := ShortComplex.epi_τ₂_of_exact_of_epi φ hpb.exact
  have : Mono col₁.f := hcol₁.mono_f
  have : Mono (row T.X₂).f := (hrow T.X₂).mono_f
  have : Mono (row T.X₃).f := (hrow T.X₃).mono_f
  have ha : Mono a := inferInstanceAs (Mono (col₁.f ≫ (row T.X₂).f))
  have hae : a ≫ e = 0 := by
    apply pullback.hom_ext
    · rw [assoc, efst, zero_comp]
      change (col₁.f ≫ (row T.X₂).f) ≫ (row T.X₂).g = 0
      rw [assoc, ShortComplex.zero, comp_zero]
    · rw [assoc, esnd, zero_comp]
      dsimp only [a]
      rw [assoc, ← i.naturality T.g, ← assoc]
      change (col₁.f ≫ col₁.g) ≫ (row T.X₃).f = 0
      rw [ShortComplex.zero, zero_comp]
  let central := ShortComplex.mk a e hae
  have hcentral : central.ShortExact := by
    refine { mono_f := ha, epi_g := he, exact := ?_ }
    apply ShortComplex.exact_of_f_is_kernel
    apply KernelFork.IsLimit.ofι'
    intro A z hz
    have hzq : z ≫ (row T.X₂).g = 0 := by
      change z ≫ j.app T.X₂ = 0
      simpa only [central, assoc, efst, zero_comp] using
        congrArg (fun m => m ≫ pullback.fst q r) hz
    let d := (hrow T.X₂).exact.lift z hzq
    have hd : d ≫ i.app T.X₂ = z := (hrow T.X₂).exact.lift_f z hzq
    have hdz : d ≫ col₁.g = 0 := by
      apply (cancel_mono (row T.X₃).f).mp
      have hz' : z ≫ F₂.map T.g = 0 := by
        simpa only [central, assoc, esnd, zero_comp] using
          congrArg (fun m => m ≫ pullback.snd q r) hz
      change (d ≫ F₁.map T.g) ≫ i.app T.X₃ = 0 ≫ _
      rw [assoc, i.naturality, ← assoc, hd, hz', zero_comp]
    refine ⟨hcol₁.exact.lift d hdz, ?_⟩
    have hl : hcol₁.exact.lift d hdz ≫ F₁.map T.f = d :=
      hcol₁.exact.lift_f d hdz
    change hcol₁.exact.lift d hdz ≫
      (F₁.map T.f ≫ i.app T.X₂) = z
    rw [← assoc, hl, hd]
  let sq := IsPullback.of_hasPullback q r
  let B := sq.shortComplex'
  have : Epi q := hcol₃.epi_g
  have hB : B.ShortExact := by
    refine
      { exact := sq.exact_shortComplex'
        mono_f := sq.mono_shortComplex'_f
        epi_g := ?_ }
    exact epi_of_epi_fac (show biprod.inl ≫ B.g = q by simp [B])
  let top : row T.X₁ ⟶ central := ShortComplex.homMk (𝟙 _)
    (F₂.map T.f) iC
    (by simp [central, a, row])
    (by
      apply pullback.hom_ext
      · simp [central, e, iC, row, q, r]
      · simp [central, e, iC, row, ← Functor.map_comp])
  let left : col₁ ⟶ central := ShortComplex.homMk (𝟙 _)
    (i.app T.X₂) iG
    (by simp [central, a, col₁])
    (by simpa [φ, pb, ShortComplex.pullbackShortComplex, central, iG, col₁, row] using
      φ.comm₁₂.symm)
  let right : col₃ ⟶ B := ShortComplex.homMk iC biprod.inl (𝟙 _)
    (by
      change iC ≫ biprod.lift (pullback.fst q r) (pullback.snd q r) =
        F₃.map T.f ≫ biprod.inl
      apply biprod.hom_ext <;> simp [iC, q, r])
    (by simp [B, col₃, q])
  let bottom : row T.X₃ ⟶ B := ShortComplex.homMk iG biprod.inr (-𝟙 _)
    (by
      change iG ≫ biprod.lift (pullback.fst q r) (pullback.snd q r) =
        i.app T.X₃ ≫ biprod.inr
      apply biprod.hom_ext <;> simp [iG, q, r])
    (by simp [B, row, r])
  have htop : (hrow T.X₁).extClass =
      (Ext.mk₀ iC).comp hcentral.extClass (zero_add 1) := by
    simpa [top] using (hrow T.X₁).extClass_naturality hcentral top
  have hleft : hcol₁.extClass =
      (Ext.mk₀ iG).comp hcentral.extClass (zero_add 1) := by
    simpa [left] using hcol₁.extClass_naturality hcentral left
  have hright : hcol₃.extClass.comp (Ext.mk₀ iC) (add_zero 1) = hB.extClass := by
    simpa [right] using hcol₃.extClass_naturality hB right
  have hbottom : (hrow T.X₃).extClass.comp (Ext.mk₀ iG) (add_zero 1) = -hB.extClass := by
    simpa [bottom] using (hrow T.X₃).extClass_naturality hB bottom
  rw [Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass]
  change (hrow T.X₃).extClass.comp hcol₁.extClass rfl =
    -(hcol₃.extClass.comp (hrow T.X₁).extClass rfl)
  rw [hleft, htop, ← Ext.comp_assoc_of_second_deg_zero,
    ← Ext.comp_assoc_of_second_deg_zero, hbottom, hright, Ext.neg_comp]

/-- Moving the original pointwise short exact row past any original Ext
class has the Koszul sign determined by that class's degree. -/
theorem exactFunctorRow_extClass_left {X Y : C} {q : ℕ}
    (y : Ext.{w} X Y q) :
    (hS X).extClass.comp (y.mapExactFunctor F₁) rfl =
      ((-1 : ℤ) ^ q) •
        (y.mapExactFunctor F₃).comp (hS Y).extClass (Nat.add_comm q 1) := by
  induction q generalizing X Y with
  | zero =>
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective X Y).surjective y
    let row (Z : C) := ShortComplex.mk (i.app Z) (j.app Z) (hij Z)
    let φ : row X ⟶ row Y := ShortComplex.homMk (F₁.map g) (F₂.map g) (F₃.map g)
      (i.naturality g) (j.naturality g)
    have hnat := (hS X).extClass_naturality (hS Y) φ
    simpa [φ, row, Ext.mapExactFunctor_mk₀] using hnat
  | succ q ih =>
    obtain ⟨M, f, hf, hz⟩ := Ext.exists_epi_mk₀_comp_eq_zero y
    let := hf
    let T := ShortComplex.kernelSequence f
    have hT : T.ShortExact := { exact := ShortComplex.kernelSequence_exact f, epi_g := hf }
    obtain ⟨y', rfl⟩ := Ext.contravariant_sequence_exact₃ hT Y y hz (Nat.add_comm 1 q)
    let ax (Z : C) := (hS Z).extClass
    let b₁ := hT.extClass.mapExactFunctor F₁
    let b₃ := hT.extClass.mapExactFunctor F₃
    let c₁ := y'.mapExactFunctor F₁
    let c₃ := y'.mapExactFunctor F₃
    have hfirst : (ax X).comp b₁ rfl = -(b₃.comp (ax (Limits.kernel f)) rfl) :=
      exactFunctorRow_extClass_extClass F₁ F₂ F₃ i j hij hS hT
    have hrest : (ax (Limits.kernel f)).comp c₁ rfl = ((-1 : ℤ) ^ q) •
        c₃.comp (ax Y) (Nat.add_comm q 1) := ih y'
    simp only [Ext.mapExactFunctor_comp]
    change (ax X).comp (b₁.comp c₁ (Nat.add_comm 1 q)) rfl =
      ((-1 : ℤ) ^ (q + 1)) •
        (b₃.comp c₃ (Nat.add_comm 1 q)).comp (ax Y) (Nat.add_comm (q + 1) 1)
    calc
      _ = ((ax X).comp b₁ rfl).comp c₁ (by omega) :=
        (Ext.comp_assoc _ _ _ rfl (Nat.add_comm 1 q) (by omega)).symm
      _ = -(b₃.comp ((ax (Limits.kernel f)).comp c₁ rfl) (by omega)) := by
        rw [hfirst, Ext.neg_comp, Ext.comp_assoc _ _ _ rfl rfl (by omega)]
      _ = -(b₃.comp (((-1 : ℤ) ^ q) •
          c₃.comp (ax Y) (Nat.add_comm q 1)) (by omega)) := by rw [hrest]
      _ = _ := by
        rw [Ext.comp_zsmul,
          ← Ext.comp_assoc _ _ _ (Nat.add_comm 1 q) (Nat.add_comm q 1) (by omega)]
        simp only [pow_succ, mul_neg, mul_one, neg_smul]


end CategoryTheory.Functor

end
