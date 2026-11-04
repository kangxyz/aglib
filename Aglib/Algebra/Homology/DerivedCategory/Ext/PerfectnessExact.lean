/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.Dual
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.Tactic.Abel

/-!
# Perfectness on the middle coefficient of an actual Ext sequence

The two Ext worlds, original additive actions and exact coefficient functor
are retained. Coefficient naturality and the two unsigned extension-class
value laws derive all six original adjoint rows. Exact dualization over the
positive ZMod ring needs no finiteness hypothesis on the carriers. The current
consumer is the native constructible etale trace pairing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

private theorem original_five_bijective
    {A₀ : Type*} {A₁ : Type*} {A₂ : Type*} {A₃ : Type*} {A₄ : Type*}
    {B₀ : Type*} {B₁ : Type*} {B₂ : Type*} {B₃ : Type*} {B₄ : Type*}
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup A₃] [AddCommGroup A₄]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup B₃] [AddCommGroup B₄]
    (f₀ : A₀ →+ A₁) (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄)
    (g₀ : B₀ →+ B₁) (g₁ : B₁ →+ B₂) (g₂ : B₂ →+ B₃) (g₃ : B₃ →+ B₄)
    (a₀ : A₀ →+ B₀) (a₁ : A₁ →+ B₁) (a₂ : A₂ →+ B₂)
    (a₃ : A₃ →+ B₃) (a₄ : A₄ →+ B₄)
    (hf₀ : Function.Exact f₀ f₁) (hf₁ : Function.Exact f₁ f₂)
    (hf₂ : Function.Exact f₂ f₃)
    (hg₀ : Function.Exact g₀ g₁) (hg₁ : Function.Exact g₁ g₂)
    (hg₂ : Function.Exact g₂ g₃)
    (h₀ : a₁.comp f₀ = g₀.comp a₀) (h₁ : a₂.comp f₁ = g₁.comp a₁)
    (h₂ : a₃.comp f₂ = g₂.comp a₂) (h₃ : a₄.comp f₃ = g₃.comp a₃)
    (ha₀ : Function.Surjective a₀) (ha₁ : Function.Bijective a₁)
    (ha₃ : Function.Bijective a₃) (ha₄ : Function.Injective a₄) :
    Function.Bijective a₂ := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    have hx₂ : f₂ x = 0 := by
      apply ha₃.injective
      calc
        a₃ (f₂ x) = g₂ (a₂ x) := DFunLike.congr_fun h₂ x
        _ = 0 := by rw [hx, map_zero]
        _ = a₃ 0 := (map_zero _).symm
    obtain ⟨y, hy⟩ := (hf₁ x).mp hx₂
    have hy₁ : g₁ (a₁ y) = 0 := by
      calc
        g₁ (a₁ y) = a₂ (f₁ y) := (DFunLike.congr_fun h₁ y).symm
        _ = 0 := by rw [hy, hx]
    obtain ⟨z, hz⟩ := (hg₀ (a₁ y)).mp hy₁
    obtain ⟨w, hw⟩ := ha₀ z
    have hw₁ : f₀ w = y := by
      apply ha₁.injective
      calc
        a₁ (f₀ w) = g₀ (a₀ w) := DFunLike.congr_fun h₀ w
        _ = g₀ z := congrArg g₀ hw
        _ = a₁ y := hz
    calc
      x = f₁ y := hy.symm
      _ = f₁ (f₀ w) := congrArg f₁ hw₁.symm
      _ = 0 := (hf₀ (f₀ w)).mpr ⟨w, rfl⟩
  · intro y
    obtain ⟨d, hd⟩ := ha₃.surjective (g₂ y)
    have hd₃ : f₃ d = 0 := by
      apply ha₄
      calc
        a₄ (f₃ d) = g₃ (a₃ d) := DFunLike.congr_fun h₃ d
        _ = g₃ (g₂ y) := congrArg g₃ hd
        _ = 0 := (hg₂ (g₂ y)).mpr ⟨y, rfl⟩
        _ = a₄ 0 := (map_zero _).symm
    obtain ⟨c, hc⟩ := (hf₂ d).mp hd₃
    have hy₂ : g₂ (y - a₂ c) = 0 := by
      have h₂c : a₃ (f₂ c) = g₂ (a₂ c) := DFunLike.congr_fun h₂ c
      rw [map_sub, ← h₂c, hc, hd, sub_self]
    obtain ⟨b, hb⟩ := (hg₁ (y - a₂ c)).mp hy₂
    obtain ⟨a, ha⟩ := ha₁.surjective b
    refine ⟨c + f₁ a, ?_⟩
    have h₁a : a₂ (f₁ a) = g₁ (a₁ a) := DFunLike.congr_fun h₁ a
    rw [map_add, h₁a, ha, hb]
    abel


private theorem original_exact_zero_left
    {Z : Type*} {A : Type*} {B : Type*}
    [AddCommGroup Z] [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Injective f) : Function.Exact (0 : Z →+ A) f := by
  intro a
  constructor
  · intro ha
    refine ⟨0, ?_⟩
    exact (hf (ha.trans (map_zero _).symm)).symm
  · rintro ⟨u, rfl⟩
    exact map_zero _

private theorem original_exact_zero_right
    {Z : Type*} {A : Type*} {B : Type*}
    [AddCommGroup Z] [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Surjective f) : Function.Exact f (0 : B →+ Z) := by
  intro b
  constructor
  · intro _
    exact hf b
  · intro _
    rfl


private theorem original_dual_subsingleton
    (R : Type*) [Semiring R] (M : Type*) [AddCommGroup M] [Module R M]
    [Subsingleton M] : Subsingleton (Module.Dual R M) := by
  refine ⟨fun f g => ?_⟩
  ext x
  rw [Subsingleton.elim x 0, map_zero, map_zero]


universe uC vC uD vD wE wH

namespace CategoryTheory.Abelian.Ext

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wE} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wH} D]
  (L : C ⥤ D) [L.Additive] (A : D) (N : C) (n : ℕ) (hn : 0 < n)
  [compactModule : ∀ (F : C) (q : ℕ), Module (ZMod n) (Ext.{wH} A (L.obj F) q)]
  [sourceModule : ∀ (F : C) (q : ℕ), Module (ZMod n) (Ext.{wE} F N q)]

omit [HasExt.{wE} C] in
private def compactMap {F G : C} (f : F ⟶ G) (q : ℕ) :
    Ext.{wH} A (L.obj F) q →ₗ[ZMod n] Ext.{wH} A (L.obj G) q :=
  AddMonoidHom.toZModLinearMap n ((Ext.mk₀ (L.map f)).postcomp A (add_zero q))

private def sourceMap {F G : C} (f : F ⟶ G) (q : ℕ) :
    Ext.{wE} G N q →ₗ[ZMod n] Ext.{wE} F N q :=
  AddMonoidHom.toZModLinearMap n ((Ext.mk₀ f).precomp N (zero_add q))

omit [HasExt.{wE} C] in
private def compactBoundary {S : ShortComplex C} (hL : (S.map L).ShortExact)
    (q q' : ℕ) (hq : q + 1 = q') :
    Ext.{wH} A (L.obj S.X₃) q →ₗ[ZMod n] Ext.{wH} A (L.obj S.X₁) q' := by
  let : Module (ZMod n) (Ext.{wH} A (S.map L).X₃ q) :=
    inferInstanceAs (Module (ZMod n) (Ext.{wH} A (L.obj S.X₃) q))
  let : Module (ZMod n) (Ext.{wH} A (S.map L).X₁ q') :=
    inferInstanceAs (Module (ZMod n) (Ext.{wH} A (L.obj S.X₁) q'))
  exact AddMonoidHom.toZModLinearMap n (hL.extClass.postcomp A hq)

private def sourceBoundary {S : ShortComplex C} (hS : S.ShortExact)
    (q q' : ℕ) (hq : 1 + q = q') :
    Ext.{wE} S.X₁ N q →ₗ[ZMod n] Ext.{wE} S.X₃ N q' :=
  AddMonoidHom.toZModLinearMap n (hS.extClass.precomp N hq)

omit [HasExt.{wE} C] in
private theorem compact_exact₂ {S : ShortComplex C} (hL : (S.map L).ShortExact) (q : ℕ) :
    Function.Exact (compactMap L A n S.f q) (compactMap L A n S.g q) := by
  have h := Ext.covariant_sequence_exact₂' A hL q
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

omit [HasExt.{wE} C] in
private theorem compact_exact₃ {S : ShortComplex C} (hL : (S.map L).ShortExact)
    (q q' : ℕ) (hq : q + 1 = q') :
    Function.Exact (compactMap L A n S.g q) (compactBoundary L A n hL q q' hq) := by
  have h := Ext.covariant_sequence_exact₃' A hL q q' hq
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

omit [HasExt.{wE} C] in
private theorem compact_exact₁ {S : ShortComplex C} (hL : (S.map L).ShortExact)
    (q q' : ℕ) (hq : q + 1 = q') :
    Function.Exact (compactBoundary L A n hL q q' hq) (compactMap L A n S.f q') := by
  have h := Ext.covariant_sequence_exact₁' A hL q q' hq
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

private theorem source_exact₂ {S : ShortComplex C} (hS : S.ShortExact) (q : ℕ) :
    Function.Exact (sourceMap N n S.g q) (sourceMap N n S.f q) := by
  have h := Ext.contravariant_sequence_exact₂' hS N q
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

private theorem source_exact₁ {S : ShortComplex C} (hS : S.ShortExact)
    (q q' : ℕ) (hq : 1 + q = q') :
    Function.Exact (sourceMap N n S.f q) (sourceBoundary N n hS q q' hq) := by
  have h := Ext.contravariant_sequence_exact₁' hS N q q' hq
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

private theorem source_exact₃ {S : ShortComplex C} (hS : S.ShortExact)
    (q q' : ℕ) (hq : 1 + q = q') :
    Function.Exact (sourceBoundary N n hS q q' hq) (sourceMap N n S.g q') := by
  have h := Ext.contravariant_sequence_exact₃' hS N q q' hq
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

omit [HasExt.{wE} C] in
private theorem compact_zero_injective {S : ShortComplex C} (hL : (S.map L).ShortExact) :
    Function.Injective (compactMap L A n S.f 0) := by
  let : Mono (L.map S.f) := hL.mono_f
  exact Ext.postcomp_mk₀_injective_of_mono A (L.map S.f)

private theorem source_zero_injective {S : ShortComplex C} (hS : S.ShortExact)
    (q : ℕ) (hq : q = 0) : Function.Injective (sourceMap N n S.g q) := by
  subst q
  let : Epi S.g := hS.epi_g
  exact Ext.precomp_mk₀_injective_of_epi N S.g

omit [L.Additive] in
private theorem pair_naturality
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP : ∀ {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2)
      (c : Ext.{wH} A (L.obj F) r) (e : Ext.{wE} G N (2 - r)),
      P G r hr (c.comp (Ext.mk₀ (L.map f)) (add_zero r)) e =
        P F r hr c ((Ext.mk₀ f).comp e (zero_add (2 - r))))
    {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2) :
    (P G r hr).comp (compactMap L A n f r) =
      (sourceMap N n f (2 - r)).dualMap.comp (P F r hr) := by
  ext c e
  exact hP f r hr c e

omit [L.Additive] in
private theorem pair_flip_naturality
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP : ∀ {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2)
      (c : Ext.{wH} A (L.obj F) r) (e : Ext.{wE} G N (2 - r)),
      P G r hr (c.comp (Ext.mk₀ (L.map f)) (add_zero r)) e =
        P F r hr c ((Ext.mk₀ f).comp e (zero_add (2 - r))))
    {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2) :
    (P F r hr).flip.comp (sourceMap N n f (2 - r)) =
      (compactMap L A n f r).dualMap.comp (P G r hr).flip := by
  ext e c
  exact (hP f r hr c e).symm

private theorem pair_boundary_zero
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP0 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 0) (e : Ext.{wE} S.X₁ N (2 - 1)),
      P S.X₁ 1 (by decide) (c.comp hL.extClass (show 0 + 1 = 1 from rfl)) e =
        P S.X₃ 0 (by decide) c (hS.extClass.comp e (show 1 + (2 - 1) = (2 - 0 : ℕ) from by
          omega))) :
    (P S.X₁ 1 (by decide)).comp (compactBoundary L A n hL 0 1 rfl) =
      (sourceBoundary N n hS (2 - 1) (2 - 0) (by omega)).dualMap.comp (P S.X₃ 0 (by decide)) := by
  ext c e
  exact hP0 c e

private theorem pair_boundary_one
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP1 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 1) (e : Ext.{wE} S.X₁ N (2 - 2)),
      P S.X₁ 2 (by decide) (c.comp hL.extClass (show 1 + 1 = 2 from rfl)) e =
        P S.X₃ 1 (by decide) c (hS.extClass.comp e (show 1 + (2 - 2) = (2 - 1 : ℕ) from by
          omega))) :
    (P S.X₁ 2 (by decide)).comp (compactBoundary L A n hL 1 2 rfl) =
      (sourceBoundary N n hS (2 - 2) (2 - 1) (by omega)).dualMap.comp (P S.X₃ 1 (by decide)) := by
  ext c e
  exact hP1 c e

private theorem pair_flip_boundary_zero
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP1 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 1) (e : Ext.{wE} S.X₁ N (2 - 2)),
      P S.X₁ 2 (by decide) (c.comp hL.extClass (show 1 + 1 = 2 from rfl)) e =
        P S.X₃ 1 (by decide) c (hS.extClass.comp e (show 1 + (2 - 2) = (2 - 1 : ℕ) from by
          omega))) :
    (P S.X₃ 1 (by decide)).flip.comp (sourceBoundary N n hS (2 - 2) (2 - 1) (by omega)) =
      (compactBoundary L A n hL 1 2 rfl).dualMap.comp (P S.X₁ 2 (by decide)).flip := by
  ext e c
  exact (hP1 c e).symm

private theorem pair_flip_boundary_one
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP0 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 0) (e : Ext.{wE} S.X₁ N (2 - 1)),
      P S.X₁ 1 (by decide) (c.comp hL.extClass (show 0 + 1 = 1 from rfl)) e =
        P S.X₃ 0 (by decide) c (hS.extClass.comp e (show 1 + (2 - 1) = (2 - 0 : ℕ) from by
          omega))) :
    (P S.X₃ 0 (by decide)).flip.comp (sourceBoundary N n hS (2 - 1) (2 - 0) (by omega)) =
      (compactBoundary L A n hL 0 1 rfl).dualMap.comp (P S.X₁ 1 (by decide)).flip := by
  ext e c
  exact (hP0 c e).symm

include hn in
private theorem middle_phi_0
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP : ∀ {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2)
      (c : Ext.{wH} A (L.obj F) r) (e : Ext.{wE} G N (2 - r)),
      P G r hr (c.comp (Ext.mk₀ (L.map f)) (add_zero r)) e =
        P F r hr c ((Ext.mk₀ f).comp e (zero_add (2 - r))))
    (hP0 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 0) (e : Ext.{wE} S.X₁ N (2 - 1)),
      P S.X₁ 1 (by decide) (c.comp hL.extClass (show 0 + 1 = 1 from rfl)) e =
        P S.X₃ 0 (by decide) c (hS.extClass.comp e (show 1 + (2 - 1) = (2 - 0 : ℕ) from by omega)))
    (h1 : Function.Bijective (P S.X₁ 0 (by decide)))
    (h3 : Function.Bijective (P S.X₃ 0 (by decide)))
    (h4 : Function.Injective (P S.X₁ 1 (by decide)))
    (hEQ : Subsingleton (Ext.{wE} S.X₃ N 3))
    : Function.Bijective (P S.X₂ 0 (by decide)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Cg := fun F q => Ext.{wH} A (L.obj F) q
  let Eg := fun F q => Ext.{wE} F N q
  let : Subsingleton (Eg S.X₃ 3) := hEQ
  let : Subsingleton (Module.Dual (ZMod n) (Eg S.X₃ 3)) :=
    original_dual_subsingleton (ZMod n) (Eg S.X₃ 3)
  exact original_five_bijective
    (0 : Cg S.X₁ 3 →+ Cg S.X₁ 0)
    ((compactMap L A n S.f 0)).toAddMonoidHom
    ((compactMap L A n S.g 0)).toAddMonoidHom
    ((compactBoundary L A n hL 0 1 rfl)).toAddMonoidHom
    ((sourceBoundary N n hS (2 - 0) 3 (by omega)).dualMap).toAddMonoidHom
    ((sourceMap N n S.f (2 - 0)).dualMap).toAddMonoidHom
    ((sourceMap N n S.g (2 - 0)).dualMap).toAddMonoidHom
    ((sourceBoundary N n hS (2 - 1) (2 - 0) (by omega)).dualMap).toAddMonoidHom
    (0 : Cg S.X₁ 3 →+ Module.Dual (ZMod n) (Eg S.X₃ 3))
    ((P S.X₁ 0 (by decide))).toAddMonoidHom
    ((P S.X₂ 0 (by decide))).toAddMonoidHom
    ((P S.X₃ 0 (by decide))).toAddMonoidHom
    ((P S.X₁ 1 (by decide))).toAddMonoidHom
    (original_exact_zero_left (compactMap L A n S.f 0).toAddMonoidHom
      (compact_zero_injective L A n hL))
    (compact_exact₂ L A n hL 0)
    (compact_exact₃ L A n hL 0 1 rfl)
    (ZMod.dualMap_exact n (sourceMap N n S.f (2 - 0)) (sourceBoundary N n hS (2 - 0) 3 (by omega))
      (source_exact₁ N n hS (2 - 0) 3 (by omega)))
    (ZMod.dualMap_exact n (sourceMap N n S.g (2 - 0)) (sourceMap N n S.f (2 - 0))
      (source_exact₂ N n hS (2 - 0)))
    (ZMod.dualMap_exact n (sourceBoundary N n hS (2 - 1) (2 - 0) (by omega)) (sourceMap N n S.g (2
      - 0))
      (source_exact₃ N n hS (2 - 1) (2 - 0) (by omega)))
    (by ext x; simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, map_zero])
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_naturality L A N n P hP S.f 0 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_naturality L A N n P hP S.g 0 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_boundary_zero L A N n hS hL P hP0) c) e)
    (by intro x; exact ⟨0, Subsingleton.elim _ _⟩)
    h1
    h3
    h4

include hn in
private theorem middle_phi_1
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP : ∀ {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2)
      (c : Ext.{wH} A (L.obj F) r) (e : Ext.{wE} G N (2 - r)),
      P G r hr (c.comp (Ext.mk₀ (L.map f)) (add_zero r)) e =
        P F r hr c ((Ext.mk₀ f).comp e (zero_add (2 - r))))
    (hP0 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 0) (e : Ext.{wE} S.X₁ N (2 - 1)),
      P S.X₁ 1 (by decide) (c.comp hL.extClass (show 0 + 1 = 1 from rfl)) e =
        P S.X₃ 0 (by decide) c (hS.extClass.comp e (show 1 + (2 - 1) = (2 - 0 : ℕ) from by omega)))
    (hP1 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 1) (e : Ext.{wE} S.X₁ N (2 - 2)),
      P S.X₁ 2 (by decide) (c.comp hL.extClass (show 1 + 1 = 2 from rfl)) e =
        P S.X₃ 1 (by decide) c (hS.extClass.comp e (show 1 + (2 - 2) = (2 - 1 : ℕ) from by omega)))
    (h0 : Function.Surjective (P S.X₃ 0 (by decide)))
    (h1 : Function.Bijective (P S.X₁ 1 (by decide)))
    (h3 : Function.Bijective (P S.X₃ 1 (by decide)))
    (h4 : Function.Injective (P S.X₁ 2 (by decide)))
    : Function.Bijective (P S.X₂ 1 (by decide)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Cg := fun F q => Ext.{wH} A (L.obj F) q
  let Eg := fun F q => Ext.{wE} F N q
  exact original_five_bijective
    ((compactBoundary L A n hL 0 1 rfl)).toAddMonoidHom
    ((compactMap L A n S.f 1)).toAddMonoidHom
    ((compactMap L A n S.g 1)).toAddMonoidHom
    ((compactBoundary L A n hL 1 2 rfl)).toAddMonoidHom
    ((sourceBoundary N n hS (2 - 1) (2 - 0) (by omega)).dualMap).toAddMonoidHom
    ((sourceMap N n S.f (2 - 1)).dualMap).toAddMonoidHom
    ((sourceMap N n S.g (2 - 1)).dualMap).toAddMonoidHom
    ((sourceBoundary N n hS (2 - 2) (2 - 1) (by omega)).dualMap).toAddMonoidHom
    ((P S.X₃ 0 (by decide))).toAddMonoidHom
    ((P S.X₁ 1 (by decide))).toAddMonoidHom
    ((P S.X₂ 1 (by decide))).toAddMonoidHom
    ((P S.X₃ 1 (by decide))).toAddMonoidHom
    ((P S.X₁ 2 (by decide))).toAddMonoidHom
    (compact_exact₁ L A n hL 0 1 rfl)
    (compact_exact₂ L A n hL 1)
    (compact_exact₃ L A n hL 1 2 rfl)
    (ZMod.dualMap_exact n (sourceMap N n S.f (2 - 1)) (sourceBoundary N n hS (2 - 1) (2 - 0) (by
      omega))
      (source_exact₁ N n hS (2 - 1) (2 - 0) (by omega)))
    (ZMod.dualMap_exact n (sourceMap N n S.g (2 - 1)) (sourceMap N n S.f (2 - 1))
      (source_exact₂ N n hS (2 - 1)))
    (ZMod.dualMap_exact n (sourceBoundary N n hS (2 - 2) (2 - 1) (by omega)) (sourceMap N n S.g (2
      - 1))
      (source_exact₃ N n hS (2 - 2) (2 - 1) (by omega)))
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_boundary_zero L A N n hS hL P hP0) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_naturality L A N n P hP S.f 1 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_naturality L A N n P hP S.g 1 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_boundary_one L A N n hS hL P hP1) c) e)
    h0
    h1
    h3
    h4

include hn in
private theorem middle_phi_2
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP : ∀ {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2)
      (c : Ext.{wH} A (L.obj F) r) (e : Ext.{wE} G N (2 - r)),
      P G r hr (c.comp (Ext.mk₀ (L.map f)) (add_zero r)) e =
        P F r hr c ((Ext.mk₀ f).comp e (zero_add (2 - r))))
    (hP1 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 1) (e : Ext.{wE} S.X₁ N (2 - 2)),
      P S.X₁ 2 (by decide) (c.comp hL.extClass (show 1 + 1 = 2 from rfl)) e =
        P S.X₃ 1 (by decide) c (hS.extClass.comp e (show 1 + (2 - 2) = (2 - 1 : ℕ) from by omega)))
    (h0 : Function.Surjective (P S.X₃ 1 (by decide)))
    (h1 : Function.Bijective (P S.X₁ 2 (by decide)))
    (h3 : Function.Bijective (P S.X₃ 2 (by decide)))
    (hCA : Subsingleton (Ext.{wH} A (L.obj S.X₁) 3))
    : Function.Bijective (P S.X₂ 2 (by decide)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Cg := fun F q => Ext.{wH} A (L.obj F) q
  let Eg := fun F q => Ext.{wE} F N q
  let : Subsingleton (Cg S.X₁ 3) := hCA
  exact original_five_bijective
    ((compactBoundary L A n hL 1 2 rfl)).toAddMonoidHom
    ((compactMap L A n S.f 2)).toAddMonoidHom
    ((compactMap L A n S.g 2)).toAddMonoidHom
    ((compactBoundary L A n hL 2 3 rfl)).toAddMonoidHom
    ((sourceBoundary N n hS (2 - 2) (2 - 1) (by omega)).dualMap).toAddMonoidHom
    ((sourceMap N n S.f (2 - 2)).dualMap).toAddMonoidHom
    ((sourceMap N n S.g (2 - 2)).dualMap).toAddMonoidHom
    (0 : Module.Dual (ZMod n) (Eg S.X₃ (2 - 2)) →+ Module.Dual (ZMod n) (Eg S.X₃ 3))
    ((P S.X₃ 1 (by decide))).toAddMonoidHom
    ((P S.X₁ 2 (by decide))).toAddMonoidHom
    ((P S.X₂ 2 (by decide))).toAddMonoidHom
    ((P S.X₃ 2 (by decide))).toAddMonoidHom
    (0 : Cg S.X₁ 3 →+ Module.Dual (ZMod n) (Eg S.X₃ 3))
    (compact_exact₁ L A n hL 1 2 rfl)
    (compact_exact₂ L A n hL 2)
    (compact_exact₃ L A n hL 2 3 rfl)
    (ZMod.dualMap_exact n (sourceMap N n S.f (2 - 2)) (sourceBoundary N n hS (2 - 2) (2 - 1) (by
      omega))
      (source_exact₁ N n hS (2 - 2) (2 - 1) (by omega)))
    (ZMod.dualMap_exact n (sourceMap N n S.g (2 - 2)) (sourceMap N n S.f (2 - 2))
      (source_exact₂ N n hS (2 - 2)))
    (original_exact_zero_right (sourceMap N n S.g (2 - 2)).dualMap.toAddMonoidHom
      (ZMod.dualMap_surjective n (sourceMap N n S.g (2 - 2)) (source_zero_injective N n hS (2 - 2)
        (by omega))))
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_boundary_one L A N n hS hL P hP1) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_naturality L A N n P hP S.f 2 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_naturality L A N n P hP S.g 2 (by
        decide)) c) e)
    (by ext x; simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply])
    h0
    h1
    h3
    (by intro x y h; exact Subsingleton.elim _ _)

include hn in
private theorem middle_psi_0
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP : ∀ {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2)
      (c : Ext.{wH} A (L.obj F) r) (e : Ext.{wE} G N (2 - r)),
      P G r hr (c.comp (Ext.mk₀ (L.map f)) (add_zero r)) e =
        P F r hr c ((Ext.mk₀ f).comp e (zero_add (2 - r))))
    (hP1 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 1) (e : Ext.{wE} S.X₁ N (2 - 2)),
      P S.X₁ 2 (by decide) (c.comp hL.extClass (show 1 + 1 = 2 from rfl)) e =
        P S.X₃ 1 (by decide) c (hS.extClass.comp e (show 1 + (2 - 2) = (2 - 1 : ℕ) from by omega)))
    (h1 : Function.Bijective (P S.X₃ 2 (by decide)).flip)
    (h3 : Function.Bijective (P S.X₁ 2 (by decide)).flip)
    (h4 : Function.Injective (P S.X₃ 1 (by decide)).flip)
    (hCA : Subsingleton (Ext.{wH} A (L.obj S.X₁) 3))
    : Function.Bijective (P S.X₂ 2 (by decide)).flip := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Cg := fun F q => Ext.{wH} A (L.obj F) q
  let Eg := fun F q => Ext.{wE} F N q
  let : Subsingleton (Cg S.X₁ 3) := hCA
  let : Subsingleton (Module.Dual (ZMod n) (Cg S.X₁ 3)) :=
    original_dual_subsingleton (ZMod n) (Cg S.X₁ 3)
  exact original_five_bijective
    (0 : Eg S.X₃ 3 →+ Eg S.X₃ (2 - 2))
    ((sourceMap N n S.g (2 - 2))).toAddMonoidHom
    ((sourceMap N n S.f (2 - 2))).toAddMonoidHom
    ((sourceBoundary N n hS (2 - 2) (2 - 1) (by omega))).toAddMonoidHom
    ((compactBoundary L A n hL 2 3 rfl).dualMap).toAddMonoidHom
    ((compactMap L A n S.g 2).dualMap).toAddMonoidHom
    ((compactMap L A n S.f 2).dualMap).toAddMonoidHom
    ((compactBoundary L A n hL 1 2 rfl).dualMap).toAddMonoidHom
    (0 : Eg S.X₃ 3 →+ Module.Dual (ZMod n) (Cg S.X₁ 3))
    ((P S.X₃ 2 (by decide)).flip).toAddMonoidHom
    ((P S.X₂ 2 (by decide)).flip).toAddMonoidHom
    ((P S.X₁ 2 (by decide)).flip).toAddMonoidHom
    ((P S.X₃ 1 (by decide)).flip).toAddMonoidHom
    (original_exact_zero_left (sourceMap N n S.g (2 - 2)).toAddMonoidHom
      (source_zero_injective N n hS (2 - 2) (by omega)))
    (source_exact₂ N n hS (2 - 2))
    (source_exact₁ N n hS (2 - 2) (2 - 1) (by omega))
    (ZMod.dualMap_exact n (compactMap L A n S.g 2) (compactBoundary L A n hL 2 3 rfl)
      (compact_exact₃ L A n hL 2 3 rfl))
    (ZMod.dualMap_exact n (compactMap L A n S.f 2) (compactMap L A n S.g 2)
      (compact_exact₂ L A n hL 2))
    (ZMod.dualMap_exact n (compactBoundary L A n hL 1 2 rfl) (compactMap L A n S.f 2)
      (compact_exact₁ L A n hL 1 2 rfl))
    (by ext x; simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, map_zero])
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_naturality L A N n P hP S.g 2 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_naturality L A N n P hP S.f 2 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_boundary_zero L A N n hS hL P hP1)
        c) e)
    (by intro x; exact ⟨0, Subsingleton.elim _ _⟩)
    h1
    h3
    h4

include hn in
private theorem middle_psi_1
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP : ∀ {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2)
      (c : Ext.{wH} A (L.obj F) r) (e : Ext.{wE} G N (2 - r)),
      P G r hr (c.comp (Ext.mk₀ (L.map f)) (add_zero r)) e =
        P F r hr c ((Ext.mk₀ f).comp e (zero_add (2 - r))))
    (hP0 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 0) (e : Ext.{wE} S.X₁ N (2 - 1)),
      P S.X₁ 1 (by decide) (c.comp hL.extClass (show 0 + 1 = 1 from rfl)) e =
        P S.X₃ 0 (by decide) c (hS.extClass.comp e (show 1 + (2 - 1) = (2 - 0 : ℕ) from by omega)))
    (hP1 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 1) (e : Ext.{wE} S.X₁ N (2 - 2)),
      P S.X₁ 2 (by decide) (c.comp hL.extClass (show 1 + 1 = 2 from rfl)) e =
        P S.X₃ 1 (by decide) c (hS.extClass.comp e (show 1 + (2 - 2) = (2 - 1 : ℕ) from by omega)))
    (h0 : Function.Surjective (P S.X₁ 2 (by decide)).flip)
    (h1 : Function.Bijective (P S.X₃ 1 (by decide)).flip)
    (h3 : Function.Bijective (P S.X₁ 1 (by decide)).flip)
    (h4 : Function.Injective (P S.X₃ 0 (by decide)).flip)
    : Function.Bijective (P S.X₂ 1 (by decide)).flip := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Cg := fun F q => Ext.{wH} A (L.obj F) q
  let Eg := fun F q => Ext.{wE} F N q
  exact original_five_bijective
    ((sourceBoundary N n hS (2 - 2) (2 - 1) (by omega))).toAddMonoidHom
    ((sourceMap N n S.g (2 - 1))).toAddMonoidHom
    ((sourceMap N n S.f (2 - 1))).toAddMonoidHom
    ((sourceBoundary N n hS (2 - 1) (2 - 0) (by omega))).toAddMonoidHom
    ((compactBoundary L A n hL 1 2 rfl).dualMap).toAddMonoidHom
    ((compactMap L A n S.g 1).dualMap).toAddMonoidHom
    ((compactMap L A n S.f 1).dualMap).toAddMonoidHom
    ((compactBoundary L A n hL 0 1 rfl).dualMap).toAddMonoidHom
    ((P S.X₁ 2 (by decide)).flip).toAddMonoidHom
    ((P S.X₃ 1 (by decide)).flip).toAddMonoidHom
    ((P S.X₂ 1 (by decide)).flip).toAddMonoidHom
    ((P S.X₁ 1 (by decide)).flip).toAddMonoidHom
    ((P S.X₃ 0 (by decide)).flip).toAddMonoidHom
    (source_exact₃ N n hS (2 - 2) (2 - 1) (by omega))
    (source_exact₂ N n hS (2 - 1))
    (source_exact₁ N n hS (2 - 1) (2 - 0) (by omega))
    (ZMod.dualMap_exact n (compactMap L A n S.g 1) (compactBoundary L A n hL 1 2 rfl)
      (compact_exact₃ L A n hL 1 2 rfl))
    (ZMod.dualMap_exact n (compactMap L A n S.f 1) (compactMap L A n S.g 1)
      (compact_exact₂ L A n hL 1))
    (ZMod.dualMap_exact n (compactBoundary L A n hL 0 1 rfl) (compactMap L A n S.f 1)
      (compact_exact₁ L A n hL 0 1 rfl))
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_boundary_zero L A N n hS hL P hP1)
        c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_naturality L A N n P hP S.g 1 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_naturality L A N n P hP S.f 1 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_boundary_one L A N n hS hL P hP0)
        c) e)
    h0
    h1
    h3
    h4

include hn in
private theorem middle_psi_2
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP : ∀ {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2)
      (c : Ext.{wH} A (L.obj F) r) (e : Ext.{wE} G N (2 - r)),
      P G r hr (c.comp (Ext.mk₀ (L.map f)) (add_zero r)) e =
        P F r hr c ((Ext.mk₀ f).comp e (zero_add (2 - r))))
    (hP0 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 0) (e : Ext.{wE} S.X₁ N (2 - 1)),
      P S.X₁ 1 (by decide) (c.comp hL.extClass (show 0 + 1 = 1 from rfl)) e =
        P S.X₃ 0 (by decide) c (hS.extClass.comp e (show 1 + (2 - 1) = (2 - 0 : ℕ) from by omega)))
    (h0 : Function.Surjective (P S.X₁ 1 (by decide)).flip)
    (h1 : Function.Bijective (P S.X₃ 0 (by decide)).flip)
    (h3 : Function.Bijective (P S.X₁ 0 (by decide)).flip)
    (hEQ : Subsingleton (Ext.{wE} S.X₃ N 3))
    : Function.Bijective (P S.X₂ 0 (by decide)).flip := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Cg := fun F q => Ext.{wH} A (L.obj F) q
  let Eg := fun F q => Ext.{wE} F N q
  let : Subsingleton (Eg S.X₃ 3) := hEQ
  exact original_five_bijective
    ((sourceBoundary N n hS (2 - 1) (2 - 0) (by omega))).toAddMonoidHom
    ((sourceMap N n S.g (2 - 0))).toAddMonoidHom
    ((sourceMap N n S.f (2 - 0))).toAddMonoidHom
    ((sourceBoundary N n hS (2 - 0) 3 (by omega))).toAddMonoidHom
    ((compactBoundary L A n hL 0 1 rfl).dualMap).toAddMonoidHom
    ((compactMap L A n S.g 0).dualMap).toAddMonoidHom
    ((compactMap L A n S.f 0).dualMap).toAddMonoidHom
    (0 : Module.Dual (ZMod n) (Cg S.X₁ 0) →+ Module.Dual (ZMod n) (Cg S.X₁ 3))
    ((P S.X₁ 1 (by decide)).flip).toAddMonoidHom
    ((P S.X₃ 0 (by decide)).flip).toAddMonoidHom
    ((P S.X₂ 0 (by decide)).flip).toAddMonoidHom
    ((P S.X₁ 0 (by decide)).flip).toAddMonoidHom
    (0 : Eg S.X₃ 3 →+ Module.Dual (ZMod n) (Cg S.X₁ 3))
    (source_exact₃ N n hS (2 - 1) (2 - 0) (by omega))
    (source_exact₂ N n hS (2 - 0))
    (source_exact₁ N n hS (2 - 0) 3 (by omega))
    (ZMod.dualMap_exact n (compactMap L A n S.g 0) (compactBoundary L A n hL 0 1 rfl)
      (compact_exact₃ L A n hL 0 1 rfl))
    (ZMod.dualMap_exact n (compactMap L A n S.f 0) (compactMap L A n S.g 0)
      (compact_exact₂ L A n hL 0))
    (original_exact_zero_right (compactMap L A n S.f 0).dualMap.toAddMonoidHom
      (ZMod.dualMap_surjective n (compactMap L A n S.f 0) (compact_zero_injective L A n hL)))
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_boundary_one L A N n hS hL P hP0)
        c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_naturality L A N n P hP S.g 0 (by
        decide)) c) e)
    (by
      ext c e
      exact LinearMap.congr_fun (LinearMap.congr_fun (pair_flip_naturality L A N n P hP S.f 0 (by
        decide)) c) e)
    (by ext x; simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply])
    h0
    h1
    h3
    (by intro x y h; exact Subsingleton.elim _ _)

include hn in
/-- Both adjoints of the given original Ext pairing pass to the actual
middle coefficient. All six rows use the same source and mapped short exact
sequences. The two displayed high groups are the only outside vanishings. -/
theorem isPerfPair_middle_of_shortExact
    {S : ShortComplex C} (hS : S.ShortExact) (hL : (S.map L).ShortExact)
    (P : ∀ (F : C) (r : ℕ), r ≤ 2 →
      Ext.{wH} A (L.obj F) r →ₗ[ZMod n] Module.Dual (ZMod n) (Ext.{wE} F N (2 - r)))
    (hP : ∀ {F G : C} (f : F ⟶ G) (r : ℕ) (hr : r ≤ 2)
      (c : Ext.{wH} A (L.obj F) r) (e : Ext.{wE} G N (2 - r)),
      P G r hr (c.comp (Ext.mk₀ (L.map f)) (add_zero r)) e =
        P F r hr c ((Ext.mk₀ f).comp e (zero_add (2 - r))))
    (hP0 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 0) (e : Ext.{wE} S.X₁ N (2 - 1)),
      P S.X₁ 1 (by decide) (c.comp hL.extClass (show 0 + 1 = 1 from rfl)) e =
        P S.X₃ 0 (by decide) c (hS.extClass.comp e (show 1 + (2 - 1) = (2 - 0 : ℕ) from by omega)))
    (hP1 : ∀ (c : Ext.{wH} A (L.obj S.X₃) 1) (e : Ext.{wE} S.X₁ N (2 - 2)),
      P S.X₁ 2 (by decide) (c.comp hL.extClass (show 1 + 1 = 2 from rfl)) e =
        P S.X₃ 1 (by decide) c (hS.extClass.comp e (show 1 + (2 - 2) = (2 - 1 : ℕ) from by omega)))
    (hA : ∀ r hr, (P S.X₁ r hr).IsPerfPair)
    (hQ : ∀ r hr, (P S.X₃ r hr).IsPerfPair)
    (hCA : Subsingleton (Ext.{wH} A (L.obj S.X₁) 3))
    (hEQ : Subsingleton (Ext.{wE} S.X₃ N 3))
    (r : ℕ) (hr : r ≤ 2) : (P S.X₂ r hr).IsPerfPair := by
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr' with rfl | rfl | rfl
  · refine ⟨middle_phi_0 L A N n hn hS hL P hP hP0
      (hA 0 (by decide)).bijective_left (hQ 0 (by decide)).bijective_left
      (hA 1 (by decide)).bijective_left.injective hEQ, ?_⟩
    exact middle_psi_2 L A N n hn hS hL P hP hP0
      (hA 1 (by decide)).bijective_right.surjective
      (hQ 0 (by decide)).bijective_right (hA 0 (by decide)).bijective_right hEQ
  · refine ⟨middle_phi_1 L A N n hn hS hL P hP hP0 hP1
      (hQ 0 (by decide)).bijective_left.surjective (hA 1 (by decide)).bijective_left
      (hQ 1 (by decide)).bijective_left (hA 2 (by decide)).bijective_left.injective, ?_⟩
    exact middle_psi_1 L A N n hn hS hL P hP hP0 hP1
      (hA 2 (by decide)).bijective_right.surjective (hQ 1 (by decide)).bijective_right
      (hA 1 (by decide)).bijective_right (hQ 0 (by decide)).bijective_right.injective
  · refine ⟨middle_phi_2 L A N n hn hS hL P hP hP1
      (hQ 1 (by decide)).bijective_left.surjective (hA 2 (by decide)).bijective_left
      (hQ 2 (by decide)).bijective_left hCA, ?_⟩
    exact middle_psi_0 L A N n hn hS hL P hP hP1
      (hQ 2 (by decide)).bijective_right (hA 2 (by decide)).bijective_right
      (hQ 1 (by decide)).bijective_right.injective hCA

end CategoryTheory.Abelian.Ext
