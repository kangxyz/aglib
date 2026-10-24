/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteExtension
public import Aglib.AlgebraicGeometry.Cohomology.Proper.BirationalFirstCohomology
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Data.Nat.Find

/-!
# A maximal original first-cohomology model

A uniform natural length bound on all original normal proper birational
models has an attained maximum. The identity of the original normal base
supplies a member of the family. Every further normal proper birational
model induces a bijection on the original structural H1 map, by the passed
injection and equality of finite lengths with the original scalar actions.

This result does not assert vanishing of a higher direct-image sheaf or
extension of a local modification to a global model.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The actual original structural A-length, with its original scalar action. -/
def originalStructureH1Length {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) : ℕ∞ :=
  letI := moduleCohomologyModuleOfHom X
    (FiniteTraceCoordinates.structureScalar f) (FiniteTraceCoordinates.structureModule X) 1
  Module.length A
    (Sheaf.H.{u + 1} (moduleAddSheaf X (FiniteTraceCoordinates.structureModule X)) 1)

private theorem exists_attained_nat_max (P : ℕ∞ → Prop)
    (hne : ∃ l, P l) (N : ℕ) (hN : ∀ l, P l → l ≤ (N : ℕ∞)) :
    ∃ n : ℕ, P (n : ℕ∞) ∧ ∀ l, P l → l ≤ (n : ℕ∞) := by
  classical
  let Q : ℕ → Prop := fun n ↦ P (n : ℕ∞)
  obtain ⟨l, hl⟩ := hne
  have hlN : l ≤ (N : ℕ∞) := hN l hl
  have hlf : l ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top N) hlN
  have hlQ : Q l.toNat := by
    change P (l.toNat : ℕ∞)
    rw [ENat.natCast_toNat hlf]
    exact hl
  let n := Nat.findGreatest Q N
  have hn : Q n := Nat.findGreatest_spec (ENat.toNat_le_of_le_natCast hlN) hlQ
  refine ⟨n, hn, ?_⟩
  intro k hk
  have hkN : k ≤ (N : ℕ∞) := hN k hk
  have hkf : k ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top N) hkN
  have hkQ : Q k.toNat := by
    change P (k.toNat : ℕ∞)
    rw [ENat.natCast_toNat hkf]
    exact hk
  have hkn : k.toNat ≤ n := Nat.le_findGreatest
    (ENat.toNat_le_of_le_natCast hkN) hkQ
  rw [← ENat.natCast_toNat hkf]
  exact ENat.natCast_le_natCast.mpr hkn

private theorem bijective_of_injective_of_length_le
    {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (v : M →ₗ[R] N)
    (hinj : Function.Injective v) (hfinite : Module.length R N ≠ ⊤)
    (hle : Module.length R N ≤ Module.length R M) : Function.Bijective v := by
  have hlen : Module.length R M = Module.length R N :=
    le_antisymm (Module.length_le_of_injective v hinj) hle
  have hfl : IsFiniteLength R N := Module.length_ne_top_iff.mp hfinite
  have hna := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  let : _root_.IsNoetherian R N := hna.1
  let : _root_.IsArtinian R N := hna.2
  refine ⟨hinj, ?_⟩
  apply LinearMap.range_eq_top.mp
  by_contra hproper
  have hstrict : Module.length R (LinearMap.range v) < Module.length R N :=
    Submodule.length_lt hproper
  have heq : Module.length R (LinearMap.range v) = Module.length R N :=
    (LinearEquiv.ofInjective v hinj).length_eq.symm.trans hlen
  exact (ne_of_lt hstrict) heq

/-- A genuine original normal model makes the family nonempty. Its bounded
original structural lengths have an attained natural maximum. -/
theorem exists_maximal_normalModification_of_model
    (A : Type u) [CommRing A] [IsDomain A]
    (hbound : NormalModificationH1Bounded A)
    {X₀ : Scheme.{u}} [IsIntegral X₀]
    (f₀ : X₀ ⟶ Spec (.of A)) [IsProper f₀] [IsDominant f₀]
    (h₀N : NormalStalks X₀)
    (h₀ff : IsIso (CommRingCat.ofHom (functionFieldMap f₀))) :
    ∃ (n : ℕ) (X : Scheme.{u}) (hX : IsIntegral X),
      letI := hX
      ∃ (f : X ⟶ Spec (.of A)) (hf : IsProper f) (hd : IsDominant f),
        letI := hf
        letI := hd
        NormalStalks X ∧ IsIso (CommRingCat.ofHom (functionFieldMap f)) ∧
          originalStructureH1Length f = (n : ℕ∞) ∧
          ∀ (Y : Scheme.{u}) [IsIntegral Y]
            (b : Y ⟶ Spec (.of A)) [IsProper b] [IsDominant b],
            NormalStalks Y → IsIso (CommRingCat.ofHom (functionFieldMap b)) →
              originalStructureH1Length b ≤ (n : ℕ∞) := by
  obtain ⟨N, hN⟩ := hbound
  let P : ℕ∞ → Prop := fun l ↦
    ∃ (X : Scheme.{u}) (hX : IsIntegral X),
      letI := hX
      ∃ (f : X ⟶ Spec (.of A)) (hf : IsProper f) (hd : IsDominant f),
        letI := hf
        letI := hd
        NormalStalks X ∧ IsIso (CommRingCat.ofHom (functionFieldMap f)) ∧
          originalStructureH1Length f = l
  have hne : ∃ l, P l :=
    ⟨originalStructureH1Length f₀, X₀, inferInstance, f₀, inferInstance, inferInstance,
      h₀N, h₀ff, rfl⟩
  have hPN : ∀ l, P l → l ≤ (N : ℕ∞) := by
    intro l hl
    obtain ⟨X, hX, rest⟩ := hl
    let : IsIntegral X := hX
    obtain ⟨f, hf, hd, rest⟩ := rest
    let : IsProper f := hf
    let : IsDominant f := hd
    obtain ⟨hXN, hff, hlen⟩ := rest
    have hb := hN X f hXN hff
    change originalStructureH1Length f ≤ (N : ℕ∞) at hb
    exact hlen ▸ hb
  obtain ⟨n, hn, hmax⟩ := exists_attained_nat_max P hne N hPN
  obtain ⟨X, hX, rest⟩ := hn
  let : IsIntegral X := hX
  obtain ⟨f, hf, hd, rest⟩ := rest
  let : IsProper f := hf
  let : IsDominant f := hd
  obtain ⟨hXN, hff, hlen⟩ := rest
  refine ⟨n, X, hX, f, hf, hd, hXN, hff, hlen, ?_⟩
  intro Y hY b hb hdB hYN hbff
  exact hmax (originalStructureH1Length b)
    ⟨Y, hY, b, hb, hdB, hYN, hbff, rfl⟩

private theorem original_structureScalar_comp
    {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of A)) :
    FiniteTraceCoordinates.structureScalar (g ≫ f) =
      g.appTop.hom.comp (FiniteTraceCoordinates.structureScalar f) := by
  simp only [FiniteTraceCoordinates.structureScalar, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_assoc]

private theorem originalStructureH1Length_comp
    {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of A)) :
    letI := moduleCohomologyModuleOfHom Y
      (g.appTop.hom.comp (FiniteTraceCoordinates.structureScalar f))
      (FiniteTraceCoordinates.structureModule Y) 1
    Module.length A
        (Sheaf.H.{u + 1} (moduleAddSheaf Y (FiniteTraceCoordinates.structureModule Y)) 1) =
      originalStructureH1Length (g ≫ f) := by
  dsimp only [originalStructureH1Length]
  rw [original_structureScalar_comp]

/-- On an attained maximum, every original normal proper birational morphism
induces a bijection on its original structural H1 map. The target action is
identified with the original composite to Spec A by its actual scalar equation. -/
theorem original_structureH1_bijective_of_maximal
    (A : Type u) [CommRing A] [IsDomain A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hXN : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (n : ℕ) (hlen : originalStructureH1Length f = (n : ℕ∞))
    (hmax : ∀ (Z : Scheme.{u}) [IsIntegral Z]
      (b : Z ⟶ Spec (.of A)) [IsProper b] [IsDominant b],
      NormalStalks Z → IsIso (CommRingCat.ofHom (functionFieldMap b)) →
        originalStructureH1Length b ≤ (n : ℕ∞))
    {Y : Scheme.{u}} [IsIntegral Y]
    (g : Y ⟶ X) [IsProper g] [IsDominant g]
    (hYN : NormalStalks Y)
    (hgf : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    Function.Bijective (moduleCohomologyMapAlongLinear g
      (FiniteTraceCoordinates.structureScalar f)
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1) := by
  let := moduleCohomologyModuleOfHom X
    (FiniteTraceCoordinates.structureScalar f) (FiniteTraceCoordinates.structureModule X) 1
  let := moduleCohomologyModuleOfHom Y
    (g.appTop.hom.comp (FiniteTraceCoordinates.structureScalar f))
    (FiniteTraceCoordinates.structureModule Y) 1
  let v := moduleCohomologyMapAlongLinear g (FiniteTraceCoordinates.structureScalar f)
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1
  have hinj : Function.Injective v :=
    moduleCohomologyMapAlongLinear_unit_injective_of_isProper_birational
      X (FiniteTraceCoordinates.structureScalar f) g hXN hgf
  have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap (g ≫ f))) := by
    let := hff
    let := hgf
    rw [functionFieldMap_comp]
    change IsIso (CommRingCat.ofHom (functionFieldMap f) ≫
      CommRingCat.ofHom (functionFieldMap g))
    infer_instance
  have hb := hmax Y (g ≫ f) hYN hcomp
  have hYlen :
      Module.length A
        (Sheaf.H.{u + 1} (moduleAddSheaf Y (FiniteTraceCoordinates.structureModule Y)) 1) ≤
        (n : ℕ∞) :=
    (originalStructureH1Length_comp g f).le.trans hb
  have hfinite :
      Module.length A
        (Sheaf.H.{u + 1} (moduleAddSheaf Y (FiniteTraceCoordinates.structureModule Y)) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top n) hYlen
  have hle :
      Module.length A
        (Sheaf.H.{u + 1} (moduleAddSheaf Y (FiniteTraceCoordinates.structureModule Y)) 1) ≤
      Module.length A
        (Sheaf.H.{u + 1} (moduleAddSheaf X (FiniteTraceCoordinates.structureModule X)) 1) :=
    hYlen.trans_eq hlen.symm
  exact bijective_of_injective_of_length_le v hinj hfinite hle

private theorem original_normalStalks_spec
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] :
    NormalStalks (Spec (.of A)) := by
  intro p
  exact (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec A p).symm

private theorem original_identity_functionFieldMap_isIso
    (S : Scheme.{u}) [IsIntegral S] :
    IsIso (CommRingCat.ofHom (functionFieldMap (𝟙 S))) := by
  let φ : S.functionField →+* S.functionField := functionFieldMap (𝟙 S)
  have heq : φ = φ.comp φ := by
    simpa only [Category.id_comp] using functionFieldMap_comp (𝟙 S) (𝟙 S)
  have hfix (x : S.functionField) : φ x = x := by
    apply φ.injective
    exact (RingHom.congr_fun heq x).symm
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective φ
  exact ⟨φ.injective, fun x ↦ ⟨x, hfix x⟩⟩

/-- The original normal base supplies its identity model. A uniform bound
therefore yields an actual maximizing normal model and bijectivity of every
original structural H1 map from it to a normal proper birational model. -/
theorem exists_maximal_normalModification
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hbound : NormalModificationH1Bounded A) :
    ∃ (n : ℕ) (X : Scheme.{u}) (hX : IsIntegral X),
      letI := hX
      ∃ (f : X ⟶ Spec (.of A)) (hf : IsProper f) (hd : IsDominant f),
        letI := hf
        letI := hd
        NormalStalks X ∧ IsIso (CommRingCat.ofHom (functionFieldMap f)) ∧
          originalStructureH1Length f = (n : ℕ∞) ∧
          (∀ (Z : Scheme.{u}) [IsIntegral Z]
            (b : Z ⟶ Spec (.of A)) [IsProper b] [IsDominant b],
            NormalStalks Z → IsIso (CommRingCat.ofHom (functionFieldMap b)) →
              originalStructureH1Length b ≤ (n : ℕ∞)) ∧
          ∀ (Y : Scheme.{u}) [IsIntegral Y]
            (g : Y ⟶ X) [IsProper g] [IsDominant g],
            NormalStalks Y → IsIso (CommRingCat.ofHom (functionFieldMap g)) →
              Function.Bijective (moduleCohomologyMapAlongLinear g
                (FiniteTraceCoordinates.structureScalar f)
                (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1) := by
  obtain ⟨n, X, hX, rest⟩ := exists_maximal_normalModification_of_model A hbound
    (𝟙 (Spec (.of A))) (original_normalStalks_spec A)
    (original_identity_functionFieldMap_isIso (Spec (.of A)))
  let : IsIntegral X := hX
  obtain ⟨f, hf, hd, rest⟩ := rest
  let : IsProper f := hf
  let : IsDominant f := hd
  obtain ⟨hXN, hff, hlen, hmax⟩ := rest
  refine ⟨n, X, hX, f, hf, hd, hXN, hff, hlen, hmax, ?_⟩
  intro Y hY g hg hdg hYN hgf
  exact original_structureH1_bijective_of_maximal A f hXN hff n hlen hmax g hYN hgf

end AlgebraicGeometry.Scheme.Cohomology
