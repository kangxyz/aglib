/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.LocallyFree

/-! Focused consumer of the zero scheme of a morphism into a finite locally free sheaf of constant
rank (Stacks Project, Tag 0FA8; the invertible case is Tags 02OQ and 02OR): its ideal on affine
opens, its universal property, its pullback, and the family-of-sections form, with axiom
guards. -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

/-- The ideal of the zero scheme on an affine open is the Fitting ideal `Fitt_{d-1}` of the
sections of the cokernel. -/
example {X : Scheme.{u}} {F E : X.Modules} [F.IsQuasicoherent] [IsFiniteLocallyFree X E]
    (σ : F ⟶ E) (d : ℕ) (U : X.affineOpens) :
    (Hom.zeroLocusIdeal σ (d + 1)).ideal U = Module.fittingIdeal Γ(X, U) Γ(cokernel σ, U) d :=
  rfl

/-- The zero scheme is a closed subscheme. -/
example {X : Scheme.{u}} {F E : X.Modules} [F.IsQuasicoherent] [IsFiniteLocallyFree X E]
    (σ : F ⟶ E) (d : ℕ) : IsClosedImmersion (Hom.zeroLocusSchemeι σ d) :=
  inferInstance

/-- **Universal property**: `g` factors through `Z(σ)` if and only if `g^* σ = 0`. -/
example {X T : Scheme.{u}} {F E : X.Modules} [F.IsQuasicoherent] [IsFiniteLocallyFree X E]
    (σ : F ⟶ E) {d : ℕ} (hE : SheafHasRank E d) (g : T ⟶ X) :
    (∃ g' : T ⟶ Hom.zeroLocusScheme σ d, g' ≫ Hom.zeroLocusSchemeι σ d = g) ↔
      (Scheme.Modules.pullback g).map σ = 0 :=
  Hom.exists_lift_zeroLocusSchemeι_iff σ hE g

/-- **Pullback**: `Z(σ)` pulls back to `Z(f^* σ)`. -/
example {X Y : Scheme.{u}} {F E : X.Modules} [F.IsQuasicoherent] [IsFiniteLocallyFree X E]
    (σ : F ⟶ E) {d : ℕ} (hE : SheafHasRank E d) (f : Y ⟶ X) :
    (Hom.zeroLocusIdeal σ d).comap f = Hom.zeroLocusIdeal ((Scheme.Modules.pullback f).map σ) d :=
  Hom.zeroLocusIdeal_comap σ hE f

/-- `Z(σ) = X` exactly when `σ = 0`. -/
example {X : Scheme.{u}} {F E : X.Modules} [F.IsQuasicoherent] [IsFiniteLocallyFree X E]
    (σ : F ⟶ E) {d : ℕ} (hE : SheafHasRank E d) :
    Hom.zeroLocusIdeal σ d = ⊥ ↔ σ = 0 :=
  Hom.zeroLocusIdeal_eq_bot_iff σ hE

/-- For `E = 𝒪_X` the zero scheme is the image-ideal zero scheme of `Modules/ZeroLocus`. -/
example {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]
    (σ : F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    Hom.zeroLocusIdeal σ 1 = Hom.imageIdealData σ :=
  Hom.zeroLocusIdeal_one_eq_imageIdealData σ

/-- The zero scheme of finitely many sections `s i : 𝒪_X ⟶ E`, `i : Fin m`: its morphisms are
those along which every pulled-back section vanishes. -/
example {X T : Scheme.{u}} {E : X.Modules} [IsFiniteLocallyFree X E] {m : ℕ}
    (s : ULift.{u} (Fin m) → ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ E))
    {d : ℕ}
    (hE : SheafHasRank E d) (g : T ⟶ X) :
    (∃ g' : T ⟶ Hom.zeroLocusScheme (freeDesc s) d,
        g' ≫ Hom.zeroLocusSchemeι (freeDesc s) d = g) ↔
      ∀ i, (pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map (s i) = 0 := by
  rw [exists_lift_zeroLocusSchemeι_freeDesc_iff s hE g]
  exact forall_congr' fun i => (Preadditive.IsIso.comp_left_eq_zero _ _).symm

/-- The same universal property with the pulled-back sections as elements of `Γ(T, g^* E)`. -/
example {X T : Scheme.{u}} {E : X.Modules} [IsFiniteLocallyFree X E] {I : Type u}
    (s : I → ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ E)) {d : ℕ}
    (hE : SheafHasRank E d) (g : T ⟶ X) :
    (∃ g' : T ⟶ Hom.zeroLocusScheme (freeDesc s) d,
        g' ≫ Hom.zeroLocusSchemeι (freeDesc s) d = g) ↔
      ∀ i, ((pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map (s i)).val.app
        (Opposite.op ⊤) (1 : Γ(T, ⊤)) = 0 :=
  exists_lift_zeroLocusSchemeι_freeDesc_iff_globalSections s hE g

/-- The zero scheme of sections pulls back to the zero scheme of the pulled-back sections. -/
example {X Y : Scheme.{u}} {E : X.Modules} [IsFiniteLocallyFree X E] {I : Type u}
    (s : I → ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ E)) {d : ℕ}
    (hE : SheafHasRank E d)
    (f : Y ⟶ X) :
    (Hom.zeroLocusIdeal (freeDesc s) d).comap f =
      Hom.zeroLocusIdeal
        (freeDesc fun i => (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (s i)) d :=
  zeroLocusIdeal_freeDesc_comap s hE f

/-- A closed subscheme is determined by the morphisms factoring through it. -/
example {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ (T : Scheme.{u}) (g : T ⟶ X), I.comap g = ⊥ ↔ J.comap g = ⊥) : I = J :=
  Scheme.IdealSheafData.eq_of_forall_comap_eq_bot_iff h

/-- Quotients of sheaves of finite type are of finite type. -/
example {X : Scheme.{u}} {E Q : X.Modules} (p : E ⟶ Q) [Epi p] [Q.IsQuasicoherent]
    [(kernel p).IsQuasicoherent] (hE : QuasiCoherent.affineLocallyFiniteType X E) :
    QuasiCoherent.affineLocallyFiniteType X Q :=
  QuasiCoherent.affineLocallyFiniteType_of_epi p hE

/-- Fitting ideal sheaves grow along epimorphisms. -/
example {X : Scheme.{u}} {E Q : X.Modules} (p : E ⟶ Q) [Epi p] [(kernel p).IsQuasicoherent]
    (hE : QuasiCoherent.affineLocallyFiniteType X E)
    (hQ : QuasiCoherent.affineLocallyFiniteType X Q) (k : ℕ) :
    fittingIdealSheaf E hE k ≤ fittingIdealSheaf Q hQ k :=
  fittingIdealSheaf_le_of_epi p hE hQ k

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.zeroLocusIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.zeroLocusIdeal

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.exists_lift_zeroLocusSchemeι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.exists_lift_zeroLocusSchemeι_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.zeroLocusIdeal_comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.zeroLocusIdeal_comap

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.zeroLocusIdeal_eq_bot_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.zeroLocusIdeal_eq_bot_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.zeroLocusIdeal_one_eq_imageIdealData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.zeroLocusIdeal_one_eq_imageIdealData

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_zeroLocusSchemeι_freeDesc_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_zeroLocusSchemeι_freeDesc_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.zeroLocusIdeal_freeDesc_comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.zeroLocusIdeal_freeDesc_comap

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_zeroLocusSchemeι_freeDesc_iff_globalSections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_zeroLocusSchemeι_freeDesc_iff_globalSections

/--
info: 'AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_of_epi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_of_epi

/--
info: 'AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_eq_top_of_epi_of_sheafHasRank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_eq_top_of_epi_of_sheafHasRank
