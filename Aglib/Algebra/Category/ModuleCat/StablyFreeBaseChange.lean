/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Stable freeness after flat base change

A finite module of finite projective dimension over a Noetherian local ring
becomes stably free whenever its flat base change is projective. Induction
splits the scalar extension of a finite free presentation and transports
actual product equivalences. No Grothendieck group is used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat

/-- A projective flat base change of a finite module with bounded projective
dimension over a Noetherian local ring has an actual finite free complement
whose product with that base change is free. -/
theorem exists_free_prod_of_projective_extendScalars
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R]
    (f : R →+* S) (hf : f.Flat)
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ)
    [HasProjectiveDimensionLE M n]
    [Module.Projective S ((extendScalars f).obj M)] :
    ∃ P : ModuleCat.{u} S, Module.Free S P ∧ Module.Finite S P ∧
      Module.Free S (((extendScalars f).obj M) × P) := by
  let := f.toAlgebra
  let F := extendScalars f
  have : PreservesFiniteLimits F := preservesFiniteLimits_extendScalars_of_flat hf
  induction n generalizing M with
  | zero =>
    have : Projective M :=
      (projective_iff_hasProjectiveDimensionLE_zero M).mpr inferInstance
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    have : Module.Free S (F.obj M) :=
      inferInstanceAs (Module.Free S (S ⊗[R] M))
    have : Module.Finite S (F.obj M) := finite_extendScalars f M
    exact ⟨F.obj M, inferInstance, inferInstance, inferInstance⟩
  | succ n ih =>
    obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R M
    let T := p.shortComplexKer
    have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hp
    have : Module.Finite R T.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker p))
    have : HasProjectiveDimensionLE T.X₁ n :=
      (hT.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    have : Module.Free S (F.obj T.X₂) :=
      inferInstanceAs (Module.Free S (S ⊗[R] P))
    have : Module.Finite S (F.obj T.X₂) := finite_extendScalars f T.X₂
    have : Module.Finite S (F.obj T.X₁) := finite_extendScalars f T.X₁
    have hTF : (T.map F).ShortExact := hT.map_of_exact F
    have : Projective (T.map F).X₃ := by
      change Projective (F.obj M)
      infer_instance
    have : Module.Projective S (T.map F).X₂ := by
      change Module.Projective S (F.obj T.X₂)
      infer_instance
    let s := hTF.splittingOfProjective
    have : Module.Projective S (F.obj T.X₁) :=
      Module.Projective.of_split (T.map F).f.hom s.r.hom
        (congrArg ModuleCat.Hom.hom s.f_r)
    obtain ⟨Q, hQfree, hQfinite, hKQfree⟩ := ih T.X₁
    let := hQfree
    let := hQfinite
    let := hKQfree
    let e : F.obj T.X₂ ≃ₗ[S] (F.obj T.X₁ × F.obj M) :=
      (s.isoBinaryBiproduct ≪≫ biprodIsoProd _ _).toLinearEquiv
    let e' : (F.obj T.X₂ × Q) ≃ₗ[S] (F.obj M × (F.obj T.X₁ × Q)) :=
      (e.prodCongr (LinearEquiv.refl S Q)) ≪≫ₗ
        ((LinearEquiv.prodComm S (F.obj T.X₁) (F.obj M)).prodCongr
          (LinearEquiv.refl S Q)) ≪≫ₗ
        LinearEquiv.prodAssoc S (F.obj M) (F.obj T.X₁) Q
    exact ⟨ModuleCat.of S (F.obj T.X₁ × Q), inferInstance, inferInstance,
      Module.Free.of_equiv e'⟩

end ModuleCat
