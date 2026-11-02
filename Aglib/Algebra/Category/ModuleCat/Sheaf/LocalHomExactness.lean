/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantProjective
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InjectiveSections
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Local boundaries for finite-source Hom on the original section complexes

The boundary sieve records actual linear lifts through the original
cochain differential. Finite projective sources have covering boundary sieves
when the sheaf complex is exact. The syzygy step uses an actual short exact
module presentation and extends its relation correction into the actual
injective section module. No auxiliary cohomology or resolution carrier is
introduced. The degree-one correction uses the original locally bijective constant unit
and injectivity of its original value module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r

namespace ModuleCat.Sheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  {Λ : Type r} [Ring Λ]

attribute [local instance] hasSheafify

/-- Arrows on which the specified original section map is an actual boundary. -/
def boundarySieve (I : CochainComplex (Sheaf J (ModuleCat.{max c h} Λ)) ℕ)
    (M : ModuleCat.{max c h} Λ) (q : ℕ) {U : C}
    (g : M ⟶ (I.X (q + 1)).obj.obj (op U)) : Sieve U where
  arrows V f := ∃ a : M ⟶ (I.X q).obj.obj (op V),
    a ≫ (I.d q (q + 1)).hom.app (op V) = g ≫ (I.X (q + 1)).obj.map f.op
  downward_closed := by
    rintro V W f ⟨a, ha⟩ k
    refine ⟨a ≫ (I.X q).obj.map k.op, ?_⟩
    rw [Category.assoc, (I.d q (q + 1)).hom.naturality, ← Category.assoc, ha,
      Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp]

/-- Every closed source-linear map locally bounds in the original section complex. -/
def LocallyBoundary (I : CochainComplex (Sheaf J (ModuleCat.{max c h} Λ)) ℕ)
    (M : ModuleCat.{max c h} Λ) (q : ℕ) : Prop :=
  ∀ (U : C) (g : M ⟶ (I.X (q + 1)).obj.obj (op U)),
    g ≫ (I.d (q + 1) (q + 2)).hom.app (op U) = 0 → boundarySieve J I M q g ∈ J U

/-- Finite projective sources have covering boundary sieves at an exact degree. -/
theorem locallyBoundary_of_projective
    (I : CochainComplex (Sheaf J (ModuleCat.{max c h} Λ)) ℕ) (q : ℕ)
    (hI : I.ExactAt (q + 1)) (M : ModuleCat.{max c h} Λ)
    [Module.Finite Λ M] [Module.Projective Λ M] : LocallyBoundary J I M q := by
  intro U g hg
  have hp : (ComplexShape.up ℕ).prev (q + 1) = q :=
    (ComplexShape.up ℕ).prev_eq' (by rfl)
  have hn : (ComplexShape.up ℕ).next (q + 1) = q + 2 :=
    (ComplexShape.up ℕ).next_eq' (by rfl)
  obtain ⟨T, hT, h⟩ := exists_cover_projective_boundary_of_exactAt J I (q + 1) hI M g
    (by rw [hn]; exact hg)
  apply J.superset_covering _ hT
  intro V f hf
  change ∃ a : M ⟶ (I.X q).obj.obj (op V),
    a ≫ (I.d q (q + 1)).hom.app (op V) = g ≫ (I.X (q + 1)).obj.map f.op
  rw [hp] at h
  exact h f hf

/-- An actual finite-projective presentation shifts the local-boundary problem to its syzygy. -/
theorem locallyBoundary_of_syzygy
    (I : CochainComplex (Sheaf J (ModuleCat.{max c h} Λ)) ℕ)
    (S : ShortComplex (ModuleCat.{max c h} Λ)) (hS : S.ShortExact) (q : ℕ)
    [Module.Finite Λ S.X₂] [Module.Projective Λ S.X₂]
    [∀ U : C, Injective ((I.X q).obj.obj (op U))]
    (hI : I.ExactAt (q + 2)) (hK : LocallyBoundary J I S.X₁ q) :
    LocallyBoundary J I S.X₃ (q + 1) := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  intro U g hg
  have hp : (S.g ≫ g) ≫ (I.d (q + 2) (q + 3)).hom.app (op U) = 0 := by
    rw [Category.assoc, hg, comp_zero]
  have hP := locallyBoundary_of_projective J I (q + 1) hI S.X₂ U (S.g ≫ g) hp
  apply J.transitive hP (boundarySieve J I S.X₃ (q + 1) g)
  intro V f hf
  obtain ⟨b, hb⟩ := hf
  have hb' : (S.f ≫ b) ≫ (I.d (q + 1) (q + 2)).hom.app (op V) = 0 := by
    rw [Category.assoc, hb, ← Category.assoc, ← Category.assoc, S.zero, zero_comp, zero_comp]
  apply J.superset_covering _ (hK V (S.f ≫ b) hb')
  intro W k hk
  obtain ⟨a, ha⟩ := hk
  let a' := Injective.factorThru a S.f
  have ha' : S.f ≫ a' = a := Injective.comp_factorThru a S.f
  let b' := b ≫ (I.X (q + 1)).obj.map k.op - a' ≫ (I.d q (q + 1)).hom.app (op W)
  have hb₀ : S.f ≫ b' = 0 := by
    dsimp only [b']
    simp only [Preadditive.comp_sub, ← Category.assoc, ha', ha, sub_self]
  refine ⟨hS.exact.desc b' hb₀, ?_⟩
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, ShortComplex.Exact.g_desc]
  have hd : (I.d q (q + 1)).hom.app (op W) ≫
      (I.d (q + 1) (q + 2)).hom.app (op W) = 0 :=
    congrArg (fun t => t.hom.app (op W)) (I.d_comp_d q (q + 1) (q + 2))
  dsimp only [b']
  rw [Preadditive.sub_comp]
  simp only [Category.assoc, hd, comp_zero, sub_zero]
  rw [(I.d (q + 1) (q + 2)).hom.naturality, ← Category.assoc, hb,
    Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp, Category.assoc]

/-- The degree-one relation correction extends into the original constant injective value. -/
theorem locallyBoundary_zero_of_presentation
    (I : CochainComplex (Sheaf J (ModuleCat.{max c h} Λ)) ℕ)
    (N : Sheaf J (ModuleCat.{max c h} Λ)) (Q : ModuleCat.{max c h} Λ) [Injective Q]
    (η : (Functor.const Cᵒᵖ).obj Q ⟶ N.obj)
    [CategoryTheory.Presheaf.IsLocallySurjective J η]
    [CategoryTheory.Presheaf.IsLocallyInjective J η]
    (i : N ⟶ I.X 0) (hi : i ≫ I.d 0 1 = 0) [Mono i]
    (hN : (ShortComplex.mk i (I.d 0 1) hi).Exact)
    (S : ShortComplex (ModuleCat.{max c h} Λ)) (hS : S.ShortExact)
    [Module.Finite Λ S.X₂] [Module.Projective Λ S.X₂]
    [Module.FinitePresentation Λ S.X₁] (hI : I.ExactAt 1) :
    LocallyBoundary J I S.X₃ 0 := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  intro U g hg
  have hp : (S.g ≫ g) ≫ (I.d 1 2).hom.app (op U) = 0 := by
    rw [Category.assoc, hg, comp_zero]
  have hP := locallyBoundary_of_projective J I 0 hI S.X₂ U (S.g ≫ g) hp
  apply J.transitive hP (boundarySieve J I S.X₃ 0 g)
  intro V f hf
  obtain ⟨b, hb⟩ := hf
  have hb' : (S.f ≫ b) ≫ (I.d 0 1).hom.app (op V) = 0 := by
    rw [Category.assoc, hb, ← Category.assoc, ← Category.assoc, S.zero, zero_comp, zero_comp]
  let E := sheafToPresheaf J (ModuleCat.{max c h} Λ) ⋙
    (evaluation Cᵒᵖ (ModuleCat.{max c h} Λ)).obj (op V)
  have hNE := hN.map_of_mono_of_preservesKernel E (inferInstance : Mono i) inferInstance
  let : Mono ((ShortComplex.mk i (I.d 0 1) hi).map E).f := by
    change Mono (E.map i)
    infer_instance
  let h : S.X₁ ⟶ N.obj.obj (op V) := hNE.lift (S.f ≫ b) hb'
  have hh : h ≫ i.hom.app (op V) = S.f ≫ b := hNE.lift_f (S.f ≫ b) hb'
  let H := Functor.whiskerRight η (coyoneda.obj (op S.X₁))
  let : CategoryTheory.Presheaf.IsLocallySurjective J H :=
    ModuleCat.Presheaf.locallySurjective_coyoneda_of_finitePresentation J η S.X₁
  apply J.superset_covering _ (CategoryTheory.Presheaf.imageSieve_mem J H h)
  intro W k hk
  obtain ⟨a, ha⟩ := hk
  change a ≫ η.app (op W) = h ≫ N.obj.map k.op at ha
  let : Injective (((Functor.const Cᵒᵖ).obj Q).obj (op W)) :=
    inferInstanceAs (Injective Q)
  let a' := Injective.factorThru a S.f
  have ha' : S.f ≫ a' = a := Injective.comp_factorThru a S.f
  let b' := b ≫ (I.X 0).obj.map k.op - a' ≫ η.app (op W) ≫ i.hom.app (op W)
  have hc : S.f ≫ (a' ≫ η.app (op W) ≫ i.hom.app (op W)) =
      (S.f ≫ b) ≫ (I.X 0).obj.map k.op := by
    rw [← Category.assoc S.f a', ha', ← Category.assoc, ha, Category.assoc,
      i.hom.naturality, ← Category.assoc, hh]
  have hb₀ : S.f ≫ b' = 0 := by
    dsimp only [b']
    rw [Preadditive.comp_sub, hc, ← Category.assoc, sub_self]
  refine ⟨hS.exact.desc b' hb₀, ?_⟩
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, ShortComplex.Exact.g_desc]
  have hd : i.hom.app (op W) ≫ (I.d 0 1).hom.app (op W) = 0 :=
    congrArg (fun t : N ⟶ I.X 1 => t.hom.app (op W)) hi
  dsimp only [b']
  rw [Preadditive.sub_comp]
  simp only [Category.assoc, hd, comp_zero, sub_zero]
  rw [(I.d 0 1).hom.naturality, ← Category.assoc, hb,
    Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp, Category.assoc]

end ModuleCat.Sheaf

namespace ModuleCat.Sheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  {Λ : Type r} [CommRing Λ] [IsNoetherianRing Λ] [Small.{max c h} Λ]

attribute [local instance] hasSheafify

/-- Finite sources have local boundaries in an exact injective-section complex
augmented by the original locally constant injective coefficient. -/
theorem locallyBoundary_finite_of_constantInjective
    (I : CochainComplex (Sheaf J (ModuleCat.{max c h} Λ)) ℕ)
    (N : Sheaf J (ModuleCat.{max c h} Λ)) (Q : ModuleCat.{max c h} Λ) [Injective Q]
    (η : (Functor.const Cᵒᵖ).obj Q ⟶ N.obj)
    [CategoryTheory.Presheaf.IsLocallySurjective J η]
    [CategoryTheory.Presheaf.IsLocallyInjective J η]
    (i : N ⟶ I.X 0) (hi : i ≫ I.d 0 1 = 0) [Mono i]
    (hN : (ShortComplex.mk i (I.d 0 1) hi).Exact)
    (hI : ∀ q : ℕ, I.ExactAt (q + 1))
    [∀ (q : ℕ) (U : C), Injective ((I.X q).obj.obj (op U))]
    (M : ModuleCat.{max c h} Λ) [Module.Finite Λ M] (q : ℕ) :
    LocallyBoundary J I M q := by
  induction q generalizing M with
  | zero =>
    obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation Λ M
    let S := p.shortComplexKer
    let : Module.FinitePresentation Λ S.X₁ :=
      Module.finitePresentation_of_finite Λ (LinearMap.ker p)
    exact locallyBoundary_zero_of_presentation J I N Q η i hi hN S
      (LinearMap.shortExact_shortComplexKer hp) (hI 0)
  | succ q ih =>
    obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation Λ M
    let S := p.shortComplexKer
    have hK : LocallyBoundary J I S.X₁ q := ih S.X₁
    exact locallyBoundary_of_syzygy J I S (LinearMap.shortExact_shortComplexKer hp) q
      (hI (q + 1)) hK

end ModuleCat.Sheaf
