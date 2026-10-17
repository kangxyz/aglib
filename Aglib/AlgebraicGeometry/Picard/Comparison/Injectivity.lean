/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Fppf
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Pushforward

/-!
# Injectivity of the fppf comparison map and fppf-locally trivial classes

Kleiman's comparison theorem (*The Picard scheme*, arXiv:math/0504020v1, Thm 2.5(1), p. 18)
asserts that `toFppfPicardSheaf p : P_{X/S} ⟶ Pic_{X/S,(fppf)}` is injective on every
`S`-scheme `T` when `O_T ⟶ (X ×_S T ⟶ T)_* O` is an isomorphism for every `T`, which holds
for `S` locally Noetherian and `p` proper, flat, with geometrically integral fibres
(`isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`). This file reduces
that statement to a property of line bundles and proves the reduction is an equivalence; the
property itself is not proved here.

`FppfLocallyTrivialMemBaseImage p` says: every class `a ∈ Pic(X ×_S T)` that vanishes on an
fppf covering sieve of `T` in `Over S` lies in the image of `Pic(T)`. This is the content of
the "alternatively" form of Kleiman's proof of Part 1 (p. 19), which uses that
`Pic_{X/S,(fppf)}` is also the sheafification of `T ↦ Pic(X ×_S T)` (`fppfFamilyPicardSheafIso`).

* `toFppfPicardSheaf_isLocallyInjective`: the sheafification unit is locally injective
  (Mathlib's `Presheaf.isLocallyInjective_toSheafify'`).
* `equalizerSieve_mem_of_toFppfPicardSheaf_app_eq_zero` and
  `exists_sieve_of_toFppfPicardSheaf_app_eq_zero`: if `[a] ∈ P_{X/S}(T)` maps to zero in the
  sheafification, then `a` vanishes in `Pic(X ×_S U)` for every `U ⟶ T` in an fppf covering
  sieve, because `quotientProjection p ≫ toFppfPicardSheaf p` is locally injective.
* `fppfLocallyTrivialMemBaseImage_iff_injective`: the property holds if and only if
  `toFppfPicardSheaf p` is injective on every `T`; `mono_toFppfPicardSheaf_of_…` records the
  monomorphism form.

The module form of universal O-connectedness, the input "`f_{T'*} p_X^* L ≃ O_{T'}`" of that
argument for trivial `p_X^* L`, is `Scheme.Modules.isIso_unit_app_unit_of_isIso_c`: if the
structure map `q.c` of `q : Y ⟶ T` is an isomorphism, so is the adjunction unit
`O_T ⟶ q_* q^* O_T`; under the hypotheses of target 2 this holds for every base change
(`isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`).

Not proved here: `FppfLocallyTrivialMemBaseImage p` under universal O-connectedness. Kleiman's
argument shows that `f_{T*} L` is invertible and `f_T^* f_{T*} L ⟶ L` is an isomorphism after
fppf base change, using flat base change of `f_{T*}` and descent along faithfully flat maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- Every class on `X ×_S T` that vanishes fppf-locally on `T` is pulled back from `T`: if the
sieve of morphisms `T' ⟶ T` along which `a` becomes zero in `Pic(X ×_S T')` is an fppf
covering sieve, then `a` lies in the image of `Pic(T) ⟶ Pic(X ×_S T)`. -/
def FppfLocallyTrivialMemBaseImage : Prop :=
  ∀ (T : (Over S)ᵒᵖ) (a : (familyPicardFunctor p).obj T),
    Presheaf.equalizerSieve (F := familyPicardFunctor p) a 0 ∈
      (Scheme.fppfTopology.over S) T.unop → a ∈ baseImage p T

/-- The sheafification unit `P_{X/S} ⟶ Pic_{X/S,(fppf)}` is locally injective. -/
instance toFppfPicardSheaf_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (toFppfPicardSheaf p) :=
  Presheaf.isLocallyInjective_toSheafify' (J := Scheme.fppfTopology.over S)
    (relativePicardFunctor p)

/-- **Kleiman, Thm 2.5(1), conditional form.** If fppf-locally trivial classes are base
classes, then `P_{X/S}(T) ⟶ Pic_{X/S,(fppf)}(T)` is injective for every `T`. -/
theorem toFppfPicardSheaf_app_injective_of_fppfLocallyTrivialMemBaseImage
    (h : FppfLocallyTrivialMemBaseImage p) (T : (Over S)ᵒᵖ) :
    Function.Injective ((toFppfPicardSheaf p).app T).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with | H a =>
  have h1 : (quotientProjection p ≫ toFppfPicardSheaf p).app T a =
      (quotientProjection p ≫ toFppfPicardSheaf p).app T 0 := by
    rw [map_zero]
    exact hx
  have hmem := Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
    (quotientProjection p ≫ toFppfPicardSheaf p) a 0 h1
  exact (QuotientAddGroup.eq_zero_iff a).mpr (h T a hmem)

/-- The monomorphism form of `toFppfPicardSheaf_app_injective_of_fppfLocallyTrivialMemBaseImage`. -/
theorem mono_toFppfPicardSheaf_of_fppfLocallyTrivialMemBaseImage
    (h : FppfLocallyTrivialMemBaseImage p) : Mono (toFppfPicardSheaf p) := by
  have : ∀ T, Mono ((toFppfPicardSheaf p).app T) := fun T =>
    ConcreteCategory.mono_of_injective _
      (toFppfPicardSheaf_app_injective_of_fppfLocallyTrivialMemBaseImage p h T)
  exact NatTrans.mono_of_mono_app _

/-- A class whose image in `Pic_{X/S,(fppf)}(T)` is zero vanishes in `Pic(X ×_S T')` for all
`T' ⟶ T` in an fppf covering sieve. -/
theorem equalizerSieve_mem_of_toFppfPicardSheaf_app_eq_zero {T : (Over S)ᵒᵖ}
    (a : (familyPicardFunctor p).obj T)
    (ha : (toFppfPicardSheaf p).app T (QuotientAddGroup.mk a) = 0) :
    Presheaf.equalizerSieve (F := familyPicardFunctor p) a 0 ∈
      (Scheme.fppfTopology.over S) T.unop := by
  refine Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
    (quotientProjection p ≫ toFppfPicardSheaf p) a 0 ?_
  rw [map_zero]
  exact ha

/-- The same vanishing on an fppf covering sieve of the underlying scheme `T.left`. -/
theorem exists_sieve_of_toFppfPicardSheaf_app_eq_zero {T : (Over S)ᵒᵖ}
    (a : (familyPicardFunctor p).obj T)
    (ha : (toFppfPicardSheaf p).app T (QuotientAddGroup.mk a) = 0) :
    ∃ R : Sieve T.unop.left, R ∈ Scheme.fppfTopology T.unop.left ∧
      ∀ ⦃U : Scheme.{u}⦄ (g : U ⟶ T.unop.left), R g →
        Scheme.Modules.Invertible.pullbackClass ((familyScheme p).map
          (Over.homMk g : Over.mk (g ≫ T.unop.hom) ⟶ T.unop)) a = 0 := by
  have hmem := equalizerSieve_mem_of_toFppfPicardSheaf_app_eq_zero p a ha
  rw [GrothendieckTopology.mem_over_iff] at hmem
  refine ⟨_, hmem, fun U g hg => ?_⟩
  rw [Sieve.overEquiv_iff] at hg
  exact hg.trans (map_zero _)

/-- Conversely, injectivity of the comparison map gives the descent property: a class that
vanishes fppf-locally has zero image in the fppf sheaf, because sections of a sheaf that
vanish locally are zero. -/
theorem fppfLocallyTrivialMemBaseImage_of_injective
    (h : ∀ T, Function.Injective ((toFppfPicardSheaf p).app T).hom) :
    FppfLocallyTrivialMemBaseImage p := by
  intro T a ha
  have hsheaf : Presieve.IsSheaf (Scheme.fppfTopology.over S)
      ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (Scheme.fppfTopology.over S)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj (fppfPicardSheaf p)).property
  have key : (quotientProjection p ≫ toFppfPicardSheaf p).app T a =
      (quotientProjection p ≫ toFppfPicardSheaf p).app T 0 := by
    refine (hsheaf.isSeparated _ ha).ext (fun Y f hf => ?_)
    have hf' : (familyPicardFunctor p).map f.op a = (familyPicardFunctor p).map f.op 0 := hf
    have e1 := NatTrans.naturality_apply (quotientProjection p ≫ toFppfPicardSheaf p) f.op a
    have e2 := NatTrans.naturality_apply (quotientProjection p ≫ toFppfPicardSheaf p) f.op 0
    rw [hf'] at e1
    exact e1.symm.trans e2
  rw [map_zero] at key
  exact (QuotientAddGroup.eq_zero_iff a).mp (h T (key.trans (map_zero _).symm))

/-- The descent property is equivalent to injectivity of the comparison map on every `T`. -/
theorem fppfLocallyTrivialMemBaseImage_iff_injective :
    FppfLocallyTrivialMemBaseImage p ↔
      ∀ T, Function.Injective ((toFppfPicardSheaf p).app T).hom :=
  ⟨toFppfPicardSheaf_app_injective_of_fppfLocallyTrivialMemBaseImage p,
    fppfLocallyTrivialMemBaseImage_of_injective p⟩

end AlgebraicGeometry.Scheme.RelativePicard

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {Y T : Scheme.{u}} (q : Y ⟶ T)

-- `T.Modules` and `SheafOfModules T.ringCatSheaf` are the same category under different
-- instance paths; relaxing instance transparency lets the sectionwise criterion apply.
set_option backward.isDefEq.respectTransparency false in
/-- If the structure map `q.c : O_T ⟶ q_* O_Y` is an isomorphism, so is the corresponding map of
module sheaves `O_T ⟶ q_* O_Y`. -/
theorem isIso_unitToPushforwardObjUnit_of_isIso_c [IsIso q.c] :
    IsIso (C := T.Modules) (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom) := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ConcreteCategory.bijective_of_isIso (q.c.app (op U))

-- `T.Modules` and `SheafOfModules T.ringCatSheaf` are the same category under different
-- instance paths; relaxing instance transparency lets `pullbackUnitIso_homEquiv` apply.
set_option backward.isDefEq.respectTransparency false in
/-- **Module form of O-connectedness.** If `q.c` is an isomorphism, the unit
`O_T ⟶ q_* q^* O_T` of the pullback–pushforward adjunction is an isomorphism: composed with
`q_*` of `pullbackUnitIso q`, it is `unitToPushforwardObjUnit`. -/
theorem isIso_unit_app_unit_of_isIso_c [IsIso q.c] :
    IsIso ((pullbackPushforwardAdjunction q).unit.app (SheafOfModules.unit T.ringCatSheaf)) := by
  have h := pullbackUnitIso_homEquiv q
  rw [Adjunction.homEquiv_unit] at h
  have : IsIso ((pullbackPushforwardAdjunction q).unit.app (SheafOfModules.unit T.ringCatSheaf) ≫
      (pushforward q).map (pullbackUnitIso q).hom) := by
    rw [h]
    exact isIso_unitToPushforwardObjUnit_of_isIso_c q
  exact IsIso.of_isIso_comp_right _ ((pushforward q).map (pullbackUnitIso q).hom)

/-- **Module form of universal O-connectedness.** For `S` locally Noetherian and `p` proper,
flat, with geometrically integral fibres, the unit `O_T ⟶ q_* q^* O_T` is an isomorphism for
`q = pullback.snd p g` and every `g : T ⟶ S`. -/
theorem isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral
    {S X : Scheme.{u}} (p : X ⟶ S) [IsLocallyNoetherian S] [IsProper p] [Flat p]
    [GeometricallyIntegral p] (g : T ⟶ S) :
    IsIso ((pullbackPushforwardAdjunction (pullback.snd p g)).unit.app
      (SheafOfModules.unit T.ringCatSheaf)) :=
  have := isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral p g
  isIso_unit_app_unit_of_isIso_c (pullback.snd p g)

end AlgebraicGeometry.Scheme.Modules
