/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageRadicialGeneric
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageNoetherianInduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageSourceReduction
public import Aglib.AlgebraicGeometry.Properties.IrreducibleComponents.IntegralOpen

/-! # Genuine finite radicial image constructibility over Noetherian schemes

Actual generic chart descent supplies the open piece in closed-support
induction. A reduced source over an integral target is integral because the
finite surjective radicial map is a closed bijection. No integral hypothesis
is imposed on the original target and no coefficient Noetherianity is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- A nonempty reduced Noetherian scheme contains a nonempty integral affine open. -/
theorem finiteImage_exists_integral_affine_open (X : Scheme.{u})
    [IsNoetherian X] [IsReduced X] [Nonempty X] :
    ∃ V : X.Opens, IsAffineOpen V ∧ Nonempty V.toScheme ∧ IsIntegral V.toScheme :=
  Scheme.exists_integral_affine_open_of_noetherian_reduced X


variable (R : Type r) [CommRing R]

/-- The original direct image along a finite surjective radicial morphism over
a Noetherian target preserves genuine constructible modules. -/
theorem isConstructible_finiteRadicialDirectImage_of_noetherian
    {Y X : Scheme.{u}} [IsNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Surjective f] [UniversallyInjective f]
    {F : ModuleSheaf R Y} (hF : IsConstructible F) :
    IsConstructible ((moduleDirectImage R f).obj F) := by
  classical
  let G := (moduleDirectImage R f).obj F
  apply isConstructible_of_noetherian_reducedClosed_open R G
  intro Z j hj hred hZ
  let : IsClosedImmersion j := hj
  let : IsReduced Z := hred
  let : Nonempty Z := hZ
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian j
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace j
  let : IsNoetherian Z := ⟨⟩
  obtain ⟨V, hVa, hV, hVi⟩ := finiteImage_exists_integral_affine_open Z
  let : IsAffine V.toScheme := hVa
  let : Nonempty V.toScheme := hV
  let : IsIntegral V.toScheme := hVi
  let : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian V.ι
  let : IsNoetherian V.toScheme := ⟨⟩
  let P := pullback f (V.ι ≫ j)
  let fV : P ⟶ V := pullback.snd f (V.ι ≫ j)
  let p : P ⟶ Y := pullback.fst f (V.ι ≫ j)
  let FP := (moduleInverseImage R p).obj F
  let : MorphismProperty.IsStableUnderBaseChange (@UniversallyInjective.{u}) :=
    UniversallyInjective.isStableUnderBaseChange
  let : UniversallyInjective fV :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @UniversallyInjective.{u}) (IsPullback.of_hasPullback f (V.ι ≫ j))
      ‹UniversallyInjective f›
  let I := IdealSheafData.vanishingIdeal (⊤ : Closeds P)
  have hIrad : I.radical = I := by
    apply Scheme.IdealSheafData.ext
    funext A
    simp only [IdealSheafData.radical_ideal]
    exact Ideal.radical_eq_iff.mpr (PrimeSpectrum.isRadical_vanishingIdeal _)
  let : IsReduced I.subscheme := IdealSheafData.subscheme_reduced_of_radical I hIrad
  let : Surjective I.subschemeι := ⟨by
    intro x
    have hx : x ∈ Set.range I.subschemeι := by
      rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
      trivial
    exact hx⟩
  let r := I.subschemeι ≫ fV
  let : UniversallyInjective r :=
    MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance inferInstance
  let : IsAffine I.subscheme := isAffine_of_isAffineHom r
  let ehome := (Equiv.ofBijective r ⟨r.injective, r.surjective⟩).toHomeomorphOfContinuousClosed
    r.continuous r.isClosedMap
  let : IrreducibleSpace I.subscheme := ehome.irreducibleSpace_iff.mpr inferInstance
  let : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let FR := (moduleInverseImage R I.subschemeι).obj FP
  have hFR : IsConstructible FR :=
    isConstructible_pullback I.subschemeι (isConstructible_pullback p hF)
  obtain ⟨B, b, hBa, hb, hB, hLC⟩ :=
    exists_nonempty_open_finiteRadicialImage_locallyConstant R r FR hFR
  let : IsOpenImmersion b := hb
  let c : B ⟶ Z := b ≫ V.ι
  let eV := (finiteImageBaseChangeIso R f fV (V.ι ≫ j) p
    (IsPullback.of_hasPullback f (V.ι ≫ j))).app F ≪≫
      (moduleDirectImageClosedSourceIso R fV I.subschemeι).app FP
  let eB := (moduleInverseImageComp R (V.ι ≫ j) b).app G ≪≫
    (moduleInverseImage R b).mapIso eV
  have hBLC : IsFiniteTypeLocallyConstant
      ((moduleInverseImage R c).obj ((moduleInverseImage R j).obj G)) := by
    let e := ((moduleInverseImageComp R j c).app G).symm ≪≫
      eqToIso (congrArg (fun a => (moduleInverseImage R a).obj G)
        (Category.assoc b V.ι j)) ≪≫ eB
    exact (isFiniteTypeLocallyConstant_iff_of_iso e).mpr hLC
  let ec := eqToIso (congrArg
      (fun a => (moduleInverseImage R a).obj ((moduleInverseImage R j).obj G))
      c.isoOpensRange_inv_comp.symm) ≪≫
    (moduleInverseImageComp R c c.isoOpensRange.inv).app ((moduleInverseImage R j).obj G)
  refine ⟨c.opensRange, ⟨c.isoOpensRange.hom (Classical.choice hB)⟩, ?_⟩
  exact (isConstructible_iff_of_iso ec).mpr
    (isConstructible_pullback c.isoOpensRange.inv
      (isConstructible_of_isFiniteTypeLocallyConstant hBLC))

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
