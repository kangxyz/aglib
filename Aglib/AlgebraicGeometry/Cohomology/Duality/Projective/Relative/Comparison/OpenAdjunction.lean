/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.InjectiveResolution
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Single
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Injective.Restriction

/-!
# Pointwise derived Hom for affine open direct images

The original restriction adjunction at a supplied injective resolution gives
an additive equivalence for every actual source complex. Affine quasicoherent
acyclicity identifies the derived target with its ordinary direct image.
All comparisons retain the original resolution inclusion, derived unit and
native shift maps. There is no exactness assumption on open direct image on
all module sheaves and no new global derived adjunction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology

private def openHomIsoAddEquiv {C : Type*} [Category* C] [Preadditive C]
    {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  { Iso.homCongr e f with
    map_add' a b := by
      simp [Iso.homCongr_apply, Preadditive.comp_add, Preadditive.add_comp] }

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [IsAffineHom j]
  (L : U.Modules) [L.IsQuasicoherent]

/-- The actual unshifted direct-image model for the supplied injective resolution. -/
def affineOpenResolutionPushforwardIso (I : InjectiveResolution L) :
    DerivedCategory.Q.obj
        (((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj ((Scheme.Modules.pushforward j).obj L) :=
  CategoryTheory.Adjunction.rightDerivedResolutionIso (G := Scheme.Modules.pushforward j) I ≪≫
    DerivedCategory.Plus.ι.mapIso (affineDerivedPushforwardSingleIso j L)

omit [IsOpenImmersion j] in
/-- The affine model carries the original pushed resolution inclusion to the original
single-complex comparison. This identifies the coefficient arrow before any adjunction. -/
theorem affineOpenResolutionPushforwardIso_unit (I : InjectiveResolution L) :
    DerivedCategory.Q.map
        (((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).map I.ι') ≫
      (affineOpenResolutionPushforwardIso j L I).hom =
        (CategoryTheory.Adjunction.singleImageIso (F := Scheme.Modules.pushforward j) L).hom := by
  let G := Scheme.Modules.pushforward j
  let K := (CochainComplex.singleFunctorPlus U.Modules 0).obj L
  let s : G.mapCochainComplexPlus.obj K ⟶
      (CochainComplex.singleFunctorPlus Y.Modules 0).obj (G.obj L) :=
    ObjectProperty.homMk ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app L)
  change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map I.ι') ≫
      (CategoryTheory.Adjunction.rightDerivedResolutionIso (G := G) I).hom ≫
      DerivedCategory.Plus.ι.map (affineDerivedPushforwardSingleIso j L).hom = _
  rw [← Category.assoc, CategoryTheory.Adjunction.rightDerivedResolutionIso_unit]
  rw [Category.assoc, ← Functor.map_comp]
  erw [affineDerivedPushforwardSingleIso_unit]
  have hs := (DerivedCategory.Plus.QCompιIso Y.Modules).inv.naturality s
  change DerivedCategory.Q.map s.hom ≫
      (DerivedCategory.Plus.QCompιIso Y.Modules).inv.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj (G.obj L)) =
    (DerivedCategory.Plus.QCompιIso Y.Modules).inv.app (G.mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map s) at hs
  erw [← hs]
  simp only [DerivedCategory.Plus.QCompιIso, ObjectProperty.liftCompιIso]
  rfl

/-- The actual shifted direct-image model for the supplied injective resolution. -/
def affineOpenResolutionPushforwardShiftIso (I : InjectiveResolution L) (k : ℤ) :
    DerivedCategory.Q.obj
        (((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).obj
          (I.cochainComplex⟦k⟧)) ≅
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pushforward j).obj L))⟦k⟧ :=
  CategoryTheory.Adjunction.rightDerivedResolutionShiftIso
      (G := Scheme.Modules.pushforward j) I k ≪≫
    (shiftFunctor (DerivedCategory Y.Modules) k).mapIso
      (DerivedCategory.Plus.ι.mapIso (affineDerivedPushforwardSingleIso j L))

/-- Actual pointwise open adjunction for an arbitrary source complex and quasicoherent
coefficient. The forward map goes from restriction to ordinary open direct image. -/
@[no_expose] def affineOpenCochainDerivedHomAddEquiv (I : InjectiveResolution L) (k : ℤ)
    (K : CochainComplex Y.Modules ℤ) :
    (DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      ((DerivedCategory.singleFunctor U.Modules 0).obj L)⟦k⟧) ≃+
    (DerivedCategory.Q.obj K ⟶
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pushforward j).obj L))⟦k⟧) :=
  (openHomIsoAddEquiv (Iso.refl _) (CategoryTheory.Adjunction.resolutionShiftIso I k)).trans
    (((Scheme.Modules.restrictAdjunction j).cochainDerivedHomEquivOfInjectiveResolution I k K).trans
      (openHomIsoAddEquiv (Iso.refl _) (affineOpenResolutionPushforwardShiftIso j L I k)))

/-- The forward pointwise comparison consists of the original resolution, original
cochain adjunction, and original affine acyclic-single comparison. -/
theorem affineOpenCochainDerivedHomAddEquiv_apply (I : InjectiveResolution L) (k : ℤ)
    (K : CochainComplex Y.Modules ℤ)
    (a : DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      ((DerivedCategory.singleFunctor U.Modules 0).obj L)⟦k⟧) :
    affineOpenCochainDerivedHomAddEquiv j L I k K a =
      (Scheme.Modules.restrictAdjunction j).cochainDerivedHomEquivOfInjectiveResolution I k K
          (a ≫ (CategoryTheory.Adjunction.resolutionShiftIso I k).hom) ≫
        (affineOpenResolutionPushforwardShiftIso j L I k).hom := by
  change 𝟙 _ ≫
    (Scheme.Modules.restrictAdjunction j).cochainDerivedHomEquivOfInjectiveResolution I k K
      (𝟙 _ ≫ a ≫ (CategoryTheory.Adjunction.resolutionShiftIso I k).hom) ≫
      (affineOpenResolutionPushforwardShiftIso j L I k).hom = _
  simp only [Category.id_comp]

/-- Every original chain representative is sent to its literal chain adjunct. -/
theorem affineOpenCochainDerivedHomAddEquiv_map (I : InjectiveResolution L) (k : ℤ)
    (K : CochainComplex Y.Modules ℤ)
    (a : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K ⟶
      I.cochainComplex⟦k⟧) :
    affineOpenCochainDerivedHomAddEquiv j L I k K
        (DerivedCategory.Q.map a ≫ (CategoryTheory.Adjunction.resolutionShiftIso I k).inv) =
      DerivedCategory.Q.map
          (((Scheme.Modules.restrictAdjunction j).mapHomologicalComplex (.up ℤ)).homEquiv
            K (I.cochainComplex⟦k⟧) a) ≫
        (affineOpenResolutionPushforwardShiftIso j L I k).hom := by
  rw [affineOpenCochainDerivedHomAddEquiv_apply]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [CategoryTheory.Adjunction.cochainDerivedHomEquivOfInjectiveResolution_map]

/-- Original source-chain precomposition is preserved by this same pointwise adjunction. -/
theorem affineOpenCochainDerivedHomAddEquiv_naturality_left
    (I : InjectiveResolution L) (k : ℤ) {K K' : CochainComplex Y.Modules ℤ}
    (s : K' ⟶ K)
    (a : DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      ((DerivedCategory.singleFunctor U.Modules 0).obj L)⟦k⟧) :
    affineOpenCochainDerivedHomAddEquiv j L I k K'
        (DerivedCategory.Q.map
          (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map s) ≫ a) =
      DerivedCategory.Q.map s ≫ affineOpenCochainDerivedHomAddEquiv j L I k K a := by
  simp only [affineOpenCochainDerivedHomAddEquiv_apply, Category.assoc]
  rw [CategoryTheory.Adjunction.cochainDerivedHomEquivOfInjectiveResolution_naturality_left]
  rw [Category.assoc]

/-- The inverse pointwise transport is original restriction followed by the original
counit on the same shifted injective-resolution complex. -/
theorem affineOpenCochainDerivedHomAddEquiv_symm_map (I : InjectiveResolution L) (k : ℤ)
    (K : CochainComplex Y.Modules ℤ)
    (b : K ⟶ ((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).obj
      (I.cochainComplex⟦k⟧)) :
    (affineOpenCochainDerivedHomAddEquiv j L I k K).symm
        (DerivedCategory.Q.map b ≫ (affineOpenResolutionPushforwardShiftIso j L I k).hom) =
      DerivedCategory.Q.map
          (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map b ≫
            ((Scheme.Modules.restrictAdjunction j).mapHomologicalComplex (.up ℤ)).counit.app
              (I.cochainComplex⟦k⟧)) ≫
        (CategoryTheory.Adjunction.resolutionShiftIso I k).inv := by
  apply (affineOpenCochainDerivedHomAddEquiv j L I k K).injective
  rw [AddEquiv.apply_symm_apply, affineOpenCochainDerivedHomAddEquiv_map]
  congr 1
  have hb := (((Scheme.Modules.restrictAdjunction j).mapHomologicalComplex (.up ℤ)).homEquiv
    K (I.cochainComplex⟦k⟧)).apply_symm_apply b
  rw [Adjunction.homEquiv_counit] at hb
  exact congrArg (DerivedCategory.Q (C := Y.Modules)).map hb.symm

/-- Every global derived arrow has an original resolution representative for which
inverse transport is literally restriction and the original resolution counit. -/
theorem affineOpenCochainDerivedHomAddEquiv_symm_representative
    (I : InjectiveResolution L) (k : ℤ) (K : CochainComplex Y.Modules ℤ)
    (a : DerivedCategory.Q.obj K ⟶
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pushforward j).obj L))⟦k⟧) :
    ∃ b : K ⟶ ((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).obj
        (I.cochainComplex⟦k⟧),
      a = DerivedCategory.Q.map b ≫ (affineOpenResolutionPushforwardShiftIso j L I k).hom ∧
      (affineOpenCochainDerivedHomAddEquiv j L I k K).symm a =
        DerivedCategory.Q.map
            (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map b ≫
              ((Scheme.Modules.restrictAdjunction j).mapHomologicalComplex (.up ℤ)).counit.app
                (I.cochainComplex⟦k⟧)) ≫
          (CategoryTheory.Adjunction.resolutionShiftIso I k).inv := by
  let J := I.cochainComplex⟦k⟧
  let : J.IsStrictlyGE (-k) := I.cochainComplex.isStrictlyGE_shift 0 k (-k) (by omega)
  let : ∀ d : ℤ, Injective (J.X d) := fun d => by
    change Injective (I.cochainComplex.X (d + k))
    infer_instance
  let := (Scheme.Modules.restrictAdjunction j).isKInjective_map_of_injectiveComplex J (-k)
  obtain ⟨b, hb⟩ := (CochainComplex.homotopyDerivedHomEquiv K
    (((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).obj J)).surjective
      (a ≫ (affineOpenResolutionPushforwardShiftIso j L I k).inv)
  obtain ⟨c, rfl⟩ := (HomotopyCategory.quotient Y.Modules (.up ℤ)).map_surjective b
  rw [CochainComplex.homotopyDerivedHomEquiv_map] at hb
  have ha : a = DerivedCategory.Q.map c ≫
      (affineOpenResolutionPushforwardShiftIso j L I k).hom := by
    rw [hb, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨c, ha, ?_⟩
  rw [ha, affineOpenCochainDerivedHomAddEquiv_symm_map]

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- The original restriction counit on a bounded-below complex. -/
def openCochainCounitPlus (S : CochainComplex.Plus U.Modules) :
    (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj
        ((Scheme.Modules.pushforward j).mapCochainComplexPlus.obj S) ⟶ S :=
  ObjectProperty.homMk
    (((Scheme.Modules.restrictAdjunction j).mapHomologicalComplex (.up ℤ)).counit.app S.obj)

/-- Canonical derived restriction followed by the original complex counit, expressed
through the installed exact derived units. -/
def openDerivedRestrictionCounit (K : CochainComplex.Plus Y.Modules)
    (S : CochainComplex.Plus U.Modules)
    (a : DerivedCategory.Plus.Q.obj K ⟶ DerivedCategory.Plus.Q.obj
      ((Scheme.Modules.pushforward j).mapCochainComplexPlus.obj S)) :
    DerivedCategory.Plus.Q.obj ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K) ⟶
      DerivedCategory.Plus.Q.obj S := by
  let F := Scheme.Modules.restrictFunctor j
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact F.rightDerivedFunctorPlusUnit.app K ≫ F.rightDerivedFunctorPlus.map a ≫
    inv (F.rightDerivedFunctorPlusUnit.app
      ((Scheme.Modules.pushforward j).mapCochainComplexPlus.obj S)) ≫
    DerivedCategory.Plus.Q.map (openCochainCounitPlus j S)

/-- On every original chain map, canonical derived restriction is literal restriction
followed by the same original counit. -/
theorem openDerivedRestrictionCounit_map (K : CochainComplex.Plus Y.Modules)
    (S : CochainComplex.Plus U.Modules)
    (b : K ⟶ (Scheme.Modules.pushforward j).mapCochainComplexPlus.obj S) :
    openDerivedRestrictionCounit j K S (DerivedCategory.Plus.Q.map b) =
      DerivedCategory.Plus.Q.map
        ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map b ≫
          openCochainCounitPlus j S) := by
  let F := Scheme.Modules.restrictFunctor j
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hb := F.rightDerivedFunctorPlusUnit.naturality b
  change DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map b) ≫
      F.rightDerivedFunctorPlusUnit.app _ =
    F.rightDerivedFunctorPlusUnit.app K ≫ F.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map b) at hb
  change F.rightDerivedFunctorPlusUnit.app K ≫ _ ≫ _ ≫ _ = _
  rw [← Category.assoc, ← hb]
  dsimp only [F]
  simp only [Category.assoc]
  erw [IsIso.hom_inv_id_assoc]
  exact (DerivedCategory.Plus.Q.map_comp _ _).symm

/-- Canonical restriction/counit is natural under every original coefficient-complex map. -/
theorem openDerivedRestrictionCounit_naturality
    (K : CochainComplex.Plus Y.Modules) {S T : CochainComplex.Plus U.Modules} (r : S ⟶ T)
    (a : DerivedCategory.Plus.Q.obj K ⟶ DerivedCategory.Plus.Q.obj
      ((Scheme.Modules.pushforward j).mapCochainComplexPlus.obj S)) :
    openDerivedRestrictionCounit j K S a ≫ DerivedCategory.Plus.Q.map r =
      openDerivedRestrictionCounit j K T
        (a ≫ DerivedCategory.Plus.Q.map
          ((Scheme.Modules.pushforward j).mapCochainComplexPlus.map r)) := by
  let F := Scheme.Modules.restrictFunctor j
  let G := Scheme.Modules.pushforward j
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let E := asIso F.rightDerivedFunctorPlusUnit
  have hn := E.inv.naturality (G.mapCochainComplexPlus.map r)
  simp only [E, asIso_inv, NatIso.isIso_inv_app] at hn
  change F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
      (G.mapCochainComplexPlus.map r)) ≫ inv (F.rightDerivedFunctorPlusUnit.app _) =
    inv (F.rightDerivedFunctorPlusUnit.app _) ≫ DerivedCategory.Plus.Q.map
      (F.mapCochainComplexPlus.map (G.mapCochainComplexPlus.map r)) at hn
  have hc : F.mapCochainComplexPlus.map (G.mapCochainComplexPlus.map r) ≫
      openCochainCounitPlus j T = openCochainCounitPlus j S ≫ r := by
    apply ObjectProperty.hom_ext
    exact (((Scheme.Modules.restrictAdjunction j).mapHomologicalComplex (.up ℤ)).counit.naturality
      r.hom)
  change (F.rightDerivedFunctorPlusUnit.app K ≫ F.rightDerivedFunctorPlus.map a ≫
      inv (F.rightDerivedFunctorPlusUnit.app _) ≫
      DerivedCategory.Plus.Q.map (openCochainCounitPlus j S)) ≫
      DerivedCategory.Plus.Q.map r =
    F.rightDerivedFunctorPlusUnit.app K ≫ F.rightDerivedFunctorPlus.map
      (a ≫ DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map r)) ≫
      inv (F.rightDerivedFunctorPlusUnit.app _) ≫
      DerivedCategory.Plus.Q.map (openCochainCounitPlus j T)
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (F.rightDerivedFunctorPlus.map
    (DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map r))), hn]
  simp only [Category.assoc]
  have hcQ := congrArg (DerivedCategory.Plus.Q (C := U.Modules)).map hc
  simp only [Functor.map_comp] at hcQ
  rw [hcQ]

/-- At a K-injective original coefficient complex and its K-injective direct image,
canonical derived restriction/counit is bijective. This is the original pointwise adjunction. -/
theorem openDerivedRestrictionCounit_bijective_of_kInjective
    (K : CochainComplex.Plus Y.Modules) (S : CochainComplex.Plus U.Modules)
    [S.obj.IsKInjective]
    [CochainComplex.IsKInjective
      (((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).obj S.obj)] :
    Function.Bijective (openDerivedRestrictionCounit j K S) := by
  let F := Scheme.Modules.restrictFunctor j
  let G := Scheme.Modules.pushforward j
  let E₀ := (Scheme.Modules.restrictAdjunction j).cochainDerivedHomEquivOfKInjective K.obj S.obj
  let E₁ : (DerivedCategory.Plus.Q.obj K ⟶
      DerivedCategory.Plus.Q.obj (G.mapCochainComplexPlus.obj S)) ≃
      (DerivedCategory.Q.obj K.obj ⟶
        DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj S.obj)) :=
    (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι (C := Y.Modules))).homEquiv
  let E₂ : (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K) ⟶
      DerivedCategory.Plus.Q.obj S) ≃
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K.obj) ⟶
        DerivedCategory.Q.obj S.obj) :=
    (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι (C := U.Modules))).homEquiv
  let E := E₁.trans (E₀.symm.toEquiv.trans E₂.symm)
  have heq : openDerivedRestrictionCounit j K S = E := by
    funext a
    obtain ⟨b, hb⟩ := (CochainComplex.homotopyDerivedHomEquiv K.obj
      ((G.mapHomologicalComplex (.up ℤ)).obj S.obj)).surjective
        (DerivedCategory.Plus.ι.map a)
    obtain ⟨c, rfl⟩ := (HomotopyCategory.quotient Y.Modules (.up ℤ)).map_surjective b
    rw [CochainComplex.homotopyDerivedHomEquiv_map] at hb
    let c' : K ⟶ G.mapCochainComplexPlus.obj S := ObjectProperty.homMk c
    have ha : DerivedCategory.Plus.Q.map c' = a := by
      apply DerivedCategory.Plus.ι.map_injective
      exact hb
    rw [← ha, openDerivedRestrictionCounit_map]
    apply E₂.injective
    change E₂ (DerivedCategory.Plus.Q.map
      (F.mapCochainComplexPlus.map c' ≫ openCochainCounitPlus j S)) =
      E₂ (E₂.symm (E₀.symm (E₁ (DerivedCategory.Plus.Q.map c'))))
    rw [Equiv.apply_symm_apply]
    change DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map c ≫
        ((Scheme.Modules.restrictAdjunction j).mapHomologicalComplex (.up ℤ)).counit.app S.obj) =
      E₀.symm (DerivedCategory.Q.map c)
    exact (by
      simpa only [Adjunction.homEquiv_counit] using
        ((Scheme.Modules.restrictAdjunction j).cochainDerivedHomEquivOfKInjective_symm_map
          K.obj S.obj c).symm)
  rw [heq]
  exact E.bijective

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- An original resolution and its original pushed quasi-isomorphism transfer bijectivity
of canonical restriction/counit to the unresolved coefficient complex. -/
theorem openDerivedRestrictionCounit_bijective_of_resolution
    (K : CochainComplex.Plus Y.Modules) {S T : CochainComplex.Plus U.Modules} (r : S ⟶ T)
    [IsIso (DerivedCategory.Plus.Q.map r)]
    [IsIso (DerivedCategory.Plus.Q.map
      ((Scheme.Modules.pushforward j).mapCochainComplexPlus.map r))]
    [T.obj.IsKInjective]
    [CochainComplex.IsKInjective
      (((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)).obj T.obj)] :
    Function.Bijective (openDerivedRestrictionCounit j K S) := by
  let E₁ := Iso.homCongr (Iso.refl (DerivedCategory.Plus.Q.obj K))
    (asIso (DerivedCategory.Plus.Q.map
      ((Scheme.Modules.pushforward j).mapCochainComplexPlus.map r)))
  let E₂ := Iso.homCongr
    (Iso.refl (DerivedCategory.Plus.Q.obj
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)))
    (asIso (DerivedCategory.Plus.Q.map r))
  have heq : E₂ ∘ openDerivedRestrictionCounit j K S =
      openDerivedRestrictionCounit j K T ∘ E₁ := by
    funext a
    change 𝟙 _ ≫ openDerivedRestrictionCounit j K S a ≫ DerivedCategory.Plus.Q.map r =
      openDerivedRestrictionCounit j K T
        (𝟙 _ ≫ a ≫ DerivedCategory.Plus.Q.map
          ((Scheme.Modules.pushforward j).mapCochainComplexPlus.map r))
    simp only [Category.id_comp]
    exact openDerivedRestrictionCounit_naturality j K r a
  have hb := (openDerivedRestrictionCounit_bijective_of_kInjective j K T).comp E₁.bijective
  rw [← heq] at hb
  exact (Equiv.comp_bijective (openDerivedRestrictionCounit j K S) E₂).mp hb

/-- For an affine open and arbitrary quasicoherent coefficient, the canonical native
restriction/counit is bijective in every integer shift and at every actual source complex. -/
theorem affineOpenDerivedRestrictionCounit_bijective [IsAffineHom j]
    (L : U.Modules) [L.IsQuasicoherent] (K : CochainComplex.Plus Y.Modules) (k : ℤ) :
    Function.Bijective (openDerivedRestrictionCounit j K
      (((CochainComplex.singleFunctorPlus U.Modules 0).obj L)⟦k⟧)) := by
  let I := injectiveResolution L
  let G := Scheme.Modules.pushforward j
  let F := G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q
  let r₀ := I.ιPlus
  let r := (shiftFunctor (CochainComplex.Plus U.Modules) k).map r₀
  let T := I.cochainComplexPlus⟦k⟧
  let : IsIso (G.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus U.Modules 0).obj L)) :=
    isIso_derivedPushforwardPlusUnit_single_of_isAffineHom j L
  let : IsIso (F.map r₀) := by
    have hc : IsIso (DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map I.ιPlus) ≫
        (I.rightDerivedFunctorPlusIso G).hom) := by
      rw [I.rightDerivedFunctorPlusIso_unit G]
      infer_instance
    change IsIso (DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map I.ιPlus))
    let := hc
    exact IsIso.of_isIso_comp_right _ (I.rightDerivedFunctorPlusIso G).hom
  let : IsIso (DerivedCategory.Plus.Q.map r₀) :=
    inferInstanceAs (IsIso (DerivedCategory.Plus.Q.map I.ιPlus))
  let : IsIso (DerivedCategory.Plus.Q.map r) := by
    change IsIso (((shiftFunctor (CochainComplex.Plus U.Modules) k) ⋙
      DerivedCategory.Plus.Q).map r₀)
    exact (NatIso.isIso_map_iff
      ((DerivedCategory.Plus.Q (C := U.Modules)).commShiftIso k) r₀).mpr (by
        change IsIso ((shiftFunctor (DerivedCategory.Plus U.Modules) k).map
          (DerivedCategory.Plus.Q.map r₀))
        infer_instance)
  let : IsIso (DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map r)) := by
    change IsIso (((shiftFunctor (CochainComplex.Plus U.Modules) k) ⋙ F).map r₀)
    exact (NatIso.isIso_map_iff (F.commShiftIso k) r₀).mpr (by
      change IsIso ((shiftFunctor (DerivedCategory.Plus Y.Modules) k).map (F.map r₀))
      infer_instance)
  let : (I.cochainComplex⟦k⟧).IsStrictlyGE (-k) :=
    I.cochainComplex.isStrictlyGE_shift 0 k (-k) (by omega)
  let : ∀ d : ℤ, Injective ((I.cochainComplex⟦k⟧).X d) := fun d => by
    change Injective (I.cochainComplex.X (d + k))
    infer_instance
  let : (I.cochainComplex⟦k⟧).IsKInjective :=
    CochainComplex.isKInjective_of_injective (I.cochainComplex⟦k⟧) (-k)
  let eT : T.obj ≅ I.cochainComplex⟦k⟧ :=
    ((CochainComplex.Plus.ι U.Modules).commShiftIso k).app I.cochainComplexPlus
  let : T.obj.IsKInjective := CochainComplex.isKInjective_of_iso eT.symm
  let := (Scheme.Modules.restrictAdjunction j).isKInjective_map_of_injectiveComplex
    (I.cochainComplex⟦k⟧) (-k)
  let : CochainComplex.IsKInjective
      ((G.mapHomologicalComplex (.up ℤ)).obj T.obj) :=
    CochainComplex.isKInjective_of_iso ((G.mapHomologicalComplex (.up ℤ)).mapIso eT).symm
  exact openDerivedRestrictionCounit_bijective_of_resolution j K r

end AlgebraicGeometry.Scheme.Cohomology
