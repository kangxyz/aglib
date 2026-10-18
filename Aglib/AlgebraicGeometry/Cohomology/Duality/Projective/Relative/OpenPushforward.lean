/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.FiniteLocallyFree

/-!
# Differential coefficients and affine open direct images

The original affine module base-change map and ordinary projection formula give
an isomorphism between the actual top differential coefficient of an affine open
direct image and the direct image of its actual differential coefficient. The
base-change square is the native pullback of the open immersion along the
original morphism. Coefficients are arbitrary quasicoherent modules. There is
no flatness, Noetherianity or coherence assumption.

This is the coefficient comparison used by the finite affine-cover argument for
relative projective Serre duality. Its forward map retains the original module
base-change mate, projection-formula arrow and differential restriction map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y U : Scheme.{u}} (p : X ⟶ Y) (j : U ⟶ Y)
  [IsOpenImmersion j] (n : ℕ)

/-- The actual top differential pullback comparison on the native open square. -/
def relativeTopDifferentialOpenPullbackIso :
    (Scheme.Modules.pullback (pullback.snd j p)).obj
        (moduleExteriorPower X (relativeDifferentialSheaf p) n) ≅
      moduleExteriorPower (pullback j p)
        (relativeDifferentialSheaf (pullback.fst j p)) n :=
  ((Scheme.Modules.restrictFunctorIsoPullback (pullback.snd j p)).app _).symm ≪≫
    relativeTopDifferentialRestrictionIso p (pullback.snd j p) (pullback.fst j p) j
      (IsPullback.of_hasPullback j p).flip.w n

private def differentialOpenPushforwardNat :
    Scheme.Modules.pushforward j ⋙ relativeTopDifferentialCoefficientsFunctor p n ⟶
      relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n ⋙
        Scheme.Modules.pushforward (pullback.snd j p) := by
  let W := pullback j p
  let i : W ⟶ X := pullback.snd j p
  let q : W ⟶ U := pullback.fst j p
  let E := moduleExteriorPower X (relativeDifferentialSheaf p) n
  let Eq := moduleExteriorPower W (relativeDifferentialSheaf q) n
  let β := cartesianBaseChangeMap q i j p (IsPullback.of_hasPullback j p)
  let γ : Scheme.Modules.pushforward i ⋙ moduleTensorLeftFunctor X E ⟶
      moduleTensorLeftFunctor W ((Scheme.Modules.pullback i).obj E) ⋙
        Scheme.Modules.pushforward i := {
    app M := projectionFormulaMap i E M
    naturality {_ _} f := projectionFormulaMap_naturality i E f }
  let δ : moduleTensorLeftFunctor W ((Scheme.Modules.pullback i).obj E) ⟶
      moduleTensorLeftFunctor W Eq :=
    moduleTensorCoefficientMap W (relativeTopDifferentialOpenPullbackIso p j n).hom
  exact Functor.whiskerRight β (moduleTensorLeftFunctor X E) ≫
    Functor.whiskerLeft (Scheme.Modules.pullback q) γ ≫
    Functor.whiskerLeft (Scheme.Modules.pullback q)
      (Functor.whiskerRight δ (Scheme.Modules.pushforward i))

/-- The original affine base-change/projection-formula comparison for actual differential
coefficients. It is defined for every module, before imposing invertibility hypotheses. -/
@[no_expose] def relativeTopDifferentialOpenPushforwardMap (L : U.Modules) :
    (relativeTopDifferentialCoefficientsFunctor p n).obj
        ((Scheme.Modules.pushforward j).obj L) ⟶
      (Scheme.Modules.pushforward (pullback.snd j p)).obj
        ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L) :=
  (differentialOpenPushforwardNat p j n).app L

/-- The forward map is the literal original affine mate, projection-formula map, and
original top differential pullback comparison. -/
theorem relativeTopDifferentialOpenPushforwardMap_eq (L : U.Modules) :
    relativeTopDifferentialOpenPushforwardMap p j n L =
      (moduleTensorLeftFunctor X
        (moduleExteriorPower X (relativeDifferentialSheaf p) n)).map
          (moduleBaseChangeMap j p L) ≫
        projectionFormulaMap (pullback.snd j p)
          (moduleExteriorPower X (relativeDifferentialSheaf p) n)
          ((Scheme.Modules.pullback (pullback.fst j p)).obj L) ≫
        (Scheme.Modules.pushforward (pullback.snd j p)).map
          ((moduleTensorCoefficientMap (pullback j p)
            (relativeTopDifferentialOpenPullbackIso p j n).hom).app
              ((Scheme.Modules.pullback (pullback.fst j p)).obj L)) := by
  rw [moduleBaseChangeMap_eq_cartesianBaseChangeMap]
  rfl

private theorem projectionFormulaMap_eq_adjoint {V Z : Scheme.{u}} (i : V ⟶ Z)
    (E : Z.Modules) (M : V.Modules) :
    projectionFormulaMap i E M =
      (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _
        (pullbackTensorMap i E ((Scheme.Modules.pushforward i).obj M) ≫
          tensorSheafMap V (𝟙 ((Scheme.Modules.pullback i).obj E))
            ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app M)) := by
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_adjoint,
    Category.assoc, ← pushforwardTensorMap_naturality, ← Category.assoc,
    tensorSheafMap_comp]
  simp only [Adjunction.right_triangle_components]
  rfl

/-- The same comparison is the actual pullback/direct-image adjunct of the tensor
pullback map, the original square, and the original open direct-image counit. -/
theorem relativeTopDifferentialOpenPushforwardMap_eq_homEquiv (L : U.Modules) :
    let i := pullback.snd j p
    let q := pullback.fst j p
    let E := moduleExteriorPower X (relativeDifferentialSheaf p) n
    relativeTopDifferentialOpenPushforwardMap p j n L =
      (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _
        (pullbackTensorMap i E
            ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pushforward j).obj L)) ≫
          tensorSheafMap (pullback j p)
            (relativeTopDifferentialOpenPullbackIso p j n).hom
            ((Scheme.Modules.pullbackSquareIso q i j p (IsPullback.of_hasPullback j p).w).hom.app
                ((Scheme.Modules.pushforward j).obj L) ≫
              (Scheme.Modules.pullback q).map
                ((Scheme.Modules.pullbackPushforwardAdjunction j).counit.app L))) := by
  dsimp only
  let W := pullback j p
  let i : W ⟶ X := pullback.snd j p
  let q : W ⟶ U := pullback.fst j p
  let E := moduleExteriorPower X (relativeDifferentialSheaf p) n
  let M := (Scheme.Modules.pullback q).obj L
  let β := moduleBaseChangeMap j p L
  let δ := (relativeTopDifferentialOpenPullbackIso p j n).hom
  have hβ : (Scheme.Modules.pullback i).map β ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app M =
      (Scheme.Modules.pullbackSquareIso q i j p (IsPullback.of_hasPullback j p).w).hom.app
          ((Scheme.Modules.pushforward j).obj L) ≫
        (Scheme.Modules.pullback q).map
          ((Scheme.Modules.pullbackPushforwardAdjunction j).counit.app L) := by
    erw [← Adjunction.homEquiv_counit]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm_apply_apply _
  rw [relativeTopDifferentialOpenPushforwardMap_eq, projectionFormulaMap_eq_adjoint]
  erw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
  apply congrArg ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _)
  change (Scheme.Modules.pullback i).map (tensorSheafMap X (𝟙 E) β) ≫
      (pullbackTensorMap i E ((Scheme.Modules.pushforward i).obj M) ≫
        tensorSheafMap W (𝟙 ((Scheme.Modules.pullback i).obj E))
          ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app M)) ≫
      tensorSheafMap W δ (𝟙 M) = _
  simp only [Category.assoc]
  rw [pullbackTensorMap_naturality_assoc, tensorSheafMap_comp_assoc, tensorSheafMap_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
    Category.comp_id, hβ]

private theorem homEquiv_leftAdjointUniq_comp
    {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G : D ⥤ C} (A : F ⊣ G) (B : F' ⊣ G)
    {M : C} {N : D} (f : F'.obj M ⟶ N) :
    A.homEquiv M N ((A.leftAdjointUniq B).hom.app M ≫ f) = B.homEquiv M N f := by
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

private theorem counit_leftAdjointUniq_inv
    {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G : D ⥤ C} (A : F ⊣ G) (B : F' ⊣ G) (N : D) :
    (A.leftAdjointUniq B).inv.app (G.obj N) ≫ A.counit.app N = B.counit.app N := by
  apply (cancel_epi ((A.leftAdjointUniq B).hom.app (G.obj N))).mp
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  apply (A.homEquiv _ _).injective
  rw [homEquiv_leftAdjointUniq_comp]
  simp only [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]

private theorem tensorRestrictionIso_inv_section {V Z : Scheme.{u}}
    (a : V ⟶ Z) [IsOpenImmersion a] (E M : Z.Modules) (U : V.Opens)
    (e : Γ(E.restrict a, U)) (m : Γ(M.restrict a, U)) :
    (tensorRestrictionIso a E M).inv.app U
        (moduleTensorSection Z E M (a ''ᵁ U) e m) =
      moduleTensorSection V (E.restrict a) (M.restrict a) U e m := by
  have h := congrArg ((tensorRestrictionIso a E M).inv.app U)
    (tensorRestrictionIso_section a E M U e m)
  have hc := congrArg (fun f => f.val.app (Opposite.op U)
    (moduleTensorSection V (E.restrict a) (M.restrict a) U e m))
      (tensorRestrictionIso a E M).hom_inv_id
  exact h.symm.trans hc

private theorem tensorRestrictionIso_inv_adjoint {V Z : Scheme.{u}}
    (a : V ⟶ Z) [IsOpenImmersion a] (E M : Z.Modules) :
    (Scheme.Modules.restrictAdjunction a).homEquiv _ _ (tensorRestrictionIso a E M).inv =
      tensorSheafMap Z ((Scheme.Modules.restrictAdjunction a).unit.app E)
          ((Scheme.Modules.restrictAdjunction a).unit.app M) ≫
        pushforwardTensorMap a (E.restrict a) (M.restrict a) := by
  rw [Adjunction.homEquiv_unit]
  apply moduleTensor_hom_ext
  intro U e m
  change (tensorRestrictionIso a E M).inv.app (a ⁻¹ᵁ U)
      (((moduleTensorLeftFunctor Z E).obj M).presheaf.map
        (homOfLE (a.image_preimage_le U)).op (moduleTensorSection Z E M U e m)) =
    (pushforwardTensorMap a (E.restrict a) (M.restrict a)).app U
      ((tensorSheafMap Z ((Scheme.Modules.restrictAdjunction a).unit.app E)
        ((Scheme.Modules.restrictAdjunction a).unit.app M)).val.app (Opposite.op U)
          (moduleTensorSection Z E M U e m))
  rw [moduleTensorSection_restrict]
  erw [tensorSheafMap_tmul Z ((Scheme.Modules.restrictAdjunction a).unit.app E)
    ((Scheme.Modules.restrictAdjunction a).unit.app M) (Opposite.op U) e m]
  erw [pushforwardTensorMap_tmul a (E.restrict a) (M.restrict a) (Opposite.op U)]
  exact tensorRestrictionIso_inv_section a E M (a ⁻¹ᵁ U) _ _

private theorem pullbackTensorMap_open {V Z : Scheme.{u}}
    (a : V ⟶ Z) [IsOpenImmersion a] (E M : Z.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback a).hom.app
        ((moduleTensorLeftFunctor Z E).obj M) ≫ pullbackTensorMap a E M =
      (tensorRestrictionIso a E M).inv ≫
        tensorSheafMap V ((Scheme.Modules.restrictFunctorIsoPullback a).hom.app E)
          ((Scheme.Modules.restrictFunctorIsoPullback a).hom.app M) := by
  apply ((Scheme.Modules.restrictAdjunction a).homEquiv _ _).injective
  change (Scheme.Modules.restrictAdjunction a).homEquiv _ _
    (((Scheme.Modules.restrictAdjunction a).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction a)).hom.app _ ≫ _) = _
  erw [homEquiv_leftAdjointUniq_comp]
  erw [pullbackTensorMap_adjoint, Adjunction.homEquiv_naturality_right,
    tensorRestrictionIso_inv_adjoint]
  have hE := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction a) (Scheme.Modules.pullbackPushforwardAdjunction a) E
  have hM := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction a) (Scheme.Modules.pullbackPushforwardAdjunction a) M
  rw [Category.assoc, ← pushforwardTensorMap_naturality, ← Category.assoc,
    tensorSheafMap_comp]
  exact (congrArg₂ (fun f g => tensorSheafMap Z f g ≫
    pushforwardTensorMap a ((Scheme.Modules.pullback a).obj E)
      ((Scheme.Modules.pullback a).obj M)) hE hM).symm

private theorem restrictPullbackCounit {V Z : Scheme.{u}}
    (a : V ⟶ Z) [IsOpenImmersion a] (M : V.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback a).inv.app
        ((Scheme.Modules.pushforward a).obj M) ≫
      (Scheme.Modules.restrictAdjunction a).counit.app M =
        (Scheme.Modules.pullbackPushforwardAdjunction a).counit.app M := by
  exact counit_leftAdjointUniq_inv (Scheme.Modules.restrictAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction a) M

private theorem pullbackOpenSquare_counit (L : U.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback (pullback.snd j p)).hom.app
        ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pushforward j).obj L)) ≫
      (Scheme.Modules.pullbackSquareIso (pullback.fst j p) (pullback.snd j p) j p
        (IsPullback.of_hasPullback j p).w).hom.app ((Scheme.Modules.pushforward j).obj L) ≫
      (Scheme.Modules.pullback (pullback.fst j p)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction j).counit.app L) =
    (Scheme.Modules.pullbackOpenSquare (pullback.snd j p) (pullback.fst j p) p j
      (IsPullback.of_hasPullback j p).flip.w).hom.app ((Scheme.Modules.pushforward j).obj L) ≫
      (Scheme.Modules.pullback (pullback.fst j p)).map
        ((Scheme.Modules.restrictAdjunction j).counit.app L) := by
  simp only [Scheme.Modules.pullbackOpenSquare, Scheme.Modules.pullbackSquareIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, restrictPullbackCounit]

private theorem tensorSheafMap_threeSteps (V : Scheme.{u})
    {E E' A A' B : V.Modules} (d : E ⟶ E') (a : A ⟶ A') (b : A' ⟶ B) :
    tensorSheafMap V (𝟙 E) a ≫ tensorSheafMap V d (𝟙 A') ≫
      tensorSheafMap V (𝟙 E') b = tensorSheafMap V d (a ≫ b) := by
  erw [tensorSheafMap_comp_assoc, tensorSheafMap_comp]
  simp only [Category.id_comp, Category.comp_id]

set_option maxHeartbeats 400000 in
-- Converting this original tensor square between the two native adjunctions exceeded 200000.
/-- The same original comparison is the restriction adjunct of the original differential
coefficient restriction followed by the original open direct-image counit. This is the
forward-map compatibility used by the relative Serre affine-cover argument. -/
theorem relativeTopDifferentialOpenPushforwardMap_eq_restrictHomEquiv (L : U.Modules) :
    let i := pullback.snd j p
    let q := pullback.fst j p
    relativeTopDifferentialOpenPushforwardMap p j n L =
      (Scheme.Modules.restrictAdjunction i).homEquiv _ _
        ((relativeTopDifferentialCoefficientsRestrictionIso p i q j
            (IsPullback.of_hasPullback j p).flip.w n).hom.app
              ((Scheme.Modules.pushforward j).obj L) ≫
          (relativeTopDifferentialCoefficientsFunctor q n).map
            ((Scheme.Modules.restrictAdjunction j).counit.app L)) := by
  dsimp only
  let W := pullback j p
  let i : W ⟶ X := pullback.snd j p
  let q : W ⟶ U := pullback.fst j p
  let E := moduleExteriorPower X (relativeDifferentialSheaf p) n
  let A := (Scheme.Modules.pullback p).obj ((Scheme.Modules.pushforward j).obj L)
  let B := (relativeTopDifferentialCoefficientsFunctor q n).obj L
  let D := (relativeTopDifferentialRestrictionIso p i q j
    (IsPullback.of_hasPullback j p).flip.w n).hom
  let γ := (Scheme.Modules.pullbackSquareIso q i j p (IsPullback.of_hasPullback j p).w).hom.app
      ((Scheme.Modules.pushforward j).obj L) ≫
    (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackPushforwardAdjunction j).counit.app L)
  let K : (Scheme.Modules.pullback i).obj ((moduleTensorLeftFunctor X E).obj A) ⟶ B :=
    pullbackTensorMap i E A ≫ tensorSheafMap W
      (relativeTopDifferentialOpenPullbackIso p j n).hom γ
  calc
    relativeTopDifferentialOpenPushforwardMap p j n L =
        (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _ K :=
      relativeTopDifferentialOpenPushforwardMap_eq_homEquiv p j n L
    _ = (Scheme.Modules.restrictAdjunction i).homEquiv _ _
        ((Scheme.Modules.restrictFunctorIsoPullback i).hom.app
          ((moduleTensorLeftFunctor X E).obj A) ≫ K) :=
      (homEquiv_leftAdjointUniq_comp (Scheme.Modules.restrictAdjunction i)
        (Scheme.Modules.pullbackPushforwardAdjunction i) K).symm
    _ = (Scheme.Modules.restrictAdjunction i).homEquiv _ _
        ((relativeTopDifferentialCoefficientsRestrictionIso p i q j
            (IsPullback.of_hasPullback j p).flip.w n).hom.app
              ((Scheme.Modules.pushforward j).obj L) ≫
          (relativeTopDifferentialCoefficientsFunctor q n).map
            ((Scheme.Modules.restrictAdjunction j).counit.app L)) := by
      apply congrArg ((Scheme.Modules.restrictAdjunction i).homEquiv _ _)
      change (Scheme.Modules.restrictFunctorIsoPullback i).hom.app
          ((moduleTensorLeftFunctor X E).obj A) ≫
          (pullbackTensorMap i E A ≫ tensorSheafMap W
            ((relativeTopDifferentialOpenPullbackIso p j n).hom) γ) = _
      erw [← Category.assoc, pullbackTensorMap_open i E A, Category.assoc,
        tensorSheafMap_comp W ((Scheme.Modules.restrictFunctorIsoPullback i).hom.app E)
          ((Scheme.Modules.restrictFunctorIsoPullback i).hom.app A)
          (relativeTopDifferentialOpenPullbackIso p j n).hom γ]
      have hD : (Scheme.Modules.restrictFunctorIsoPullback i).hom.app E ≫
          (relativeTopDifferentialOpenPullbackIso p j n).hom = D := by
        change (Scheme.Modules.restrictFunctorIsoPullback i).hom.app E ≫
          ((Scheme.Modules.restrictFunctorIsoPullback i).inv.app E ≫ D) = D
        rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      erw [hD, pullbackOpenSquare_counit p j L]
      dsimp only [relativeTopDifferentialCoefficientsRestrictionIso,
        relativeTopDifferentialCoefficientsFunctor, Iso.trans_hom, Iso.symm_hom,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
        Functor.comp_map]
      change (tensorRestrictionIso i E A).inv ≫ tensorSheafMap W D
          ((Scheme.Modules.pullbackOpenSquare i q p j
              (IsPullback.of_hasPullback j p).flip.w).hom.app
                ((Scheme.Modules.pushforward j).obj L) ≫
            (Scheme.Modules.pullback q).map ((Scheme.Modules.restrictAdjunction j).counit.app L)) =
        (tensorRestrictionIso i E A).inv ≫
          tensorSheafMap W (𝟙 (E.restrict i))
            ((Scheme.Modules.pullbackOpenSquare i q p j
              (IsPullback.of_hasPullback j p).flip.w).hom.app
                ((Scheme.Modules.pushforward j).obj L)) ≫
          tensorSheafMap W D (𝟙 _) ≫
          tensorSheafMap W (𝟙 _) ((Scheme.Modules.pullback q).map
            ((Scheme.Modules.restrictAdjunction j).counit.app L))
      exact congrArg (fun f => (tensorRestrictionIso i E A).inv ≫ f)
        (tensorSheafMap_threeSteps W D
          ((Scheme.Modules.pullbackOpenSquare i q p j
            (IsPullback.of_hasPullback j p).flip.w).hom.app
              ((Scheme.Modules.pushforward j).obj L))
          ((Scheme.Modules.pullback q).map
            ((Scheme.Modules.restrictAdjunction j).counit.app L))).symm

/-- The original comparison is natural in the module on the open base. -/
@[reassoc] theorem relativeTopDifferentialOpenPushforwardMap_naturality
    {L L' : U.Modules} (f : L ⟶ L') :
    (relativeTopDifferentialCoefficientsFunctor p n).map
        ((Scheme.Modules.pushforward j).map f) ≫
      relativeTopDifferentialOpenPushforwardMap p j n L' =
    relativeTopDifferentialOpenPushforwardMap p j n L ≫
      (Scheme.Modules.pushforward (pullback.snd j p)).map
        ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).map f) :=
  (differentialOpenPushforwardNat p j n).naturality f

/-- Affine open direct images commute with the actual differential coefficient functor.
Only the ambient top differential line needs to be finite locally free. -/
theorem relativeTopDifferentialOpenPushforwardMap_isIso
    [IsAffineHom j] (L : U.Modules) [L.IsQuasicoherent]
    [IsFiniteLocallyFree X (moduleExteriorPower X (relativeDifferentialSheaf p) n)] :
    IsIso (relativeTopDifferentialOpenPushforwardMap p j n L) := by
  rw [relativeTopDifferentialOpenPushforwardMap_eq]
  let := moduleBaseChangeMap_isIso j p L
  let := isIso_projectionFormulaMap (pullback.snd j p)
    (moduleExteriorPower X (relativeDifferentialSheaf p) n)
    ((Scheme.Modules.pullback (pullback.fst j p)).obj L)
  have : IsIso
      ((moduleTensorCoefficientMap (pullback j p)
        (relativeTopDifferentialOpenPullbackIso p j n).hom).app
          ((Scheme.Modules.pullback (pullback.fst j p)).obj L)) := by
    change IsIso ((moduleTensorRightFunctor (pullback j p)
      ((Scheme.Modules.pullback (pullback.fst j p)).obj L)).map
        (relativeTopDifferentialOpenPullbackIso p j n).hom)
    infer_instance
  infer_instance

/-- The actual differential coefficient/open-direct-image isomorphism, retaining the
original affine module base-change and projection-formula arrow. -/
def relativeTopDifferentialOpenPushforwardIso
    [IsAffineHom j] (L : U.Modules) [L.IsQuasicoherent]
    [IsFiniteLocallyFree X (moduleExteriorPower X (relativeDifferentialSheaf p) n)] :
    (relativeTopDifferentialCoefficientsFunctor p n).obj
        ((Scheme.Modules.pushforward j).obj L) ≅
      (Scheme.Modules.pushforward (pullback.snd j p)).obj
        ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L) := by
  letI := relativeTopDifferentialOpenPushforwardMap_isIso p j n L
  exact asIso (relativeTopDifferentialOpenPushforwardMap p j n L)

/-- The isomorphism has exactly the original comparison as its forward map. -/
theorem relativeTopDifferentialOpenPushforwardIso_hom
    [IsAffineHom j] (L : U.Modules) [L.IsQuasicoherent]
    [IsFiniteLocallyFree X (moduleExteriorPower X (relativeDifferentialSheaf p) n)] :
    (relativeTopDifferentialOpenPushforwardIso p j n L).hom =
      relativeTopDifferentialOpenPushforwardMap p j n L := rfl

end AlgebraicGeometry.Scheme.Cohomology
