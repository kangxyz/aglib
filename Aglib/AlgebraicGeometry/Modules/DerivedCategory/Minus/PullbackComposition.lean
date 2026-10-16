/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Flat.Pullback
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Minus.Pullback
public import Aglib.AlgebraicGeometry.Modules.Complex.Pullback


/-!
# Composition of actual arbitrary bounded-above derived pullbacks

The comparison is built from the original geometric pullback composition
isomorphism. The second flat-resolution augmentation remains a quasi-isomorphism
under arbitrary pullback because the first pulled-back model is genuinely flat.
Naturality gives the actual ambient contravariant composition isomorphism.
Pentagon coherence, triangulatedness, and preservation of local perfectness are
separate results, not asserted here.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedMinusPullbackComposition.lean`.
SHA-256: `7c11f65254689134ba4172a2246b281ee57f5297fb780b6825e092f422dd3921`.
Selected source lines: 1–197.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

open CochainComplex


open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- Termwise pullback preserves actual upper support; no quasi-isomorphism assertion is made here.
-/
def pullbackBoundedFunctor (f : X ⟶ Y) :
    BoundedAboveComplex Y.Modules ⥤ BoundedAboveComplex X.Modules :=
  (boundedAbove X.Modules).lift ((boundedAbove Y.Modules).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.pullback f)
    (fun K => ⟨chosenUpperBound K, by
      rw [CochainComplex.isStrictlyLE_iff]
      intro n hn
      exact (Scheme.Modules.pullback f).map_isZero (K.obj.isZero_of_isStrictlyLE _ n hn)⟩)

/-- The flat model of the bounded-above sheaf complex `K`, packaged with the chosen upper bound of
its underlying presheaf model. -/
def flatModelBounded (X : Scheme.{u}) (K : BoundedAboveComplex X.Modules) :
    BoundedAboveComplex X.Modules :=
  ⟨flatModel X K, chosenUpperBound ((underlyingPresheafBoundedFunctor X).obj K), inferInstance⟩

/-- The bounded-above complex obtained by pulling back the chosen flat model of `K` along the
scheme morphism `f : X ⟶ Y`. -/
def pullbackFlatModelBounded (f : X ⟶ Y) (K : BoundedAboveComplex Y.Modules) :
    BoundedAboveComplex X.Modules := (pullbackBoundedFunctor f).obj (flatModelBounded Y K)

/-- The chain map between pulled-back flat models obtained by applying the flat-model map of `s`
and then bounded-above pullback along `f`. -/
def pullbackFlatModelBoundedMap (f : X ⟶ Y) {K L : BoundedAboveComplex Y.Modules} (s : K ⟶ L) :
    pullbackFlatModelBounded f K ⟶ pullbackFlatModelBounded f L :=
  (pullbackBoundedFunctor f).map (ObjectProperty.homMk (flatModelMap s))

theorem pullbackFlatModelBounded_flat (f : X ⟶ Y) (K : BoundedAboveComplex Y.Modules) (n : ℤ) :
    stalkwiseFlat X ((pullbackFlatModelBounded f K).obj.X n) :=
  stalkwiseFlat_pullback f (flatModel_flat Y K n)

@[simp]
theorem resolvedPullbackFunctorMinus_obj (f : X ⟶ Y) [HasDerivedCategory.{w₁} X.Modules]
    (K : BoundedAboveComplex Y.Modules) :
    (resolvedPullbackFunctorMinus f).obj K =
      (boundedAboveQMinus X.Modules).obj (pullbackFlatModelBounded f K) := rfl

@[simp]
theorem resolvedPullbackFunctorMinus_map (f : X ⟶ Y) [HasDerivedCategory.{w₁} X.Modules]
    {K L : BoundedAboveComplex Y.Modules} (s : K ⟶ L) :
    (resolvedPullbackFunctorMinus f).map s =
      (boundedAboveQMinus X.Modules).map (pullbackFlatModelBoundedMap f s) := by
  apply ObjectProperty.hom_ext
  exact resolvedPullbackFunctor_map f s

/-- The flat-model augmentation gives an actual comparison with termwise pullback on flat inputs. -/
def resolvedFlatComparisonMinus (f : X ⟶ Y) [HasDerivedCategory.{w₁} X.Modules]
    (K : BoundedAboveComplex Y.Modules) (hK : ∀ n, stalkwiseFlat Y (K.obj.X n)) :
    (resolvedPullbackFunctorMinus f).obj K ≅
      (boundedAboveQMinus X.Modules).obj ((pullbackBoundedFunctor f).obj K) := by
  have : QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map (flatModelπ Y K)) :=
    quasiIso_pullback_of_boundedAbove_stalkwiseFlat f (flatModel_flat Y K) hK
      (chosenUpperBound ((underlyingPresheafBoundedFunctor Y).obj K)) (chosenUpperBound K)
      (fun n hn => (flatModel Y K).isZero_of_isStrictlyLE _ n hn)
      (fun n hn => K.obj.isZero_of_isStrictlyLE _ n hn) _
  exact ObjectProperty.isoMk _
    (asIso (DerivedCategory.Q.map ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map
      (flatModelπ Y
      K))))

/-- This comparison is natural for actual maps between arbitrary bounded-above flat complexes. -/
@[reassoc]
theorem resolvedFlatComparisonMinus_naturality (f : X ⟶ Y) [HasDerivedCategory.{w₁} X.Modules]
    {K L : BoundedAboveComplex Y.Modules} (s : K ⟶ L)
    (hK : ∀ n, stalkwiseFlat Y (K.obj.X n)) (hL : ∀ n, stalkwiseFlat Y (L.obj.X n)) :
    (resolvedPullbackFunctorMinus f).map s ≫ (resolvedFlatComparisonMinus f L hL).hom =
      (resolvedFlatComparisonMinus f K hK).hom ≫
        (boundedAboveQMinus X.Modules).map ((pullbackBoundedFunctor f).map s) := by
  apply ObjectProperty.hom_ext
  change (resolvedPullbackFunctor f).map s ≫
      DerivedCategory.Q.map ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map (flatModelπ Y
        L)) =
    DerivedCategory.Q.map ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map (flatModelπ Y
      K)) ≫
      DerivedCategory.Q.map ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map s.hom)
  rw [resolvedPullbackFunctor_map]
  simpa only [Functor.map_comp, AlgebraicGeometry.Scheme.Modules.Complex.pullback] using
    DerivedCategory.Q_map_eq_of_homotopy X.Modules
    ((Scheme.Modules.pullback f).mapHomotopy (flatModelMapHomotopy s))

@[reassoc]
theorem resolvedFlatComparisonMinus_inv_naturality (f : X ⟶ Y) [HasDerivedCategory.{w₁} X.Modules]
    {K L : BoundedAboveComplex Y.Modules} (s : K ⟶ L)
    (hK : ∀ n, stalkwiseFlat Y (K.obj.X n)) (hL : ∀ n, stalkwiseFlat Y (L.obj.X n)) :
    (boundedAboveQMinus X.Modules).map ((pullbackBoundedFunctor f).map s) ≫
        (resolvedFlatComparisonMinus f L hL).inv =
      (resolvedFlatComparisonMinus f K hK).inv ≫ (resolvedPullbackFunctorMinus f).map s := by
  apply (cancel_epi (resolvedFlatComparisonMinus f K hK).hom).mp
  rw [← Category.assoc, ← resolvedFlatComparisonMinus_naturality f s hK hL]
  simp

variable (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} Y.Modules]
    [HasDerivedCategory.{w₃} Z.Modules]

/-- The actual geometric composition isomorphism, evaluated on the original chosen flat model. -/
def resolvedPullbackCompGeometric (K : BoundedAboveComplex Z.Modules) :
    (resolvedPullbackFunctorMinus (f ≫ g)).obj K ≅
      (boundedAboveQMinus X.Modules).obj
        ((pullbackBoundedFunctor f).obj (pullbackFlatModelBounded g K)) :=
  ObjectProperty.isoMk _ (DerivedCategory.Q.mapIso
    ((AlgebraicGeometry.Scheme.Modules.Complex.pullbackCompIso f g).app (flatModel Z K)))

omit [HasDerivedCategory.{w₂} Y.Modules] [HasDerivedCategory.{w₃} Z.Modules] in
@[reassoc]
theorem resolvedPullbackCompGeometric_naturality {K L : BoundedAboveComplex Z.Modules} (s : K ⟶ L) :
    (resolvedPullbackFunctorMinus (f ≫ g)).map s ≫ (resolvedPullbackCompGeometric f g L).hom =
      (resolvedPullbackCompGeometric f g K).hom ≫
        (boundedAboveQMinus X.Modules).map
          ((pullbackBoundedFunctor f).map (pullbackFlatModelBoundedMap g s)) := by
  apply ObjectProperty.hom_ext
  change (resolvedPullbackFunctor (f ≫ g)).map s ≫
      DerivedCategory.Q.map
        ((AlgebraicGeometry.Scheme.Modules.Complex.pullbackCompIso f g).hom.app (flatModel Z L)) =
    DerivedCategory.Q.map
        ((AlgebraicGeometry.Scheme.Modules.Complex.pullbackCompIso f g).hom.app (flatModel Z K)) ≫
      DerivedCategory.Q.map
        ((AlgebraicGeometry.Scheme.Modules.Complex.pullback g ⋙
          AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map (flatModelMap s))
  rw [resolvedPullbackFunctor_map]
  exact (Functor.map_comp DerivedCategory.Q _ _).symm.trans
    ((congrArg DerivedCategory.Q.map
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullbackCompIso f g).hom.naturality
        (flatModelMap s))).trans
        (Functor.map_comp DerivedCategory.Q _ _))

/-- A natural comparison between derived successive pullback and the actual composite.
The second replacement augmentation is invertible because the first pullback model is flat. -/
def resolvedPullbackCompIso : resolvedPullbackFunctorMinus (f ≫ g) ≅
    resolvedPullbackFunctorMinus g ⋙ derivedPullbackMinus f :=
  NatIso.ofComponents (fun K =>
    resolvedPullbackCompGeometric f g K ≪≫
      (resolvedFlatComparisonMinus f (pullbackFlatModelBounded g K)
        (pullbackFlatModelBounded_flat g K)).symm ≪≫
      ((derivedPullbackMinusFactors f).app (pullbackFlatModelBounded g K)).symm)
    (fun {K L} s => by
      dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.comp_map]
      simp only [Category.assoc]
      rw [resolvedPullbackCompGeometric_naturality_assoc,
        resolvedFlatComparisonMinus_inv_naturality_assoc f (pullbackFlatModelBoundedMap g s)
          (pullbackFlatModelBounded_flat g K) (pullbackFlatModelBounded_flat g L)]
      congr 2
      rw [resolvedPullbackFunctorMinus_map g]
      exact ((derivedPullbackMinusFactors f).inv.naturality (pullbackFlatModelBoundedMap g s)))

/-- Arbitrary ambient derived pullback has the actual contravariant composition comparison. -/
def derivedPullbackMinusCompIso :
    derivedPullbackMinus (f ≫ g) ≅ derivedPullbackMinus g ⋙ derivedPullbackMinus f :=
  Localization.liftNatIso (boundedAboveQMinus Z.Modules) (boundedAboveQuasiIso Z.Modules)
    (resolvedPullbackFunctorMinus (f ≫ g))
    (resolvedPullbackFunctorMinus g ⋙ derivedPullbackMinus f)
    (derivedPullbackMinus (f ≫ g)) (derivedPullbackMinus g ⋙ derivedPullbackMinus f)
    (resolvedPullbackCompIso f g)

end AlgebraicGeometry.Scheme.Modules
