/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.KummerAffineFieldExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.GeometricallyConnected
public import Aglib.AlgebraicGeometry.Stalk.OpenSmoothCurveDVR
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality

/-! # Original Kummer field invariance for nonempty opens of proper curves

The existing smooth proper geometrically connected curve properties and a
nonempty actual open immersion supply all geometry required by the complete
boundary construction. Original H1 injectivity follows from actual
geometrically connected finite-etale descent. Thus the unchanged roots H1 map
along the literal field-extension projection is bijective at positive
invertible level, for algebraically closed source and target fields.
The standard Ext universe is explicitly retained. No affine-unit roots,
normality premise, boundary model, or genus condition is added.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerOpenFieldExtension

attribute [local instance] hasSheafifyLarge HasExt.standard

private theorem noetherian_open {T Z : Scheme.{u}} [IsNoetherian T]
    (i : Z ⟶ T) [IsOpenImmersion i] : IsNoetherian Z := by
  let : IsLocallyNoetherian Z := isLocallyNoetherian_of_isOpenImmersion i
  let : NoetherianSpace Z := i.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  exact ⟨⟩

private theorem closedDVR {F : Type u} [Field F] {T : Scheme.{u}} [IsIntegral T]
    (p : T ⟶ Spec (.of F)) [SmoothOfRelativeDimension 1 p] (x : ClosedPoint T) :
    IsDiscreteValuationRing (T.presheaf.stalk x.val) := by
  let : SmoothOfRelativeDimension 1 (𝟙 T ≫ p) := by
    simpa only [Category.id_comp] using (inferInstance : SmoothOfRelativeDimension 1 p)
  exact Scheme.smoothChart_closedPoint_dvr (𝟙 T) p x.val x.property

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
  (X : FScheme k) (hX : Properties X)
  {U : Scheme.{u}} [Nonempty U] (j : U ⟶ X.left) [IsOpenImmersion j]
  (n : ℕ) (hn : 0 < n) (hk : IsUnit (n : Γ(Spec (.of k), ⊤)))

include hX in
/-- The original roots H1 map is surjective on a nonempty actual open of the
specified smooth proper curve; all geometric guards are supplied internally. -/
theorem h1Map_surjective :
    Function.Surjective (h1Map.{u, u + 2, u + 2}
      (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) n hn
      (levelInvertible j n (levelInvertible X.hom n hk))) := by
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let : IsProper X.hom := hX.proper
  let : IsIntegral X.left :=
    curveProperties_isIntegral Scheme.smoothFieldNormality Scheme.normalComponentsOpen hX
  let : IsNoetherian X.left := curveProperties_isNoetherian hX
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let : ∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    closedDVR X.hom
  let Y : FScheme K := Over.mk (pullback.snd X.hom (Spec.algebraMap k K))
  have hY : Properties Y := curveProperties_baseChange hX K (Spec.algebraMap k K)
  let : SmoothOfRelativeDimension 1 Y.hom := hY.smooth
  let : IsIntegral Y.left :=
    curveProperties_isIntegral Scheme.smoothFieldNormality Scheme.normalComponentsOpen hY
  let : IsNoetherian Y.left := curveProperties_isNoetherian hY
  let : LocallyOfFiniteType Y.hom := curveProperties_locallyOfFiniteType hY
  let : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  let : ∀ y : ClosedPoint Y.left, IsDiscreteValuationRing (Y.left.presheaf.stalk y.val) :=
    closedDVR Y.hom
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsNoetherian U := noetherian_open j
  let : SmoothOfRelativeDimension 1 (j ≫ X.hom) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (j ≫ X.hom))
  let : ∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val) :=
    closedDVR (j ≫ X.hom)
  let Z : Scheme.{u} := pullback (j ≫ X.hom) (Spec.algebraMap k K)
  let jK : Z ⟶ Y.left := Hom.fibreInclusion X.hom j (Spec.algebraMap k K)
  have H := Hom.fibreInclusion_isPullback X.hom j (Spec.algebraMap k K)
  let : IsOpenImmersion jK := MorphismProperty.of_isPullback H inferInstance
  let : Surjective (Spec.algebraMap k K) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  let : Surjective (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) := inferInstance
  let : Nonempty Z := by
    obtain ⟨z, _⟩ := (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)).surjective
      (Classical.choice (inferInstance : Nonempty U))
    exact ⟨z⟩
  let : IsIntegral Z := isIntegral_of_isOpenImmersion jK
  let : IsNoetherian Z := noetherian_open jK
  let : SmoothOfRelativeDimension 1 (pullback.snd (j ≫ X.hom) (Spec.algebraMap k K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback (j ≫ X.hom) (Spec.algebraMap k K))
      (inferInstance : SmoothOfRelativeDimension 1 (j ≫ X.hom))
  let : ∀ z : ClosedPoint Z, IsDiscreteValuationRing (Z.presheaf.stalk z.val) :=
    closedDVR (pullback.snd (j ≫ X.hom) (Spec.algebraMap k K))
  let : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z) := fun z =>
    (Scheme.smoothFieldNormality K Z
      (pullback.snd (j ≫ X.hom) (Spec.algebraMap k K))
      (SmoothOfRelativeDimension.smooth 1 _) z).2
  let : IsIntegral (pullback X.hom (Spec.algebraMap k K)) :=
    inferInstanceAs (IsIntegral Y.left)
  let : IsNoetherian (pullback X.hom (Spec.algebraMap k K)) :=
    inferInstanceAs (IsNoetherian Y.left)
  let : JacobsonSpace (pullback X.hom (Spec.algebraMap k K) : Scheme.{u}) :=
    inferInstanceAs (JacobsonSpace Y.left)
  let : ∀ y : ClosedPoint (pullback X.hom (Spec.algebraMap k K)),
      IsDiscreteValuationRing
        ((pullback X.hom (Spec.algebraMap k K)).presheaf.stalk y.val) :=
    inferInstanceAs (∀ y : ClosedPoint Y.left,
      IsDiscreteValuationRing (Y.left.presheaf.stalk y.val))
  let : IsIntegral (pullback (j ≫ X.hom) (Spec.algebraMap k K)) :=
    inferInstanceAs (IsIntegral Z)
  let : IsNoetherian (pullback (j ≫ X.hom) (Spec.algebraMap k K)) :=
    inferInstanceAs (IsNoetherian Z)
  let : ∀ z : ClosedPoint (pullback (j ≫ X.hom) (Spec.algebraMap k K)),
      IsDiscreteValuationRing
        ((pullback (j ≫ X.hom) (Spec.algebraMap k K)).presheaf.stalk z.val) :=
    inferInstanceAs (∀ z : ClosedPoint Z, IsDiscreteValuationRing (Z.presheaf.stalk z.val))
  let : ∀ z : (pullback (j ≫ X.hom) (Spec.algebraMap k K) : Scheme),
      IsIntegrallyClosed
        ((pullback (j ≫ X.hom) (Spec.algebraMap k K)).presheaf.stalk z) :=
    inferInstanceAs (∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
  exact KummerAffineFieldExtension.h1Map_surjective_open_fieldExtension k K X j
    (Scheme.smoothFieldNormality k X.left X.hom (curveProperties_smooth hX))
    (curveProperties_dimension Scheme.smoothFieldDimension hX)
    (curveProperties_dimension Scheme.smoothFieldDimension hY).le n hn hk

include hX in
/-- The unchanged roots-coefficient H1 pullback is bijective on every such
nonempty open, in the original standard Ext realization. -/
theorem h1Map_bijective :
    Function.Bijective (h1Map.{u, u + 2, u + 2}
      (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) n hn
      (levelInvertible j n (levelInvertible X.hom n hk))) := by
  let : IsIntegral X.left :=
    curveProperties_isIntegral Scheme.smoothFieldNormality Scheme.normalComponentsOpen hX
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let hi := levelInvertible j n (levelInvertible X.hom n hk)
  refine ⟨?_, h1Map_surjective k K X hX j n hn hk⟩
  exact (coefficientIso (rootsPullbackIso
    (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) n hn hi)).injective.comp
      (h1Pullback_injective_fieldExtension k K (j ≫ X.hom) (mu U n)
        (GroupCohomology.Kummer.mu_isFiniteLocallyConstant U n hn hi))

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerOpenFieldExtension
