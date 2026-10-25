/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.GenericModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Spectrum

/-! # Original dominant generic points detect the global model product

The actual normal-model extension maps retain their original generic
adjoints. Dominant field points of the original integral covering strata
therefore prove that their literal finite product is monic. The models can
still be infinite over the base; the finite-target factorization is separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} {F : AbelianSheaf.{u, u + 1} X}

/-- The actual direct-image targets of the given normal models. -/
def globalModelTargets (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ i, GlobalNormalGenericModel (t.inclusion i) F) :
    t.index → AbelianSheaf.{u, u + 1} X :=
  fun i => (directImage ((m i).morphism)).obj
    (ConstantFinite.coefficient (m i).value ((m i).source))

/-- The literal product of the original normal-model extension maps. -/
def globalModelProduct (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ i, GlobalNormalGenericModel (t.inclusion i) F) :
    F ⟶ ∏ᶜ globalModelTargets t m :=
  Pi.lift (f := globalModelTargets t m) fun i => (m i).extensionMap

/-- Each original product coordinate is the supplied normal-model extension. -/
@[reassoc]
theorem globalModelProduct_π (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ i, GlobalNormalGenericModel (t.inclusion i) F) (i : t.index) :
    globalModelProduct t m ≫ Pi.π (globalModelTargets t m) i = (m i).extensionMap :=
  Pi.lift_comp_π (f := globalModelTargets t m) (fun i => (m i).extensionMap) i

/-- The actual dominant generic points of the covering strata detect the
original maps, so the original normal-model product is monic. -/
theorem mono_globalModelProduct (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ i, GlobalNormalGenericModel (t.inclusion i) F) :
    Mono (globalModelProduct t m) where
  right_cancellation {G} a b hab := by
    apply t.fieldPoint_inverseImages_map_injective
      (fun i => (m i).source.functionField) (fun i => (m i).point) G
    funext i
    change (inverseImage ((m i).point ≫ t.inclusion i)).map a =
      (inverseImage ((m i).point ≫ t.inclusion i)).map b
    rw [(m i).over]
    apply (cancel_mono (m i).trivialization.hom).mp
    apply ((inverseImageAdjunction
      (((m i).source).fromSpecStalk
        (genericPoint ((m i).source)) ≫
          (m i).morphism)).homEquiv G _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
    let π := Pi.π (globalModelTargets t m) i
    have hp : globalModelProduct t m ≫ π = (m i).extensionMap :=
      globalModelProduct_π t m i
    have hcoord : a ≫ (m i).extensionMap = b ≫ (m i).extensionMap := by
      have hproj : a ≫ (globalModelProduct t m ≫ π) = b ≫ (globalModelProduct t m ≫ π) :=
        (Category.assoc a (globalModelProduct t m) π).symm.trans
          ((congrArg (fun k => k ≫ π) hab).trans
            (Category.assoc b (globalModelProduct t m) π))
      exact (congrArg (fun k => a ≫ k) hp.symm).trans
        (hproj.trans (congrArg (fun k => b ≫ k) hp))
    let N := (m i).source
    let f := (m i).morphism
    let v := (directImage f).map
      (NormalConstants.constantGenericIso N (ConstantFinite.value (m i).value)).hom ≫
      (directImageCompIso f (N.fromSpecStalk (genericPoint N))).hom.app
        (ConstantFinite.coefficient (m i).value (Spec N.functionField))
    have hfac : (m i).extensionMap ≫ v =
        (inverseImageAdjunction (N.fromSpecStalk (genericPoint N) ≫ f)).homEquiv F _
          (m i).trivialization.hom := (m i).extensionMap_comp
    exact (congrArg (fun k => a ≫ k) hfac.symm).trans
      ((Category.assoc a (m i).extensionMap v).symm.trans
        ((congrArg (fun k => k ≫ v) hcoord).trans
          ((Category.assoc b (m i).extensionMap v).trans
            (congrArg (fun k => b ≫ k) hfac))))


end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
