/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.GenericModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Spectrum
public import Aglib.CategoryTheory.Adjunction.MonicProducts

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
    Mono (globalModelProduct t m) := by
  let N (i : t.index) := (m i).source
  let f (i : t.index) := (m i).morphism
  let k (i : t.index) := (N i).fromSpecStalk (genericPoint (N i)) ≫ f i
  let M (i : t.index) :=
    ConstantFinite.coefficient (m i).value (Spec (N i).functionField)
  let v (i : t.index) : globalModelTargets t m i ⟶ (directImage (k i)).obj (M i) :=
    (directImage (f i)).map
      (NormalConstants.constantGenericIso (N i) (ConstantFinite.value (m i).value)).hom ≫
      (directImageCompIso (f i) ((N i).fromSpecStalk (genericPoint (N i)))).hom.app (M i)
  have hL (G : AbelianSheaf.{u, u + 1} X) (a b : G ⟶ F)
      (h : ∀ i, (inverseImage (k i)).map a = (inverseImage (k i)).map b) : a = b := by
    apply t.fieldPoint_inverseImages_map_injective
      (fun i => (m i).source.functionField) (fun i => (m i).point) G
    funext i
    change (inverseImage ((m i).point ≫ t.inclusion i)).map a =
      (inverseImage ((m i).point ≫ t.inclusion i)).map b
    rw [(m i).over]
    exact h i
  exact Adjunction.mono_lift_of_monic_adjunct_factors
    (fun i => inverseImageAdjunction (k i)) F hL M (fun i => (m i).trivialization.hom)
    (fun i => (m i).extensionMap) v (fun i => (m i).extensionMap_comp)


end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
