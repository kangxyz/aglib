/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.QuasiCompactCategory
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/BaseProduct.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 117]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
Actual product functors over the integral terminal scheme. Their natural transformations retain
genuine pullback squares, open-immersion and flatness preservation; fixed quasi-compact legs give
endofunctors of the honest full category of qc schemes.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Products

/-- The actual integral terminal scheme, with the universe lift made explicit. -/
abbrev integerBase : AlgebraicGeometry.Scheme.{u} := Spec (.of (ULift.{u} ℤ))

/-- The unique structural morphism to the terminal integral scheme. -/
def toIntegerBase (X : AlgebraicGeometry.Scheme.{u}) : X ⟶ integerBase :=
  specULiftZIsTerminal.from X

@[reassoc (attr := simp)] lemma toIntegerBase_naturality
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    f ≫ toIntegerBase Y = toIntegerBase X := specULiftZIsTerminal.hom_ext _ _

/-- The genuine fiber product with a fixed scheme over the integral terminal scheme. -/
def baseProductFunctor {S : AlgebraicGeometry.Scheme.{u}} (p : S ⟶ integerBase) :
    AlgebraicGeometry.Scheme.{u} ⥤ AlgebraicGeometry.Scheme.{u} where
  obj X := pullback (toIntegerBase X) p
  map {X Y} f := pullback.map _ _ _ _ f (𝟙 S) (𝟙 integerBase)
    (by simp) (by simp)
  map_id X := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

/-- Its actual first projection, natural for every scheme map. -/
def baseProductProjection {S : AlgebraicGeometry.Scheme.{u}} (p : S ⟶ integerBase) :
    baseProductFunctor p ⟶ 𝟭 _ where
  app X := pullback.fst _ _
  naturality {X Y} f := by simp [baseProductFunctor]

/-- A genuine map over the integral base induces a natural map of these original products. -/
def baseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) (q : T ⟶ integerBase) (f : S ⟶ T) (hf : f ≫ q = p) :
    baseProductFunctor p ⟶ baseProductFunctor q where
  app X := pullback.map _ _ _ _ (𝟙 X) f (𝟙 integerBase) (by simp) (by simpa using hf.symm)
  naturality {X Y} g := by
    apply pullback.hom_ext <;> simp [baseProductFunctor]

@[reassoc (attr := simp)] lemma baseProductTransformation_projection
    {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) (q : T ⟶ integerBase) (f : S ⟶ T) (hf : f ≫ q = p)
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductTransformation p q f hf).app X ≫ (baseProductProjection q).app X =
      (baseProductProjection p).app X := by simp [baseProductTransformation,baseProductProjection]

/-- The actual product construction preserves quasi-compact objects when the fixed leg is qc. -/
def qcBaseProductFunctor {S : AlgebraicGeometry.Scheme.{u}} (p : S ⟶ integerBase) [QuasiCompact p] :
    QuasiCompactSchemes.{u} ⥤ QuasiCompactSchemes.{u} where
  obj X := ⟨(baseProductFunctor p).obj X.obj,by dsimp [baseProductFunctor]; infer_instance⟩
  map f := ⟨(baseProductFunctor p).map f.hom⟩
  map_id X := by apply ObjectProperty.hom_ext; exact (baseProductFunctor p).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (baseProductFunctor p).map_comp _ _

/-- The induced map in the honest full category of quasi-compact schemes. -/
def qcBaseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) (q : T ⟶ integerBase) [QuasiCompact p] [QuasiCompact q]
    (f : S ⟶ T) (hf : f ≫ q = p) :
    qcBaseProductFunctor p ⟶ qcBaseProductFunctor q where
  app X := ⟨(baseProductTransformation p q f hf).app X.obj⟩
  naturality {X Y} g := by
    apply ObjectProperty.hom_ext
    exact (baseProductTransformation p q f hf).naturality g.hom

/-- The displayed natural map is an actual base change of the original fixed-factor map. -/
lemma baseProductTransformation_isPullback {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) (q : T ⟶ integerBase) (f : S ⟶ T) (hf : f ≫ q = p)
    (X : AlgebraicGeometry.Scheme.{u}) :
    IsPullback ((baseProductTransformation p q f hf).app X)
      (pullback.snd (toIntegerBase X) p) (pullback.snd (toIntegerBase X) q) f := by
  apply IsPullback.of_right (h₁₂ := pullback.fst (toIntegerBase X) q) (h₂₂ := q)
  · simpa [baseProductTransformation,hf] using (IsPullback.of_hasPullback (toIntegerBase X) p)
  · simp [baseProductTransformation]
  · exact IsPullback.of_hasPullback (toIntegerBase X) q

instance instIsOpenImmersionBaseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) (q : T ⟶ integerBase) (f : S ⟶ T) (hf : f ≫ q = p)
    [IsOpenImmersion f] (X : AlgebraicGeometry.Scheme.{u}) :
    IsOpenImmersion ((baseProductTransformation p q f hf).app X) :=
  MorphismProperty.of_isPullback (baseProductTransformation_isPullback p q f hf X).flip
    inferInstance

instance instFlatBaseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) (q : T ⟶ integerBase) (f : S ⟶ T) (hf : f ≫ q = p)
    [Flat f] (X : AlgebraicGeometry.Scheme.{u}) :
    Flat ((baseProductTransformation p q f hf).app X) :=
  MorphismProperty.of_isPullback (baseProductTransformation_isPullback p q f hf X).flip
    inferInstance


end AlgebraicGeometry.Scheme.Products

end
