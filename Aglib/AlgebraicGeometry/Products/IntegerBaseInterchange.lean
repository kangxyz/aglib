/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Products.IntegerBase

/-!
# Interchange of independent products over the integer base

The actual nested pullbacks retain their three projections, original factor maps and
involutive swap. The full-category lift retains quasi-compactness of the fixed legs;
morphisms of the varying scheme remain unrestricted.

Source: archive Quillen/AlgebraicGeometry/Scheme/BaseProductInterchange.lean
SHA256: 7ec69cef161801f81533c1215b27e6b3aa885c09809f00068df9088897cf3f44
Selection: lines 25-231, independent-factor interchange and actual qc lift.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Products

variable {S T S' T' : AlgebraicGeometry.Scheme.{u}}

/-- The literal nested pullback map sends `((x,s),t)` to `((x,t),s)`. -/
def baseProductSwapMap (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductFunctor q).obj ((baseProductFunctor p).obj X) ⟶
      (baseProductFunctor p).obj ((baseProductFunctor q).obj X) :=
  pullback.lift
    (pullback.lift
      (pullback.fst (toIntegerBase ((baseProductFunctor p).obj X)) q ≫
        pullback.fst (toIntegerBase X) p)
      (pullback.snd (toIntegerBase ((baseProductFunctor p).obj X)) q)
      (specULiftZIsTerminal.hom_ext _ _))
    (pullback.fst (toIntegerBase ((baseProductFunctor p).obj X)) q ≫
      pullback.snd (toIntegerBase X) p)
    (specULiftZIsTerminal.hom_ext _ _)

/-- The shared original base coordinate is unchanged. -/
@[reassoc (attr := simp)]
theorem baseProductSwapMap_fst_fst (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫
        pullback.fst (toIntegerBase ((baseProductFunctor q).obj X)) p ≫
          pullback.fst (toIntegerBase X) q =
      pullback.fst (toIntegerBase ((baseProductFunctor p).obj X)) q ≫
        pullback.fst (toIntegerBase X) p := by
  simp [baseProductSwapMap]

/-- The original outer factor becomes the inner second coordinate. -/
@[reassoc (attr := simp)]
theorem baseProductSwapMap_fst_snd (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫
        pullback.fst (toIntegerBase ((baseProductFunctor q).obj X)) p ≫
          pullback.snd (toIntegerBase X) q =
      pullback.snd (toIntegerBase ((baseProductFunctor p).obj X)) q := by
  simp [baseProductSwapMap]

/-- The original inner second coordinate becomes the outer factor. -/
@[reassoc (attr := simp)]
theorem baseProductSwapMap_snd (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫
        pullback.snd (toIntegerBase ((baseProductFunctor q).obj X)) p =
      pullback.fst (toIntegerBase ((baseProductFunctor p).obj X)) q ≫
        pullback.snd (toIntegerBase X) p := by
  simp [baseProductSwapMap]

/-- Exchanging the same two original factors twice is the original identity map. -/
theorem baseProductSwapMap_comp (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫ baseProductSwapMap q p X = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [Category.assoc]
  · simp [Category.assoc]

/-- The swap commutes with every original base-scheme morphism. -/
@[reassoc]
theorem baseProductSwapMap_naturality (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    (baseProductFunctor q).map ((baseProductFunctor p).map f) ≫ baseProductSwapMap p q Y =
      baseProductSwapMap p q X ≫
        (baseProductFunctor p).map ((baseProductFunctor q).map f) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [baseProductSwapMap, baseProductFunctor, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, Category.assoc]

/-- The actual independent-factor interchange of the existing product functors. -/
def baseProductSwapIso (p : S ⟶ integerBase) (q : T ⟶ integerBase) :
    baseProductFunctor p ⋙ baseProductFunctor q ≅
      baseProductFunctor q ⋙ baseProductFunctor p :=
  NatIso.ofComponents (fun X =>
    { hom := baseProductSwapMap p q X
      inv := baseProductSwapMap q p X
      hom_inv_id := baseProductSwapMap_comp p q X
      inv_hom_id := baseProductSwapMap_comp q p X })
    (fun f => baseProductSwapMap_naturality p q f)

/-- The forward isomorphism component is exactly the original two-lift map. -/
@[simp]
theorem baseProductSwapIso_hom_app (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X = baseProductSwapMap p q X := rfl

/-- The chosen reverse component is the same literal swap with factors exchanged. -/
@[simp]
theorem baseProductSwapIso_inv_app (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).inv.app X = baseProductSwapMap q p X := rfl

/-- The actual natural isomorphisms are involutive without identifying their pullback objects. -/
theorem baseProductSwapIso_trans (p : S ⟶ integerBase) (q : T ⟶ integerBase) :
    baseProductSwapIso p q ≪≫ baseProductSwapIso q p = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact baseProductSwapMap_comp p q X

/-- Removing the final first factor retains the original map of the other product functor. -/
@[reassoc]
theorem baseProductSwapIso_projection_first (p : S ⟶ integerBase)
    (q : T ⟶ integerBase) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X ≫
        (baseProductProjection p).app ((baseProductFunctor q).obj X) =
      (baseProductFunctor q).map ((baseProductProjection p).app X) := by
  apply pullback.hom_ext <;>
    simp [baseProductSwapMap, baseProductProjection, baseProductFunctor]

/-- Removing the inner second factor retains the original outer projection. -/
@[reassoc]
theorem baseProductSwapIso_projection_second (p : S ⟶ integerBase)
    (q : T ⟶ integerBase) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X ≫
        (baseProductFunctor p).map ((baseProductProjection q).app X) =
      (baseProductProjection q).app ((baseProductFunctor p).obj X) := by
  apply pullback.hom_ext <;>
    simp [baseProductSwapMap, baseProductProjection, baseProductFunctor, Category.assoc]

/-- An actual morphism of the first fixed factor commutes with the whole swap. -/
@[reassoc]
theorem baseProductSwapIso_transformation_first (p : S ⟶ integerBase)
    (p' : S' ⟶ integerBase) (q : T ⟶ integerBase) (f : S ⟶ S')
    (hf : f ≫ p' = p) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductFunctor q).map ((baseProductTransformation p p' f hf).app X) ≫
        (baseProductSwapIso p' q).hom.app X =
      (baseProductSwapIso p q).hom.app X ≫
        (baseProductTransformation p p' f hf).app ((baseProductFunctor q).obj X) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]

/-- An independent actual morphism of the second factor commutes with the whole swap. -/
@[reassoc]
theorem baseProductSwapIso_transformation_second (p : S ⟶ integerBase)
    (q : T ⟶ integerBase) (q' : T' ⟶ integerBase) (g : T ⟶ T')
    (hg : g ≫ q' = q) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductTransformation q q' g hg).app ((baseProductFunctor p).obj X) ≫
        (baseProductSwapIso p q').hom.app X =
      (baseProductSwapIso p q).hom.app X ≫
        (baseProductFunctor p).map ((baseProductTransformation q q' g hg).app X) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]

/-- The same literal swap in the original full category of quasi-compact schemes. -/
def qcBaseProductSwapIso (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    [QuasiCompact p] [QuasiCompact q] :
    qcBaseProductFunctor p ⋙ qcBaseProductFunctor q ≅
      qcBaseProductFunctor q ⋙ qcBaseProductFunctor p :=
  NatIso.ofComponents
    (fun X => quasiCompactSchemeProperty.isoMk ((baseProductSwapIso p q).app X.obj))
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact (baseProductSwapIso p q).hom.naturality f.hom)

/-- No map is changed by lifting the original swap to quasi-compact schemes. -/
@[simp]
theorem qcBaseProductSwapIso_hom_hom (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    [QuasiCompact p] [QuasiCompact q] (X : QuasiCompactSchemes.{u}) :
    ((qcBaseProductSwapIso p q).hom.app X).hom = (baseProductSwapIso p q).hom.app X.obj := rfl

/-- The original first projection equation persists on the actual quasi-compact objects. -/
theorem qcBaseProductSwapIso_projection_first (p : S ⟶ integerBase)
    (q : T ⟶ integerBase) [QuasiCompact p] [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}) :
    ((qcBaseProductSwapIso p q).hom.app X).hom ≫
        (baseProductProjection p).app ((qcBaseProductFunctor q).obj X).obj =
      (baseProductFunctor q).map ((baseProductProjection p).app X.obj) :=
  baseProductSwapIso_projection_first p q X.obj

/-- The original second projection equation persists on the same quasi-compact objects. -/
theorem qcBaseProductSwapIso_projection_second (p : S ⟶ integerBase)
    (q : T ⟶ integerBase) [QuasiCompact p] [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}) :
    ((qcBaseProductSwapIso p q).hom.app X).hom ≫
        (baseProductFunctor p).map ((baseProductProjection q).app X.obj) =
      (baseProductProjection q).app ((qcBaseProductFunctor p).obj X).obj :=
  baseProductSwapIso_projection_second p q X.obj

/-- First-factor maps retain the original full-subcategory chart square. -/
@[reassoc]
theorem qcBaseProductSwapIso_transformation_first (p : S ⟶ integerBase)
    (p' : S' ⟶ integerBase) (q : T ⟶ integerBase)
    [QuasiCompact p] [QuasiCompact p'] [QuasiCompact q]
    (f : S ⟶ S') (hf : f ≫ p' = p) (X : QuasiCompactSchemes.{u}) :
    (qcBaseProductFunctor q).map ((qcBaseProductTransformation p p' f hf).app X) ≫
        (qcBaseProductSwapIso p' q).hom.app X =
      (qcBaseProductSwapIso p q).hom.app X ≫
        (qcBaseProductTransformation p p' f hf).app ((qcBaseProductFunctor q).obj X) := by
  apply ObjectProperty.hom_ext
  exact baseProductSwapIso_transformation_first p p' q f hf X.obj

/-- Second-factor maps retain their independent original full-subcategory square. -/
@[reassoc]
theorem qcBaseProductSwapIso_transformation_second (p : S ⟶ integerBase)
    (q : T ⟶ integerBase) (q' : T' ⟶ integerBase)
    [QuasiCompact p] [QuasiCompact q] [QuasiCompact q']
    (g : T ⟶ T') (hg : g ≫ q' = q) (X : QuasiCompactSchemes.{u}) :
    (qcBaseProductTransformation q q' g hg).app ((qcBaseProductFunctor p).obj X) ≫
        (qcBaseProductSwapIso p q').hom.app X =
      (qcBaseProductSwapIso p q).hom.app X ≫
        (qcBaseProductFunctor p).map ((qcBaseProductTransformation q q' g hg).app X) := by
  apply ObjectProperty.hom_ext
  exact baseProductSwapIso_transformation_second p q q' g hg X.obj

end AlgebraicGeometry.Scheme.Products
