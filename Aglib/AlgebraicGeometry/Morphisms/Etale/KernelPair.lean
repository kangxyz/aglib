/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.GeometricPoints
public import Aglib.AlgebraicGeometry.Geometrically.Reduced.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The actual scheme kernel pair and fixed-extension-point detection

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.Classification`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 109–182.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.OverField
universe u
variable {F : Type u} [Field F] {X Y Z T : FScheme F}

/-- The literal scheme pullback of an actual morphism with itself, over F. -/
def kernelPair (f : X ⟶ Y) : FScheme F :=
  Over.mk (pullback.fst f.left f.left ≫ X.hom)

/-- The first projection from the actual scheme kernel pair. -/
def kernelPairFst (f : X ⟶ Y) : kernelPair f ⟶ X :=
  Over.homMk (pullback.fst f.left f.left) rfl

/-- The second projection from the actual scheme kernel pair. -/
def kernelPairSnd (f : X ⟶ Y) : kernelPair f ⟶ X :=
  Over.homMk (pullback.snd f.left f.left) (by
    change pullback.snd f.left f.left ≫ X.hom = pullback.fst f.left f.left ≫ X.hom
    have h := congrArg (fun m : pullback f.left f.left ⟶ Y.left => m ≫ Y.hom)
      (pullback.condition (f := f.left) (g := f.left)).symm
    simpa only [Category.assoc, Over.w] using h)

@[reassoc] theorem kernelPair_condition (f : X ⟶ Y) :
    kernelPairFst f ≫ f = kernelPairSnd f ≫ f := by
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- The universal kernel-pair map induced by two maps with equal composites. -/
def kernelPairLift (f : X ⟶ Y) (a b : T ⟶ X) (h : a ≫ f = b ≫ f) : T ⟶ kernelPair f :=
  Over.homMk (pullback.lift a.left b.left (congrArg (fun m => m.left) h)) (by
    change pullback.lift a.left b.left _ ≫ (pullback.fst f.left f.left ≫ X.hom) = T.hom
    rw [pullback.lift_fst_assoc, Over.w])

@[reassoc] theorem kernelPairLift_fst (f : X ⟶ Y) (a b : T ⟶ X) (h : a ≫ f = b ≫ f) :
    kernelPairLift f a b h ≫ kernelPairFst f = a := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[reassoc] theorem kernelPairLift_snd (f : X ⟶ Y) (a b : T ⟶ X) (h : a ≫ f = b ≫ f) :
    kernelPairLift f a b h ≫ kernelPairSnd f = b := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- The actual kernel pair of an etale map out of a smooth F-scheme is
geometrically reduced. Connectedness of the kernel pair is not asserted. -/
theorem kernelPair_geometricallyReduced (f : X ⟶ Y) [Etale f.left] [Smooth X.hom] :
    GeometricallyReduced (kernelPair f).hom := by
  let : Smooth (kernelPair f).hom := by
    dsimp [kernelPair]
    infer_instance
  exact Scheme.geometricallyReduced_of_smooth (kernelPair f).hom

/-- Equality on the specified actual algebraically closed extension proves
scheme equality of the two kernel-pair maps. -/
theorem kernelPair_comp_eq_of_extension_points {K : Type u} [Field K] [IsAlgClosed K] (α : F →+* K)
    (f : X ⟶ Y) [Etale f.left] [Smooth X.hom] (g : X ⟶ Z)
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (h : ∀ a b : extensionPointSource α ⟶ X,
      a ≫ f = b ≫ f → a ≫ g = b ≫ g) :
    kernelPairFst f ≫ g = kernelPairSnd f ≫ g := by
  let := kernelPair_geometricallyReduced f
  let : Smooth (kernelPair f).hom := by dsimp [kernelPair]; infer_instance
  apply hom_eq_of_extension_points α
  intro x
  have hc : (x ≫ kernelPairFst f) ≫ f = (x ≫ kernelPairSnd f) ≫ f := by
    rw [Category.assoc, Category.assoc, kernelPair_condition]
  simpa only [Category.assoc] using h (x ≫ kernelPairFst f) (x ≫ kernelPairSnd f) hc

/-- A proved scheme kernel-pair equality gives the actual all-test descent
cocycle, by its ordinary pullback universal property. -/
theorem all_test_cocycle_of_kernelPair (f : X ⟶ Y) (g : X ⟶ Z)
    (h : kernelPairFst f ≫ g = kernelPairSnd f ≫ g)
    (a b : T ⟶ X) (hab : a ≫ f = b ≫ f) : a ≫ g = b ≫ g := by
  have he := congrArg (fun m : kernelPair f ⟶ Z => kernelPairLift f a b hab ≫ m) h
  simpa only [kernelPairLift_fst_assoc, kernelPairLift_snd_assoc] using he


/-- The source kernel-pair carrier is literally the native scheme pullback. -/
@[simp] theorem kernelPair_left (f : X ⟶ Y) :
    (kernelPair f).left = pullback f.left f.left := rfl

end AlgebraicGeometry.Scheme.OverField
