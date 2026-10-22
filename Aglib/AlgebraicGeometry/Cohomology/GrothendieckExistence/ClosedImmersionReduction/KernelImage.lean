/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction

/-! # Transport from a closed immersion's kernel subscheme

Ideal-sheaf induction supplies effectivity on the subscheme defined by the
kernel of a composite closed immersion. The native image factorization
transports that conclusion to the original iterated closed subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (i : Y ⟶ X) [IsClosedImmersion i]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- Effectivity on the native kernel subscheme gives effectivity on the
original closed source, preserving its actual structure morphism. -/
theorem completionEssSurjOfKernelImage
    (h : let : IsLocallyNoetherian i.ker.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian i.ker.subschemeι
      (completionFunctor i.ker.subscheme
        (idealThickeningIdealSheaf (i.ker.subschemeι ≫ f) I)).EssSurj) :
    (completionFunctor Y (idealThickeningIdealSheaf (i ≫ f) I)).EssSurj := by
  let : IsLocallyNoetherian i.image :=
    LocallyOfFiniteType.isLocallyNoetherian i.imageι
  let : (completionFunctor i.image
      (idealThickeningIdealSheaf (i.imageι ≫ f) I)).EssSurj := h
  have he := completionFunctor_essSurj_of_closedImmersion I i.toImage (i.imageι ≫ f)
  have hh : i.toImage ≫ (i.imageι ≫ f) = i ≫ f :=
    (Category.assoc i.toImage i.imageι f).symm.trans
      (congrArg (fun g : Y ⟶ X => g ≫ f) i.toImage_imageι)
  exact hh ▸ he

end AlgebraicGeometry.Scheme.Cohomology
