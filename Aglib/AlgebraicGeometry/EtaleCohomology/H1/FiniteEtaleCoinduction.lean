/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ShortExactComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.GeometricallyConnected
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtaleCoinduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.LocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CohomologyPullback

/-! # Original H1 comparison descended from a finite-etale cover

The actual adjunction unit is monic, and its literal cokernel is finite
locally constant. Original H0 comparison and H1 injection for that cokernel,
canonical finite-direct-image comparison, and the native four lemma descend
surjectivity from the cover. No degree condition or trace splitting is used.
The cover H1-surjectivity input remains explicit: this formal construction
does not by itself assert geometric invariance on that cover.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wV wY wW

attribute [local instance] hasSheafifyLarge

/-- Actual finite-etale coinduction descends original H1 surjectivity along
flat quasi-compact geometrically connected base change. -/
theorem h1Pullback_surjective_of_finiteEtale_cover
    {X V Y W : Scheme.{u}}
    [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{wV} (AbelianSheaf.{u, u + 1} V)]
    [HasExt.{wY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{wW} (AbelianSheaf.{u, u + 1} W)]
    (p : V ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (p' : W ⟶ Y) (g : Y ⟶ X) (g' : W ⟶ V) (h : IsPullback g' p' p g)
    [Flat g] [QuasiCompact g] [GeometricallyConnected g]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F)
    (hV : Function.Surjective (h1Pullback g' ((inverseImage p).obj F))) :
    Function.Surjective (h1Pullback g F) := by
  let η := (inverseImageAdjunction p).unit.app F
  let : Mono η :=
    Constructible.FiniteCogenerators.mono_unit_of_finiteLocallyConstant p F hF
  let T := ShortComplex.mk η (cokernel.π η) (cokernel.condition η)
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel η }
  have hC : IsFiniteLocallyConstant (cokernel η) :=
    Constructible.isFiniteLocallyConstant_cokernel η hF
      (Constructible.isFiniteLocallyConstant_finiteEtaleCoinduction p hF)
  apply h1Pullback_surjective_of_shortExact g T hT
  · exact (h0Pullback_bijective_of_flat_quasiCompact_geometricallyConnected
      g (cokernel η) hC).surjective
  · exact (Finite.cohomologyPullback_directImage_surjective_iff
      p p' g g' h ((inverseImage p).obj F) 1).mpr hV
  · exact h1Pullback_injective_of_flat_quasiCompact_geometricallyConnected
      g (cokernel η) hC

end AlgebraicGeometry.Scheme.EtaleCohomology
