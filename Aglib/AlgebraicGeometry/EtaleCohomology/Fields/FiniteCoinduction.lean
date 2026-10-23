/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.CoinductionCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteDirectImageExact.LocalProduct

/-! # Actual finite coinduction preserves finite field coefficients

An actual finite-etale cover of a field splits on an etale chart containing
a point, hence on a surjective chart. The original local-product comparison
identifies coinduction of inverse image with a finite power on that chart.
This proves finite local constancy of the actual direct-image coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

open Scheme.FiniteEtale Scheme.FiniteEtale.FieldGalois.Arbitrary
open FiniteDirectImage

attribute [local instance] hasSheafifyLarge Fintype.ofFinite

/-- Original finite-etale coinduction of inverse image preserves finite local
constancy over a field, including empty or disconnected finite covers. -/
theorem isFiniteLocallyConstant_finiteEtaleCoinduction
    (K : Type u) [Field K] (Y : Scheme.FiniteEtale (Spec (.of K)))
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K))) (hF : IsFiniteLocallyConstant F) :
    IsFiniteLocallyConstant ((directImage Y.obj.hom).obj ((inverseImage Y.obj.hom).obj F)) := by
  obtain ⟨V, A, e, v, _⟩ := exists_labelled_chart Y (default : Spec (.of K))
  let c := fun a : A => splitComponent Y e a
  let G := fun a : A => etaleRestriction (c a)
  let B := (inverseImage Y.obj.hom).obj F
  let d : (etaleRestriction V.hom).obj ((directImage Y.obj.hom).obj B) ≅
      ∏ᶜ fun a : A => (etaleRestriction (c a)).obj B :=
    (localProductIso Y e).app B ≪≫
      PreservesProduct.iso ((CategoryTheory.evaluation _ _).obj B) G
  exact isFiniteLocallyConstant_directImage_inverseImage_of_split Y.obj.hom V.hom A c
    (splitComponent_w Y e) F (fun x => ⟨v, Subsingleton.elim _ _⟩) hF d

/-- For a finite separable extension, the original direct image of inverse
image is an actual finite locally constant coefficient on the base field. -/
theorem isFiniteLocallyConstant_finiteFieldCoinduction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K))) (hF : IsFiniteLocallyConstant F) :
    IsFiniteLocallyConstant
      ((directImage (Spec.algebraMap K L)).obj ((inverseImage (Spec.algebraMap K L)).obj F)) :=
  isFiniteLocallyConstant_finiteEtaleCoinduction K (finiteFieldCover K L) F hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
