/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteProducts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteCokernelGeneral
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction

/-! # Finite coefficients on a split coinduction chart

Every component of a split finite cover has the same composite to the base.
The original inverse-image composition identifies the resulting product of
restrictions with a finite power of the original base coefficient. This gives
finite local constancy on the chart and descent along its covering map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

attribute [local instance] hasSheafifyLarge Fintype.ofFinite

variable {X S T : Scheme.{u}} (p : S ⟶ X) (v : T ⟶ X)
  (I : Type u) [Finite I] (c : I → (T ⟶ S)) [∀ i, Etale (c i)]
  (hc : ∀ i, c i ≫ p = v) (F : AbelianSheaf.{u, u + 1} X)

/-- The original component restrictions of an inverse image identify with a
finite power of the same original inverse image on the splitting chart. -/
def splitCoinductionCoefficientIso :
    (∏ᶜ fun i : I => (etaleRestriction (c i)).obj ((inverseImage p).obj F)) ≅
      ∏ᶜ fun _ : I => (inverseImage v).obj F :=
  Pi.mapIso fun i =>
    ((inverseImageEtaleIso (c i)).app ((inverseImage p).obj F)).symm ≪≫
      ((inverseImageComp p (c i)).app F).symm ≪≫
        eqToIso (congrArg (fun f => (inverseImage f).obj F) (hc i))

include v hc

/-- A split coinduction chart has finite locally constant original coefficients
when the base coefficient is finite locally constant. -/
theorem isFiniteLocallyConstant_splitCoinduction
    (hF : IsFiniteLocallyConstant F) :
    IsFiniteLocallyConstant
      (∏ᶜ fun i : I => (etaleRestriction (c i)).obj ((inverseImage p).obj F)) :=
  (isFiniteLocallyConstant_iff_of_iso (splitCoinductionCoefficientIso p v I c hc F)).mpr
    (isFiniteLocallyConstant_finitePower I (isFiniteLocallyConstant_pullback v hF))

/-- A literal splitting-chart comparison proves finite local constancy of the
actual direct-image/inverse-image coefficient, by descent of the same charts. -/
theorem isFiniteLocallyConstant_directImage_inverseImage_of_split
    [Etale v] (hv : Function.Surjective v) (hF : IsFiniteLocallyConstant F)
    (e : (etaleRestriction v).obj ((directImage p).obj ((inverseImage p).obj F)) ≅
      ∏ᶜ fun i : I => (etaleRestriction (c i)).obj ((inverseImage p).obj F)) :
    IsFiniteLocallyConstant ((directImage p).obj ((inverseImage p).obj F)) := by
  apply isFiniteLocallyConstant_of_etale_pullback v hv
  exact (isFiniteLocallyConstant_iff_of_iso
    (((inverseImageEtaleIso v).app ((directImage p).obj ((inverseImage p).obj F))) ≪≫ e)).mpr
      (isFiniteLocallyConstant_splitCoinduction p v I c hc F hF)

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
