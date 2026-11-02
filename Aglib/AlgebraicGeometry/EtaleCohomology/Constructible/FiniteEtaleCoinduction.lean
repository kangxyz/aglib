/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.CoinductionCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteDirectImageExact.LocalProduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.General

/-! # Actual finite-etale coinduction and its cokernel

Pointwise labelled splitting charts and the original finite-power comparison
construct a single finite local trivialization of actual coinduction. The
literal cokernel is finite locally constant by native finite-colimit closure.
The same annihilator is retained by additive functors and the original
cokernel projection. No trace or condition on the cover degree is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.EtaleCohomology.Fields
open AlgebraicGeometry.Scheme.EtaleCohomology.Fields.FiniteDirectImage

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge Fintype.ofFinite

/-- Original coinduction along every finite-etale morphism preserves finite
local constancy, using the actual point-indexed family of splitting charts. -/
theorem isFiniteLocallyConstant_finiteEtaleCoinduction
    {X S : Scheme.{u}} (p : S ⟶ X) [IsFinite p] [Etale p]
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsFiniteLocallyConstant F) :
    IsFiniteLocallyConstant ((directImage p).obj ((inverseImage p).obj F)) := by
  let Y : Scheme.FiniteEtale X := Scheme.FiniteEtale.mk p
  let B := (inverseImage p).obj F
  let C := (directImage p).obj B
  choose V A e v hv using exists_labelled_chart Y
  have ht (x : X) : IsFiniteLocallyConstant ((inverseImage (V x).hom).obj C) := by
    let c := fun a : A x => splitComponent Y (e x) a
    let G := fun a : A x => etaleRestriction (c a)
    let d : (etaleRestriction (V x).hom).obj C ≅
        ∏ᶜ fun a : A x => (etaleRestriction (c a)).obj B :=
      (localProductIso Y (e x)).app B ≪≫
        PreservesProduct.iso ((CategoryTheory.evaluation _ _).obj B) G
    exact (isFiniteLocallyConstant_iff_of_iso
      ((inverseImageEtaleIso (V x).hom).app C ≪≫ d)).mpr
        (isFiniteLocallyConstant_splitCoinduction p (V x).hom (A x) c
          (splitComponent_w Y (e x)) F hF)
  let t := fun x => Classical.choice (ht x)
  refine ⟨{
    index := Σ x : X, (t x).index
    chart := fun i => Scheme.Etale.mk (((t i.1).chart i.2).hom ≫ (V i.1).hom)
    covers := ?_
    value := fun i => (t i.1).value i.2
    finite_value := fun i => (t i.1).finite_value i.2
    trivialization := fun i =>
      (inverseImageComp (V i.1).hom ((t i.1).chart i.2).hom).app C ≪≫
        (t i.1).trivialization i.2 }⟩
  intro x
  obtain ⟨i, z, hz⟩ := (t x).covers (v x)
  refine ⟨⟨x, i⟩, z, ?_⟩
  change (V x).hom (((t x).chart i).hom z) = x
  rw [hz, hv]

/-- The literal cokernel of a morphism of finite local systems is finite
locally constant on an arbitrary scheme. -/
theorem isFiniteLocallyConstant_cokernel
    {X : Scheme.{u}} {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G)
    (hF : IsFiniteLocallyConstant F) (hG : IsFiniteLocallyConstant G) :
    IsFiniteLocallyConstant (cokernel a) := by
  apply FiniteColimits.isFiniteLocallyConstant_of_isColimit
    (parallelPair a 0) (cokernelIsCokernel a)
  intro j
  cases j
  · exact hF
  · exact hG

/-- Additive direct image retains the original annihilator. -/
theorem killedBy_directImage {X S : Scheme.{u}} (p : S ⟶ X)
    {F : AbelianSheaf.{u, u + 1} S} {n : ℕ} (hF : KilledBy n F) :
    KilledBy n ((directImage p).obj F) := by
  have h := congrArg (fun a : F ⟶ F => (directImage p).map a) hF
  simpa [KilledBy] using h

/-- The original cokernel projection transports any annihilator of its source. -/
theorem killedBy_cokernel {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) {n : ℕ}
    (hG : KilledBy n G) : KilledBy n (cokernel a) := by
  apply (cancel_epi (cokernel.π a)).mp
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  have h := congrArg (fun b : G ⟶ G => b ≫ cokernel.π a) hG
  simpa [KilledBy] using h

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
