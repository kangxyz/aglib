/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.SchemeTorsorBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorTrivial
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.CoefficientRepresentation
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.SectionPullback
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.FiniteCoefficientPullback

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.FiniteEtaleRigidity` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`340e657cfa437aed17ebb60508f9d4ec60332d42bb870886b7963008a6a015c4`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1

/-!
# Finite-etale fullness and actual H1 detection

Single lower owner for the generic fullness, finite torsor, injectivity and
arithmetic inflation results accepted in the unsplit-origin investigation.
The six declarations are moved with unchanged statements and proof bodies
from the frozen Criterion source (SHA256
71ab8d2cf3e301a0e3bc16a22044b8a722fd92574621524d9116aa769a286bcb).
They use actual finite covers and cohomology, with the same explicit ordinary
03AJ/03RV inputs. There is no K-theory dependency or higher-result alias.
Source scope: auxiliary finite-coefficient foundations for
K2-018#prop:k2018-arithmetic-characters, mathematical revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982. This extraction does not realize
henselian fullness or close the remaining ordinary origin foundations.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.EtaleH1.PointedNaturality
namespace AlgebraicGeometry.Scheme.EtaleH1.FiniteEtaleRigidity
universe u wB wR

section SheafRigidity
variable {B S : Scheme.{u}} (p : S ⟶ B) (o : B ⟶ S) (ho : o ≫ p = 𝟙 B)
  [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)]
  [HasExt.{wR} (AbelianSheaf.{u, u + 1} S)]
  (T : AbelianSheaf.{u, u + 1} B)

/-- Closed-fibre injectivity alone, with the existing section retraction,
forces every class to be its arithmetic inflation. No trivial-action or
primitive-root premise occurs. For a henselian local spectrum and finite
locally constant coefficients, the injectivity is an ordinary missing input. -/
theorem inflation_section_of_injective
    (hrig : Function.Injective (sectionPullback p o ho T))
    (c : H1Etale S ((inverseImage p).obj T)) :
    h1Pullback p T (sectionPullback p o ho T c) = c := by
  apply hrig
  exact sectionPullback_inflation p o ho T _
end SheafRigidity


section FiniteEtaleRigidity
open Opposite
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange mk)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
variable {B S : Scheme.{u}} (f : B ⟶ S)
  [(baseChange f).Full]
  [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)]
  [HasExt.{wR} (AbelianSheaf.{u, u + 1} S)]
  (hAS : Stacks03AJ.{u, wR} S) (hRS : Stacks03RV S)
  (hAB : Stacks03AJ.{u, wB} B)
  (A : Grp (Over S)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
  (hA : IsFiniteLocallyConstant (representedSheaf A))

/-- A section after pullback lifts using only fullness of the ACTUAL finite
etale pullback functor. The source and target are actual finite covers. -/
def sectionOfFull (Y : Scheme.FiniteEtale S)
    (t : Over.mk (𝟙 B) ⟶ ((baseChange f).obj Y).obj) :
    Over.mk (𝟙 S) ⟶ Y.obj := by
  let U : Scheme.FiniteEtale S := Scheme.FiniteEtale.mk (𝟙 S)
  let ε : ((baseChange f).obj U).obj ⟶ Over.mk (𝟙 B) :=
    Over.homMk ((baseChange f).obj U).obj.hom (by simp)
  let k : (baseChange f).obj U ⟶ (baseChange f).obj Y := ⟨ε ≫ t⟩
  exact ((baseChange f).preimage k).hom

include hAS hRS hAB hA in
/-- Finite etale fullness detects zero in actual H1 for a represented finite
coefficient group. Proof: represent the torsor, lift its closed-fibre section,
and use the already constructed torsor-to-Ext class. No H1 square is assumed. -/
theorem h1Pullback_eq_zero_of_full
    (c : H1Etale S (representedSheaf A))
    (hc : h1Pullback f (representedSheaf A) c = 0) : c = 0 := by
  obtain ⟨p, rfl⟩ := (hAS.bijective (representedSheaf A)).surjective c
  revert hc
  refine Quotient.inductionOn p ?_
  intro P hP
  change h1Pullback f (representedSheaf A) (torsorExtClass P) = 0 at hP
  let Y := P.finiteEtaleRepresentative hRS hA
  let e := P.finiteEtaleRepresentativeIso hRS hA
  let τ := P.representedSchemeAction A Y e
  let : Surjective Y.obj.hom := P.represented_surjective A Y e
  have heq : torsorExtClass (torsorOfSchemeAction A Y τ) = torsorExtClass P :=
    torsorExtClass_iso (P.representedSchemeActionIso A Y e)
  have hz : torsorExtClass
      (torsorOfSchemeAction (baseChangedGroup f A) ((baseChange f).obj Y)
        (Scheme.EtaleH1.SchemeTorsorBaseChange.pullbackSchemeAction f
            A Y τ)) = 0 := by
    rw [← Scheme.EtaleH1.SchemeTorsorBaseChange.torsorExtClass_pullbackSchemeAction f A Y τ,
      heq, hP, map_zero]
  obtain ⟨t⟩ := (torsorExtClass_eq_zero_iff_globalSection _ hAB).mp hz
  let s : Over.mk (𝟙 S) ⟶ Y.obj := sectionOfFull f Y t.down
  exact torsorExtClass_eq_zero_of_section P (e.hom.hom.app (op (etaleTerminal S)) (ULift.up s))

include hAS hRS hAB hA in
/-- The finite-coefficient H1 pullback is injective under the same ordinary
categorical premise; no action trivialization or primitive root is needed. -/
theorem h1Pullback_injective_of_full :
    Function.Injective (h1Pullback f (representedSheaf A)) := by
  intro a b h
  apply sub_eq_zero.mp
  apply h1Pullback_eq_zero_of_full f hAS hRS hAB A hA
  rw [map_sub, h, sub_self]
end FiniteEtaleRigidity

section ArbitraryFiniteRigidity
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
variable {B S : Scheme.{u}} (f : B ⟶ S)
    [(Scheme.FiniteEtale.baseChange f).Full]
  [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)]
  [HasExt.{wR} (AbelianSheaf.{u, u + 1} S)]
  (hAS : Stacks03AJ.{u, wR} S) (hRS : Stacks03RV S)
  (hAB : Stacks03AJ.{u, wB} B)

include hAS hRS hAB in
/-- Ordinary finite-etale fullness gives injectivity for every actual finite
locally constant abelian sheaf. Its group-scheme representative is constructed
from the existing 03RV input, and no trivialization of the Galois action occurs. -/
theorem h1Pullback_injective_finite_of_full
    (T : AbelianSheaf.{u, u + 1} S) (hT : IsFiniteLocallyConstant T) :
    Function.Injective (h1Pullback f T) := by
  let R :=
      Scheme.EtaleH1.CoefficientRepresentation.ofFiniteLocallyConstant
      T hRS hT
  have hA : IsFiniteLocallyConstant (representedSheaf R.group) :=
    (isFiniteLocallyConstant_iff_of_iso R.iso).mpr hT
  intro a b h
  apply (coefficientIso R.iso.symm).injective
  apply h1Pullback_injective_of_full f hAS hRS hAB R.group hA
  change h1Pullback f (representedSheaf R.group) (coefficientMap R.iso.inv a) =
    h1Pullback f (representedSheaf R.group) (coefficientMap R.iso.inv b)
  rw [h1Pullback_coefficientMap, h1Pullback_coefficientMap, h]
end ArbitraryFiniteRigidity

section ClosedFiniteRigidity
variable {B S : Scheme.{u}} (p : S ⟶ B) (o : B ⟶ S) (ho : o ≫ p = 𝟙 B)
  [(Scheme.FiniteEtale.baseChange o).Full]
  [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)]
  [HasExt.{wR} (AbelianSheaf.{u, u + 1} S)]
  (hAS : Stacks03AJ.{u, wR} S) (hRS : Stacks03RV S)
  (hAB : Stacks03AJ.{u, wB} B)

include hAS hRS hAB in
/-- For finite coefficients pulled from the residue field, actual finite-etale
fullness and the actual section imply the complete arithmetic inflation law.
This includes the tensor-square root sheaf with its unsplit cyclotomic action. -/
theorem inflation_section_of_full (T : AbelianSheaf.{u, u + 1} B)
    (hT : IsFiniteLocallyConstant T)
    (c : H1Etale S ((inverseImage p).obj T)) :
    h1Pullback p T (sectionPullback p o ho T c) = c := by
  apply h1Pullback_injective_finite_of_full o hAS hRS hAB
    ((inverseImage p).obj T) (isFiniteLocallyConstant_pullback p hT)
  apply (coefficientIso (sectionCoefficientIso p o ho T)).injective
  exact sectionPullback_inflation p o ho T _
end ClosedFiniteRigidity


end AlgebraicGeometry.Scheme.EtaleH1.FiniteEtaleRigidity
