/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.FiniteEtaleRigidity

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.PullbackSquare` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`59e1cf47df4cbb6a996fe566803c7b3acf068e5eda3e20d39919bfecd6cc5a8d`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1

/-!
# Actual H1 congruence across scheme pullback squares

The two closed-fibre congruence proofs use only the existing inverse-image
composition/transport and section laws, together with lower finite-etale H1
rigidity. No triangleIso is added, copied, or aliased. The generic square proof
moves its accepted direct PullbackComposition/SectionPullback derivation.
The statements preserve all assumptions of the frozen unsplit sources.
Auxiliary source scope: K2-018#prop:k2018-arithmetic-characters,
e73d98b1b5c1e5abcdebf7d058e436d792b87982. There is no K-theory import.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.EtaleH1.PointedNaturality
namespace AlgebraicGeometry.Scheme.EtaleH1.PullbackSquare
open FiniteEtaleRigidity
universe u wB wK wR wS wL

section ClosedSquare
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
variable {B R S : Scheme.{u}} (uS : S ⟶ R) (oS : B ⟶ S) (oR : B ⟶ R)
  (hc : oS ≫ uS = oR) [(baseChange oS).Full]
  [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)]
  [HasExt.{wR} (AbelianSheaf.{u, u + 1} R)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]
  (hAS : Stacks03AJ.{u, wS} S) (hRS : Stacks03RV S)
  (hAB : Stacks03AJ.{u, wB} B)

include hc hAS hRS hAB in
/-- Closed-fibre equality is detected after the actual extension by fullness.
The composition and equality transports are the existing native ones. -/
theorem pullback_eq_of_closed_eq (T : AbelianSheaf.{u, u + 1} R)
    (hT : IsFiniteLocallyConstant T) (c d : H1Etale R T)
    (hcd : h1Pullback oR T c = h1Pullback oR T d) :
    h1Pullback uS T c = h1Pullback uS T d := by
  apply h1Pullback_injective_finite_of_full oS hAS hRS hAB
    ((inverseImage uS).obj T) (isFiniteLocallyConstant_pullback uS hT)
  have hcomp : h1Pullback (oS ≫ uS) T c = h1Pullback (oS ≫ uS) T d := by
    let e : (inverseImage (oS ≫ uS)).obj T ≅ (inverseImage oR).obj T :=
      eqToIso (congrArg (fun a : B ⟶ R => (inverseImage a).obj T) hc)
    apply (coefficientIso e).injective
    change coefficientMap (eqToIso (congrArg (fun a : B ⟶ R => (inverseImage a).obj T) hc)).hom
      (h1Pullback (oS ≫ uS) T c) =
      coefficientMap (eqToIso (congrArg (fun a : B ⟶ R => (inverseImage a).obj T) hc)).hom
        (h1Pullback (oS ≫ uS) T d)
    rw [h1Pullback_eq_transport hc T c, h1Pullback_eq_transport hc T d]
    exact hcd
  rw [← h1Pullback_comp, ← h1Pullback_comp, hcomp]
end ClosedSquare

section PullbackArithmeticFactorization
variable {B R S : Scheme.{u}} (p : R ⟶ B) (o : B ⟶ R) (ho : o ≫ p = 𝟙 B)
  (uS : S ⟶ R) (oS : B ⟶ S) (hc : oS ≫ uS = o)
  [(Scheme.FiniteEtale.baseChange oS).Full]
  [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)]
  [HasExt.{wK} (AbelianSheaf.{u, u + 1} R)]
  [HasExt.{wR} (AbelianSheaf.{u, u + 1} S)]
  (hAS : Stacks03AJ.{u, wR} S) (hRS : Stacks03RV S)
  (hAB : Stacks03AJ.{u, wB} B)

include hc hAS hRS hAB in
/-- After extension with full closed-fibre pullback, a finite-coefficient class
is the pullback of its arithmetic inflation. This uses the existing section
retraction and the lower closed-square congruence, without higher triangles. -/
theorem pullback_eq_arithmetic_of_full (T : AbelianSheaf.{u, u + 1} B)
    (hT : IsFiniteLocallyConstant T)
    (c : H1Etale R ((inverseImage p).obj T)) :
    h1Pullback uS ((inverseImage p).obj T) c =
    h1Pullback uS ((inverseImage p).obj T)
      (h1Pullback p T (sectionPullback p o ho T c)) := by
  apply pullback_eq_of_closed_eq uS oS o hc hAS hRS hAB
    ((inverseImage p).obj T) (isFiniteLocallyConstant_pullback p hT)
  apply (coefficientIso (sectionCoefficientIso p o ho T)).injective
  exact (sectionPullback_inflation p o ho T _).symm
end PullbackArithmeticFactorization

section GenericSquare
variable {R S K L : Scheme.{u}}
  [HasExt.{wR} (AbelianSheaf.{u, u + 1} R)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{wK} (AbelianSheaf.{u, u + 1} K)]
  [HasExt.{wL} (AbelianSheaf.{u, u + 1} L)]
  (uS : S ⟶ R) (gS : L ⟶ S) (gK : K ⟶ R) (k : L ⟶ K)
  (hs : gS ≫ uS = k ≫ gK)

include hs in
/-- Pullback equality transports across the actual generic scheme square. -/
theorem iterated_pullback_eq_of_square (T : AbelianSheaf.{u, u + 1} R)
    (c d : H1Etale R T) (hcd : h1Pullback uS T c = h1Pullback uS T d) :
    h1Pullback k ((inverseImage gK).obj T) (h1Pullback gK T c) =
      h1Pullback k ((inverseImage gK).obj T) (h1Pullback gK T d) := by
  have h1 : h1Pullback (gS ≫ uS) T c = h1Pullback (gS ≫ uS) T d := by
    apply (coefficientIso ((inverseImageComp uS gS).app T)).injective
    change coefficientMap ((inverseImageComp uS gS).hom.app T) _ =
      coefficientMap ((inverseImageComp uS gS).hom.app T) _
    rw [h1Pullback_comp, h1Pullback_comp, hcd]
  have h2 : h1Pullback (k ≫ gK) T c = h1Pullback (k ≫ gK) T d := by
    let e : (inverseImage (gS ≫ uS)).obj T ≅ (inverseImage (k ≫ gK)).obj T :=
      eqToIso (congrArg (fun a : L ⟶ R => (inverseImage a).obj T) hs)
    have ht := congrArg (coefficientMap.{u, u + 1, wL} e.hom) h1
    exact (h1Pullback_eq_transport hs T c).symm.trans
      (ht.trans (h1Pullback_eq_transport hs T d))
  rw [← h1Pullback_comp, ← h1Pullback_comp, h2]
end GenericSquare


end AlgebraicGeometry.Scheme.EtaleH1.PullbackSquare
