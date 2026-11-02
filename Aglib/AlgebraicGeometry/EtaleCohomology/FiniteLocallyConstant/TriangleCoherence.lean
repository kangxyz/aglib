/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SheafCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.FieldNaturality
public import Aglib.AlgebraicGeometry.FunctionField.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence.Basic

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.TriangleCoherence` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`f2856da541624b0c9ba45549715dcc43057aa759c5d25d05cd66860e80301f96`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
/-!
# Actual arithmetic and geometric generic restriction

Manuscript locator: `K2-018#prop:k2018-arithmetic-characters`.
Mathematical basis: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Migrated interface basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
The original basis remains historical; new-interface compilation is pending.

The ordinary coefficient maps are composed and reassociated before passing to
Ext. The arithmetic coefficient keeps its native Lambda action. Its geometric
contraction uses the literal C1 image of P1's selected primitive root. The
resulting field comparison uses the existing canonical field-pullback map for
every curve Ext class, without requiring that class to come from the base.

The actual-function-field specialization uses exactly constantsAlgebra and
fieldExtensionAlgebra from C1 and proves both scalar towers and the generic
scheme square from the constructed maps. Its public CurveH1 wrapper uses the
existing actual character comparison and frozen geometricH1Hom. No generic
H1 or Bockstein square is an input. P8 identification of its restriction and
field Bockstein remains a downstream application boundary.

Retained standard premises are only the displayed finite Galois-category and
fibre-functor instances, Ext existence/universe inputs, Stacks03AJ/03RV, and
Stacks0BTX for the final coordinate wrapper. That wrapper additionally uses
properness and geometric connectedness, while actual function fields need only
the displayed integrality. Positive levels include n = 1 and composite n.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.EtaleCohomology
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.Group
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
open AlgebraicGeometry.Scheme.EtaleCohomology
namespace AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence
open _root_.AlgebraicGeometry.Scheme.EtaleCohomology.SheafCoherence
open _root_.AlgebraicGeometry.Scheme.Group.BaseChange.PointTransport
attribute [local instance] Over.cartesianMonoidalCategory
universe u w w' w'' w'''

/-- Canonical roots inverse-image coefficients compose as actual sheaf maps. -/
theorem rootsPullbackIso_comp {X Y Z : Scheme.{u}} {D : Type u} [Field D] [IsSepClosed D]
    (f : Y ⟶ X) (g : Z ⟶ Y) (z : Spec (.of D) ⟶ Z)
    [GaloisCategory (Scheme.FiniteEtale Z)] [PreGaloisCategory.FiberFunctor (fiberToFinite z)]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImageComp f g).hom.app (GroupCohomology.Kummer.Coefficients.mu X n) ≫
      (inverseImage g).map
          (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso f n
          hn hinv).hom ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n
            hinv)).hom =
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso (g ≫ f) n
          hn hinv).hom := by
  let A := MultiplicativeGroup.rootsGroupScheme X n
  let : CommGrpObj (MultiplicativeGroup.rootsScheme X n) := MultiplicativeGroup.rootsCommGroup X n
  let : IsFinite A.X.hom := RootsFiniteEtale.rootsScheme_finite X n hn
  let : Etale A.X.hom := RootsFiniteEtale.rootsScheme_etale X n hn hinv
  let AY := MultiplicativeGroup.rootsGroupScheme Y n
  let : CommGrpObj (MultiplicativeGroup.rootsScheme Y n) := MultiplicativeGroup.rootsCommGroup Y n
  let : IsFinite AY.X.hom := RootsFiniteEtale.rootsScheme_finite Y n hn
  let : Etale AY.X.hom := RootsFiniteEtale.rootsScheme_etale Y n hn
    (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
  have hh : (Over.pullback g).mapGrp.map (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom ≫
      (MultiplicativeBaseChange.rootsBaseChangeIso g n).hom =
      (groupPullbackCompIso g f A).hom ≫
        (MultiplicativeBaseChange.rootsBaseChangeIso (g ≫ f) n).hom := by
    apply Grp.hom_ext
    change (Over.pullback g).map (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom.hom.hom ≫
        (MultiplicativeBaseChange.rootsBaseChangeIso g n).hom.hom.hom = _
    rw [Grp.comp_hom_hom, groupPullbackCompIso_projection]
    exact MultiplicativeBaseChange.rootsBaseChangeIso_comp g f n
  change (inverseImageComp f g).hom.app (representedSheaf A) ≫
    (inverseImage g).map ((representedSheafBaseChangeIso f A).hom ≫
      representedSheafMap (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom) ≫
    (representedSheafBaseChangeIso g AY).hom ≫
      representedSheafMap (MultiplicativeBaseChange.rootsBaseChangeIso g n).hom = _
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (representedSheafBaseChangeIso_naturality g
    (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom), ← representedSheafMap_comp, hh]
  simp only [representedSheafMap_comp]
  rw [reassoc_of% (representedSheafBaseChangeIso_comp f g z A)]
  rfl

/-- The literal root coefficients also respect equality of the underlying maps. -/
theorem rootsPullbackIso_congr {X Y : Scheme.{u}} {f g : Y ⟶ X} (e : f = g)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (eqToIso (congrArg (fun k => (inverseImage k).obj
        (GroupCohomology.Kummer.Coefficients.mu X n)) e)).hom ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g n hn
          hinv).hom =
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso f n hn
          hinv).hom := by
  subst g
  simp


section C1Compatibility
open AlgebraicGeometry.Scheme
variable {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
local instance : Nonempty (⊤ : X.Opens) := ⟨⟨_root_.genericPoint X, trivial⟩⟩
/-- The generic triangle uses exactly the C1 constants embedding. -/
theorem generic_constants (p : X ⟶ Spec (.of F)) :
    (X.fromSpecStalk (genericPoint X)) ≫ p =
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldConstants X p)) := by
  apply (cancel_mono (Spec.map (Scheme.ΓSpecIso (.of F)).hom)).mp
  rw [Category.assoc, SpecMap_ΓSpecIso_hom, Scheme.toSpecΓ_naturality]
  rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ]
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  change p.appTop ≫ X.presheaf.germ ⊤ _ _ =
    (Scheme.ΓSpecIso (.of F)).hom ≫
      ((Scheme.ΓSpecIso (.of F)).inv ≫ p.appTop ≫ X.germToFunctionField ⊤)
  simp [Scheme.germToFunctionField]
/-- The arithmetic function-field algebra is the literal constants algebra. -/
theorem generic_fieldMorphism (p : X ⟶ Spec (.of F)) :
    letI := AlgebraicGeometry.Scheme.functionFieldConstantsAlgebra X p
    (X.fromSpecStalk (genericPoint X)) ≫ p =
      GroupCohomology.Kummer.FieldNaturality.fieldMorphism (K := F) (L :=
          X.functionField) :=
  generic_constants p

variable {C : Type u} [Field C] [Algebra F C]
variable (p : X ⟶ Spec (.of F))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap F C))
local notation "Xbar" => pullback p b
variable [IsIntegral (pullback p (Spec.map (CommRingCat.ofHom (algebraMap F C))))]
/-- Both scalar-tower paths are the actual C1 field maps. -/
theorem actual_scalarTower :
    letI := AlgebraicGeometry.Scheme.functionFieldConstantsAlgebra X p
    letI := AlgebraicGeometry.Scheme.functionFieldConstantsAlgebra Xbar (pullback.snd p b)
    letI := Scheme.functionFieldBaseChangeAlgebra p (algebraMap F C)
    letI : Algebra F (Xbar).functionField :=
      ((AlgebraicGeometry.Scheme.functionFieldConstants Xbar (pullback.snd p b)).comp
          (algebraMap F C)).toAlgebra
    IsScalarTower F X.functionField (Xbar).functionField := by
  let := AlgebraicGeometry.Scheme.functionFieldConstantsAlgebra X p
  let := AlgebraicGeometry.Scheme.functionFieldConstantsAlgebra Xbar (pullback.snd p b)
  let := Scheme.functionFieldBaseChangeAlgebra p (algebraMap F C)
  let : Algebra F (Xbar).functionField :=
    ((AlgebraicGeometry.Scheme.functionFieldConstants Xbar (pullback.snd p b)).comp (algebraMap
        F C)).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  exact (Scheme.functionFieldBaseChange_constants p (algebraMap F C)).symm

omit [IsIntegral X] in
/-- The closed-constants tower uses the same selected F-algebra on the geometric field. -/
-- Retain integrality of the original scheme in the generic-constants triangle interface.
@[nolint unusedArguments]
theorem constants_scalarTower [IsIntegral X] :
    letI := AlgebraicGeometry.Scheme.functionFieldConstantsAlgebra Xbar (pullback.snd p b)
    letI : Algebra F (Xbar).functionField :=
      ((AlgebraicGeometry.Scheme.functionFieldConstants Xbar (pullback.snd p b)).comp
          (algebraMap F C)).toAlgebra
    IsScalarTower F C (Xbar).functionField := by
  let := AlgebraicGeometry.Scheme.functionFieldConstantsAlgebra Xbar (pullback.snd p b)
  let : Algebra F (Xbar).functionField :=
    ((AlgebraicGeometry.Scheme.functionFieldConstants Xbar (pullback.snd p b)).comp (algebraMap
        F C)).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- The actual generic square uses C1's actual fieldExtension.toAlgebra. -/
theorem actual_generic_square :
    letI := Scheme.functionFieldBaseChangeAlgebra p (algebraMap F C)
    (pullback p b : Scheme.{u}).fromSpecStalk
        (genericPoint (pullback p b : Scheme.{u})) ≫ pullback.fst p b =
      GroupCohomology.Kummer.FieldNaturality.fieldMorphism (K :=
          X.functionField) (L := (Xbar).functionField) ≫
        (X.fromSpecStalk (genericPoint X)) :=
  Scheme.functionFieldBaseChange_genericPoint p (algebraMap F C)

end C1Compatibility

section CoefficientPasting
variable {B X Y Z : Scheme.{u}} {D : Type u} [Field D] [IsSepClosed D]
  (z : Spec (.of D) ⟶ Z)
  [GaloisCategory (Scheme.FiniteEtale Z)] [PreGaloisCategory.FiberFunctor (fiberToFinite z)]

include z in
/-- Root coefficient transport respects every actual two-step pullback,
including an explicitly identified composite map. -/
theorem rootsCoefficient_comp (f : Y ⟶ X) (g : Z ⟶ Y) (r : Z ⟶ X) (h : g ≫ f = r)
    {L : AbelianSheaf.{u, u + 1} X} (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (e : L ⟶ GroupCohomology.Kummer.Coefficients.mu X n) :
    (eqToIso (congrArg (fun k => (inverseImage k).obj L) h)).inv ≫
      (inverseImageComp f g).hom.app L ≫
      (inverseImage g).map ((inverseImage f).map e) ≫
      (inverseImage g).map
          (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso f n
          hn hinv).hom ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n
            hinv)).hom =
    (inverseImage r).map e ≫
        (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso r n hn
        hinv).hom := by
  subst r
  simp only [eqToIso_refl, Iso.refl_inv, Category.id_comp]
  rw [← Category.assoc, inverseImageComp_map]
  simp only [Category.assoc]
  rw [rootsPullbackIso_comp f g z]

include z in
/-- Ordinary root contraction after a generic-point triangle, at an arbitrary
coefficient sheaf and arbitrary root-sheaf map. -/
theorem root_route_inner (b : X ⟶ B) (g : Y ⟶ X) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : AbelianSheaf.{u, u + 1} B}
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (e : (inverseImage b).obj L ⟶ GroupCohomology.Kummer.Coefficients.mu X n) :
    (triangleIso (g ≫ b) m q
      ((Category.assoc m g b).symm.trans ((congrArg (fun t => t ≫ b) hm).trans hq)) L).inv ≫
      (inverseImage m).map ((inverseImageComp b g).hom.app L ≫
        (inverseImage g).map e ≫
            (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g n
            hn hinv).hom) ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso m n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible g n
            hinv)).hom =
    (triangleIso b r q hq L).inv ≫ (inverseImage r).map e ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso r n hn
          hinv).hom := by
  let hb : m ≫ (g ≫ b) = q := (Category.assoc m g b).symm.trans
    ((congrArg (fun t => t ≫ b) hm).trans hq)
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (triangleIso_assoc_inv b g m q hb (L := L))]
  rw [triangleIso_congr_inv b hm q _ hq L]
  simp only [Category.assoc]
  exact congrArg (fun t => (triangleIso b r q hq L).inv ≫ t)
    (rootsCoefficient_comp z g m r hm n hn hinv e)

include z in
/-- Entire geometric root route, proved before native tensor specialization. -/
theorem geometric_coefficient_route {U : Scheme.{u}} (p : U ⟶ B) (f : Y ⟶ U)
    (b : X ⟶ B) (g : Y ⟶ X) (hf : f ≫ p = g ≫ b) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : AbelianSheaf.{u, u + 1} B}
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (e : (inverseImage b).obj L ⟶ GroupCohomology.Kummer.Coefficients.mu X n) :
    (inverseImageComp f m).hom.app ((inverseImage p).obj L) ≫
      (inverseImage m).map ((triangleIso p f (g ≫ b) hf L).hom ≫
        (inverseImageComp b g).hom.app L ≫ (inverseImage g).map e ≫
        (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g n hn
            hinv).hom) ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso m n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible g n
            hinv)).hom =
    (triangleIso p (m ≫ f) q
      ((Category.assoc m f p).trans ((congrArg (fun t => m ≫ t) hf).trans
        ((Category.assoc m g b).symm.trans ((congrArg (fun t => t ≫ b) hm).trans hq)))) L).hom ≫
      (eqToIso (congrArg (fun k => (inverseImage k).obj L) hq)).inv ≫
      (inverseImageComp b r).hom.app L ≫ (inverseImage r).map e ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso r n hn
          hinv).hom := by
  let hb : m ≫ (g ≫ b) = q := (Category.assoc m g b).symm.trans
    ((congrArg (fun t => t ≫ b) hm).trans hq)
  have ho := triangleIso_route p f m (g ≫ b) hf q hb (L := L)
    ((inverseImageComp b g).hom.app L ≫ (inverseImage g).map e ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g n hn
          hinv).hom)
    (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso m n hn
      (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible g n hinv)).hom
  have hi := root_route_inner z b g m r hm q hq n hn hinv e
  have ht := congrArg (fun t =>
    (triangleIso p (m ≫ f) q
      ((Category.assoc m f p).trans ((congrArg (fun t => m ≫ t) hf).trans hb)) L).hom ≫ t) hi
  simpa only [triangleIso_inv, Category.assoc] using ho.trans ht

end CoefficientPasting

/-- Generic represented coefficient transport along a scheme triangle. Native
marked groups are substituted only after this map equation is proved. -/
-- Retain finiteness of the actual represented coefficient group in the original interface.
@[nolint unusedArguments]
theorem represented_generic_triangle {S X Y : Scheme.{u}} {E : Type u} [Field E] [IsSepClosed E]
    (p : X ⟶ S) (k : Y ⟶ X) (q : Y ⟶ S) (hk : k ≫ p = q)
    (z : Spec (.of E) ⟶ Y)
    [GaloisCategory (Scheme.FiniteEtale Y)] [PreGaloisCategory.FiberFunctor (fiberToFinite z)]
    (A B : Grp (Over S)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
    [IsCommMonObj B.X] [IsFinite B.X.hom] [Etale B.X.hom]
    (D : Grp (Over Y)) [IsCommMonObj D.X]
    (α : A ⟶ B) (β : baseChangedGroup q B ⟶ D) :
    (inverseImageComp p k).hom.app (representedSheaf A) ≫
      (inverseImage k).map (representedSheafBaseChangeIso p A).hom ≫
      (representedSheafBaseChangeIso k (baseChangedGroup p A)).hom ≫
      representedSheafMap ((groupPullbackCompIso k p A).hom ≫
        (eqToIso (congrArg (fun f => baseChangedGroup f A) hk)).hom ≫
        (Over.pullback q).mapGrp.map α ≫ β) =
    (eqToIso (congrArg (fun f => (inverseImage f).obj (representedSheaf A)) hk)).hom ≫
      (inverseImage q).map (representedSheafMap α) ≫
      (representedSheafBaseChangeIso q B).hom ≫ representedSheafMap β := by
  simp only [representedSheafMap_comp]
  rw [reassoc_of% (representedSheafBaseChangeIso_comp p k z A)]
  rw [reassoc_of% (representedSheafBaseChangeIso_congr hk A)]
  rw [← reassoc_of% (representedSheafBaseChangeIso_naturality q α)]


end AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence
