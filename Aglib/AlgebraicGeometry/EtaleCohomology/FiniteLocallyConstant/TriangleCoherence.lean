/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SheafCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.FieldNaturality
public import Aglib.AlgebraicGeometry.FunctionField.BaseChange

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

/-- Evaluation form of coefficient functoriality, avoiding partial-hom rewriting. -/
theorem coefficientMap_comp_apply {Y : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
    {L M N : AbelianSheaf.{u, u + 1} Y} (q : L ⟶ M) (r : M ⟶ N) (a : H1Etale Y L) :
    coefficientMap r (coefficientMap q a) = coefficientMap (q ≫ r) a :=
  (congrArg (fun h : H1Etale Y L →+ H1Etale Y N => h a) (coefficientMap_comp q r)).symm

/-- Pure categorical cancellation, keeping all later scheme endpoints opaque. -/
theorem iso_cancel_right_pair {V : Type*} [Category V] {A B C D E : V}
    (a : A ≅ B) (b : B ⟶ C) (c : D ≅ C) (d : E ≅ D) (e : A ⟶ E)
    (h : a.hom ≫ b = e ≫ d.hom ≫ c.hom) :
    b ≫ c.inv ≫ d.inv = a.inv ≫ e := by
  apply (cancel_epi a.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    using congrArg (fun q => q ≫ c.inv ≫ d.inv) h

/-- A second pure categorical cancellation for inverse triangle pasting. -/
theorem iso_factor_inverse {V : Type*} [Category V] {X Y Z T : V}
    (a : X ⟶ Y) (b : Y ≅ Z) (c : Z ≅ T) (d : X ≅ T)
    (h : a ≫ b.hom ≫ c.hom = d.hom) :
    c.inv ≫ b.inv = d.inv ≫ a := by
  apply (cancel_epi d.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    using (congrArg (fun q => q ≫ c.inv ≫ b.inv) h).symm

/-- The literal inverse-image coefficient transport along a scheme triangle. -/
def triangleIso {B X Y : Scheme.{u}} (p : X ⟶ B) (f : Y ⟶ X)
    (q : Y ⟶ B) (hf : f ≫ p = q) (L : AbelianSheaf.{u, u + 1} B) :
    (inverseImage f).obj ((inverseImage p).obj L) ≅ (inverseImage q).obj L :=
  ((inverseImageComp p f).app L).symm ≪≫
    eqToIso (congrArg (fun k => (inverseImage k).obj L) hf)

/-- Coherence of the actual triangle transport is proved before using Ext. -/
theorem triangleIso_comp {B X Y Z : Scheme.{u}} {D : Type u} [Field D] [IsSepClosed D]
    (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    (z : Spec (.of D) ⟶ Z)
    [GaloisCategory (Scheme.FiniteEtale Z)] [PreGaloisCategory.FiberFunctor (fiberToFinite z)]
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L) :
    (inverseImageComp f g).hom.app ((inverseImage p).obj L) ≫
        (inverseImage g).map (triangleIso p f q hf L).hom ≫
        (triangleIso q g r hg L).hom =
      (triangleIso p (g ≫ f) r
        ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom := by
  subst q
  subst r
  have hc := iso_cancel_right_pair
    ((inverseImageComp p (g ≫ f)).app L)
    ((inverseImageComp f g).hom.app ((inverseImage p).obj L))
    ((inverseImage g).mapIso ((inverseImageComp p f).app L))
    ((inverseImageComp (f ≫ p) g).app L)
    (eqToIso (congrArg (fun k => (inverseImage k).obj L) (Category.assoc g f p))).hom
    (inverseImageComp_assoc_finite p f g z R)
  simpa only [triangleIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, Functor.map_comp,
    Functor.map_id, Functor.mapIso_inv, Iso.app_hom] using hc

/-- The same coherence with the final triangle moved to the other side. -/
theorem triangleIso_comp_inv {B X Y Z : Scheme.{u}} {D : Type u} [Field D] [IsSepClosed D]
    (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    (z : Spec (.of D) ⟶ Z)
    [GaloisCategory (Scheme.FiniteEtale Z)] [PreGaloisCategory.FiberFunctor (fiberToFinite z)]
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L) :
    (inverseImageComp f g).hom.app ((inverseImage p).obj L) ≫
        (inverseImage g).map (triangleIso p f q hf L).hom =
      (triangleIso p (g ≫ f) r
        ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom ≫
        (triangleIso q g r hg L).inv := by
  apply (cancel_mono (triangleIso q g r hg L).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact triangleIso_comp p f g q hf r hg z R

/-- Equality of actual generic maps gives precisely the corresponding transport. -/
theorem triangleIso_congr {B X Y : Scheme.{u}} (p : X ⟶ B)
    {f g : Y ⟶ X} (e : f = g) (q : Y ⟶ B) (hf : f ≫ p = q) (hg : g ≫ p = q)
    (L : AbelianSheaf.{u, u + 1} B) :
    (eqToIso (congrArg (fun k => (inverseImage k).obj ((inverseImage p).obj L)) e)).hom ≫
        (triangleIso p g q hg L).hom = (triangleIso p f q hf L).hom := by
  subst g
  simp

/-- Inverse-image composition is natural in the literal coefficient map. -/
theorem inverseImageComp_map {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {L M : AbelianSheaf.{u, u + 1} X} (q : L ⟶ M) :
    (inverseImageComp f g).hom.app L ≫ (inverseImage g).map ((inverseImage f).map q) =
      (inverseImage (g ≫ f)).map q ≫ (inverseImageComp f g).hom.app M :=
  ((inverseImageComp f g).hom.naturality q).symm

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
/-- Inverse triangle transport reassociates with actual inverse-image composition. -/
theorem triangleIso_assoc_inv (b : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (r : Z ⟶ B) (h : g ≫ (f ≫ b) = r)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L) :
    (triangleIso (f ≫ b) g r h L).inv ≫
      (inverseImage g).map ((inverseImageComp b f).hom.app L) =
    (triangleIso b (g ≫ f) r ((Category.assoc g f b).trans h) L).inv ≫
      (inverseImageComp f g).hom.app ((inverseImage b).obj L) := by
  have ht := triangleIso_comp b f g (f ≫ b) rfl r h z R
  have hi := iso_factor_inverse
    ((inverseImageComp f g).hom.app ((inverseImage b).obj L))
    ((inverseImage g).mapIso (triangleIso b f (f ≫ b) rfl L))
    (triangleIso (f ≫ b) g r h L)
    (triangleIso b (g ≫ f) r ((Category.assoc g f b).trans h) L) ht
  simpa only [triangleIso, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, eqToIso_refl,
    Iso.refl_inv, Category.id_comp, Functor.mapIso_inv] using hi

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

omit [GaloisCategory (Scheme.FiniteEtale Z)] in
/-- Inverse triangle transport respects an actual equality of generic maps. -/
-- Retain the original Galois-category input for the generic triangle source.
@[nolint unusedArguments]
theorem triangleIso_congr_inv [GaloisCategory (Scheme.FiniteEtale Z)] (p : X ⟶ B) {f g : Z ⟶ X}
    (e : f = g)
    (r : Z ⟶ B) (hf : f ≫ p = r) (hg : g ≫ p = r) (L : AbelianSheaf.{u, u + 1} B) :
    (triangleIso p f r hf L).inv = (triangleIso p g r hg L).inv ≫
      (eqToIso (congrArg (fun k => (inverseImage k).obj ((inverseImage p).obj L)) e)).inv := by
  subst g
  simp
/-- The inverse triangle formula is kept opaque before native specialization. -/
theorem triangleIso_inv {B X Y : Scheme.{u}} (p : X ⟶ B) (f : Y ⟶ X)
    (q : Y ⟶ B) (hf : f ≫ p = q) (L : AbelianSheaf.{u, u + 1} B) :
    (triangleIso p f q hf L).inv =
      (eqToIso (congrArg (fun k => (inverseImage k).obj L) hf)).inv ≫
        (inverseImageComp p f).hom.app L := rfl

include z in
/-- Pasting a triangle with arbitrary ordinary coefficient morphisms. -/
theorem triangleIso_route (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L)
    {N : AbelianSheaf.{u, u + 1} Y} {Q : AbelianSheaf.{u, u + 1} Z}
    (e : (inverseImage q).obj L ⟶ N) (s : (inverseImage g).obj N ⟶ Q) :
    (inverseImageComp f g).hom.app ((inverseImage p).obj L) ≫
      (inverseImage g).map ((triangleIso p f q hf L).hom ≫ e) ≫ s =
    (triangleIso p (g ≫ f) r
      ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom ≫
      (triangleIso q g r hg L).inv ≫ (inverseImage g).map e ≫ s := by
  have h := triangleIso_comp_inv p f g q hf r hg z (L := L) R
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t => t ≫ (inverseImage g).map e ≫ s) h

include z in
/-- Explicit direct-source form of the generic coefficient route. -/
theorem triangleIso_route_explicit (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L)
    {N : AbelianSheaf.{u, u + 1} Y} {Q : AbelianSheaf.{u, u + 1} Z}
    (e : (inverseImage q).obj L ⟶ N) (s : (inverseImage g).obj N ⟶ Q) :
    (inverseImageComp f g).hom.app ((inverseImage p).obj L) ≫
      (inverseImage g).map ((triangleIso p f q hf L).hom ≫ e) ≫ s =
    (triangleIso p (g ≫ f) r
      ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom ≫
      (eqToIso (congrArg (fun k => (inverseImage k).obj L) hg)).inv ≫
      (inverseImageComp q g).hom.app L ≫ (inverseImage g).map e ≫ s := by
  simpa only [triangleIso_inv, Category.assoc] using
    triangleIso_route z p f g q hf r hg R e s

include z in
/-- Ordinary root contraction after a generic-point triangle, at an arbitrary
coefficient sheaf and arbitrary root-sheaf map. -/
theorem root_route_inner (b : X ⟶ B) (g : Y ⟶ X) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L)
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
  rw [reassoc_of% (triangleIso_assoc_inv z b g m q hb (L := L) R)]
  rw [triangleIso_congr_inv b hm q _ hq L]
  simp only [Category.assoc]
  exact congrArg (fun t => (triangleIso b r q hq L).inv ≫ t)
    (rootsCoefficient_comp z g m r hm n hn hinv e)

include z in
/-- Entire geometric root route, proved before native tensor specialization. -/
theorem geometric_coefficient_route {U : Scheme.{u}} (p : U ⟶ B) (f : Y ⟶ U)
    (b : X ⟶ B) (g : Y ⟶ X) (hf : f ≫ p = g ≫ b) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L)
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
  have ho := triangleIso_route z p f m (g ≫ b) hf q hb (L := L) R
    ((inverseImageComp b g).hom.app L ≫ (inverseImage g).map e ≫
      (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso g n hn
          hinv).hom)
    (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso m n hn
      (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible g n hinv)).hom
  have hi := root_route_inner z b g m r hm q hq R n hn hinv e
  have ht := congrArg (fun t =>
    (triangleIso p (m ≫ f) q
      ((Category.assoc m f p).trans ((congrArg (fun t => m ≫ t) hf).trans hb)) L).hom ≫ t) hi
  simpa only [triangleIso_inv, Category.assoc] using ho.trans ht

end CoefficientPasting

/-- The actual scheme-triangle transport is natural in ordinary coefficient maps. -/
theorem triangleIso_naturality {B X Y : Scheme.{u}} (p : X ⟶ B) (f : Y ⟶ X)
    (r : Y ⟶ B) (hf : f ≫ p = r) {L N : AbelianSheaf.{u, u + 1} B} (q : L ⟶ N) :
    (inverseImage f).map ((inverseImage p).map q) ≫ (triangleIso p f r hf N).hom =
      (triangleIso p f r hf L).hom ≫ (inverseImage r).map q := by
  subst r
  simpa only [triangleIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, Functor.comp_map, Functor.comp_obj]
    using ((inverseImageComp p f).inv.naturality q)

/-- Generic naturality of the entire geometric coefficient route, with all
ordinary coefficient sheaves kept abstract. -/
theorem geometric_coefficient_route_naturality {B C X Y : Scheme.{u}}
    (p : X ⟶ B) (f : Y ⟶ X) (b : C ⟶ B) (g : Y ⟶ C) (hf : f ≫ p = g ≫ b)
    {L N : AbelianSheaf.{u, u + 1} B} {M : AbelianSheaf.{u, u + 1} C}
    {Q : AbelianSheaf.{u, u + 1} Y} (a : L ⟶ N)
    (e : (inverseImage b).obj N ⟶ M) (r : (inverseImage g).obj M ⟶ Q) :
    (inverseImage f).map ((inverseImage p).map a) ≫
      (triangleIso p f (g ≫ b) hf N).hom ≫ (inverseImageComp b g).hom.app N ≫
      (inverseImage g).map e ≫ r =
    (triangleIso p f (g ≫ b) hf L).hom ≫ (inverseImageComp b g).hom.app L ≫
      (inverseImage g).map ((inverseImage b).map a ≫ e) ≫ r := by
  rw [reassoc_of% (triangleIso_naturality p f (g ≫ b) hf a)]
  rw [reassoc_of% ((inverseImageComp b g).hom.naturality a)]
  simp only [Functor.map_comp, Category.assoc]

/-- Iso-form of the abstract geometric coefficient route. Its two iso
parenthesizations match the native tensor and represented arithmetic definitions. -/
theorem geometric_coefficient_route_iso {B C X Y : Scheme.{u}}
    (p : X ⟶ B) (f : Y ⟶ X) (b : C ⟶ B) (g : Y ⟶ C) (hf : f ≫ p = g ≫ b)
    {L N : AbelianSheaf.{u, u + 1} B} {M : AbelianSheaf.{u, u + 1} C}
    {Q : AbelianSheaf.{u, u + 1} Y} (a : L ≅ N)
    (e : (inverseImage b).obj N ≅ M) (r : (inverseImage g).obj M ≅ Q) :
    ((inverseImage f).mapIso ((inverseImage p).mapIso a)).hom ≫
      (triangleIso p f (g ≫ b) hf N ≪≫ (inverseImageComp b g).app N ≪≫
        (inverseImage g).mapIso e ≪≫ r).hom =
    (((inverseImageComp p f).app L).symm ≪≫
      eqToIso (congrArg (fun t => (inverseImage t).obj L) hf) ≪≫
      (inverseImageComp b g).app L ≪≫
      (inverseImage g).mapIso ((inverseImage b).mapIso a ≪≫ e) ≪≫ r).hom := by
  simpa only [triangleIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
    geometric_coefficient_route_naturality p f b g hf a.hom e.hom r.hom

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

/-- An ordinary common-source coefficient equation identifies the two actual
triangle restriction routes; every coefficient object remains abstract. -/
theorem triangle_coefficient_transport_eq {B X Y : Scheme.{u}}
    (p : X ⟶ B) (k : Y ⟶ X) (q : Y ⟶ B) (hk : k ≫ p = q)
    {L N : AbelianSheaf.{u, u + 1} B} {D : AbelianSheaf.{u, u + 1} X}
    {Q : AbelianSheaf.{u, u + 1} Y} (α : L ⟶ N)
    (c : (inverseImage p).obj L ⟶ D) (r : (inverseImage k).obj D ⟶ Q)
    (s : (inverseImage q).obj N ⟶ Q)
    (he : (inverseImageComp p k).hom.app L ≫ (inverseImage k).map c ≫ r =
      (eqToIso (congrArg (fun f => (inverseImage f).obj L) hk)).hom ≫
        (inverseImage q).map α ≫ s) :
    (inverseImage k).map ((inverseImage p).map α) ≫
      (triangleIso p k q hk N).hom ≫ s = (inverseImage k).map c ≫ r := by
  rw [reassoc_of% (triangleIso_naturality p k q hk α)]
  apply (cancel_epi ((inverseImageComp p k).hom.app L)).mp
  simpa only [triangleIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc, Iso.hom_inv_id_app_assoc] using he.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.TriangleCoherence
