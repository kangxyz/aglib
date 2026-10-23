/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteSetRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsSections
public import Mathlib.CategoryTheory.Presentable.Finite

/-! # Compactness of actual finite locally constant abelian coefficients

An actual finite étale group representative identifies additive morphisms out
of the original coefficient with sections satisfying its group-law equation.
Only its finite étale carrier and binary product are used as test objects.
Their original sections commute with filtered colimits over a qcqs base.
No finite-presentation existence or marking is supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory
  BraidedCategory.ofCartesianMonoidalCategory Cardinal.fact_isRegular_aleph0

namespace FiniteLocallyConstantCompactness

variable {X : Scheme.{u}}

/-- Original sections, with their actual standard value universe. -/
abbrev sectionEvaluation (U : X.Etale) :
    AbelianSheaf.{u, u + 1} X ⥤ Type (u + 1) :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}

/-- The original coefficient morphism commutes with restriction of the identical section. -/
theorem coefficient_restriction {F G : AbelianSheaf.{u, u + 1} X} (q : F ⟶ G)
    {U V : X.Etale} (f : U ⟶ V) (s : F.obj.obj (op V)) :
    q.hom.app (op U) (F.obj.map f.op s) =
      G.obj.map f.op (q.hom.app (op V) s) :=
  ConcreteCategory.congr_hom (q.hom.naturality f.op) s

/-- The actual qcqs sections supplier also preserves the original underlying section sets. -/
abbrev sectionEvaluationPreservesFilteredColimits
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I] (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    PreservesColimitsOfShape I (sectionEvaluation U) := by
  let := Continuity.qcqsSectionsPreservesFilteredColimits (I := I) U
  infer_instance

/-- The original section cocone of a qcqs test object is colimiting. -/
def sectionCoconeIsColimit
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ AbelianSheaf.{u, u + 1} X} {c : Cocone D} (hc : IsColimit c)
    (U : X.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    IsColimit ((sectionEvaluation U).mapCocone c) := by
  let := sectionEvaluationPreservesFilteredColimits (I := I) U
  exact isColimitOfPreserves (sectionEvaluation U) hc

section Group

variable (H : Grp (Over X)) [Etale H.X.hom]

/-- The actual étale test object underlying the representing group. -/
abbrev coefficientObject : X.Etale := Etale.mk H.X.hom

/-- The actual binary group product, as an original étale test object. -/
def squareObject : X.Etale := by
  let : Etale (H.X ⊗ H.X).hom := by
    change Etale (pullback.fst H.X.hom H.X.hom ≫ H.X.hom)
    infer_instance
  exact Etale.mk (H.X ⊗ H.X).hom

/-- An original section of the group is the corresponding actual small-site arrow. -/
def toCoefficient {U : X.Etale}
    (a : (Etale.forget X).obj U ⟶ H.X) : U ⟶ coefficientObject H :=
  MorphismProperty.Over.homMk a.left (Over.w a) (by trivial)

/-- Forgetting this small-site arrow recovers the original group-valued section. -/
@[simp]
theorem forget_toCoefficient {U : X.Etale}
    (a : (Etale.forget X).obj U ⟶ H.X) :
    (Etale.forget X).map (toCoefficient H a) = a := by
  apply Over.OverMorphism.ext
  rfl

/-- The universal identity section has the original identity small-site arrow. -/
@[simp]
theorem toCoefficient_id :
    toCoefficient H (U := coefficientObject H) (𝟙 H.X) = 𝟙 (coefficientObject H) := by
  apply MorphismProperty.Over.Hom.ext
  rfl

/-- Converting actual sections respects the original restriction arrows. -/
theorem toCoefficient_comp {U V : X.Etale} (f : U ⟶ V)
    (a : (Etale.forget X).obj V ⟶ H.X) :
    toCoefficient H ((Etale.forget X).map f ≫ a) = f ≫ toCoefficient H a := by
  apply (Etale.forget X).map_injective
  rw [Functor.map_comp, forget_toCoefficient, forget_toCoefficient]

/-- The original multiplication arrow of the representing group on the small site. -/
def multiplication : squareObject H ⟶ coefficientObject H := toCoefficient H μ[H.X]

/-- The first original group-product projection on the small site. -/
def first : squareObject H ⟶ coefficientObject H := toCoefficient H (fst H.X H.X)

/-- The second original group-product projection on the small site. -/
def second : squareObject H ⟶ coefficientObject H := toCoefficient H (snd H.X H.X)

/-- The original Cartesian pair of two actual group-valued sections. -/
def pairArrow {U : X.Etale} (a b : (Etale.forget X).obj U ⟶ H.X) : U ⟶ squareObject H :=
  MorphismProperty.Over.homMk (lift a b).left (Over.w (lift a b)) (by trivial)

/-- Its first projection is the identical first section. -/
@[reassoc (attr := simp)]
theorem pairArrow_first {U : X.Etale} (a b : (Etale.forget X).obj U ⟶ H.X) :
    pairArrow H a b ≫ first H = toCoefficient H a := by
  apply (Etale.forget X).map_injective
  change lift a b ≫ fst H.X H.X = a
  exact lift_fst a b

/-- Its second projection is the identical second section. -/
@[reassoc (attr := simp)]
theorem pairArrow_second {U : X.Etale} (a b : (Etale.forget X).obj U ⟶ H.X) :
    pairArrow H a b ≫ second H = toCoefficient H b := by
  apply (Etale.forget X).map_injective
  change lift a b ≫ snd H.X H.X = b
  exact lift_snd a b

/-- Native Cartesian Hom-group multiplication is precisely the original multiplication arrow. -/
@[reassoc (attr := simp)]
theorem pairArrow_multiplication {U : X.Etale}
    (a b : (Etale.forget X).obj U ⟶ H.X) :
    pairArrow H a b ≫ multiplication H = toCoefficient H (a * b) := by
  apply (Etale.forget X).map_injective
  rfl

variable [IsCommMonObj H.X]

/-- The literal universal identity section of the actual represented additive sheaf. -/
def universalSection : (representedSheaf H).obj.obj (op (coefficientObject H)) :=
  ULift.up (Additive.ofMul (𝟙 H.X))

/-- Evaluate an original additive coefficient morphism on that universal identity section. -/
def homSection {G : AbelianSheaf.{u, u + 1} X} (a : representedSheaf H ⟶ G) :
    G.obj.obj (op (coefficientObject H)) :=
  a.hom.app (op (coefficientObject H)) (universalSection H)

/-- Genuine represented Yoneda determines the map on every original group-valued section. -/
theorem homSection_formula {G : AbelianSheaf.{u, u + 1} X} (a : representedSheaf H ⟶ G)
    (U : X.Etale) (t : (representedSheaf H).obj.obj (op U)) :
    a.hom.app (op U) t =
      G.obj.map (toCoefficient H t.down.toMul).op (homSection H a) := by
  have h := ConcreteCategory.congr_hom
    (a.hom.naturality (toCoefficient H t.down.toMul).op) (universalSection H)
  change a.hom.app (op U)
      (ULift.up (Additive.ofMul (t.down.toMul ≫ 𝟙 H.X))) =
    G.obj.map (toCoefficient H t.down.toMul).op (homSection H a) at h
  simpa only [Category.comp_id, ofMul_toMul, ULift.up_down] using h

/-- An original additive morphism is determined by its universal section. -/
theorem hom_ext {G : AbelianSheaf.{u, u + 1} X} {a b : representedSheaf H ⟶ G}
    (h : homSection H a = homSection H b) : a = b := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro t
  exact (homSection_formula H a U.unop t).trans
    ((congrArg (fun s => G.obj.map (toCoefficient H t.down.toMul).op s) h).trans
      (homSection_formula H b U.unop t).symm)

/-- The single original group-law equation characterizing additive sections. -/
def IsAdditiveSection (G : AbelianSheaf.{u, u + 1} X)
    (s : G.obj.obj (op (coefficientObject H))) : Prop :=
  G.obj.map (multiplication H).op s =
    G.obj.map (first H).op s + G.obj.map (second H).op s

/-- The universal section of an actual additive morphism satisfies the genuine group law. -/
theorem homSection_isAdditive {G : AbelianSheaf.{u, u + 1} X}
    (a : representedSheaf H ⟶ G) : IsAdditiveSection H G (homSection H a) := by
  let p : (representedSheaf H).obj.obj (op (squareObject H)) :=
    ULift.up (Additive.ofMul (fst H.X H.X))
  let q : (representedSheaf H).obj.obj (op (squareObject H)) :=
    ULift.up (Additive.ofMul (snd H.X H.X))
  let m : (representedSheaf H).obj.obj (op (squareObject H)) :=
    ULift.up (Additive.ofMul μ[H.X])
  have hm : m = p + q := by
    apply ULift.ext
    exact congrArg Additive.ofMul (MonObj.mul_eq_mul H.X)
  calc
    G.obj.map (multiplication H).op (homSection H a) =
        a.hom.app (op (squareObject H)) m :=
      (homSection_formula H a (squareObject H) m).symm
    _ = a.hom.app (op (squareObject H)) (p + q) := congrArg _ hm
    _ = a.hom.app (op (squareObject H)) p +
        a.hom.app (op (squareObject H)) q := map_add _ _ _
    _ = G.obj.map (first H).op (homSection H a) +
        G.obj.map (second H).op (homSection H a) :=
      congrArg₂ (· + ·) (homSection_formula H a (squareObject H) p)
        (homSection_formula H a (squareObject H) q)

omit [IsCommMonObj H.X] in
/-- Pulling back the actual group-law equation gives additivity on every original section. -/
theorem restriction_additive_section (G : AbelianSheaf.{u, u + 1} X)
    (s : G.obj.obj (op (coefficientObject H))) (hs : IsAdditiveSection H G s)
    {U : X.Etale} (a b : (Etale.forget X).obj U ⟶ H.X) :
    G.obj.map (toCoefficient H (a * b)).op s =
      G.obj.map (toCoefficient H a).op s + G.obj.map (toCoefficient H b).op s := by
  let l := pairArrow H a b
  have hl : G.obj.map l.op (G.obj.map (multiplication H).op s) =
      G.obj.map l.op (G.obj.map (first H).op s + G.obj.map (second H).op s) :=
    congrArg (G.obj.map l.op) hs
  have hm : G.obj.map l.op (G.obj.map (multiplication H).op s) =
      G.obj.map (toCoefficient H (a * b)).op s := by
    rw [← Functor.map_comp_apply, ← op_comp, pairArrow_multiplication]
  have hp : G.obj.map l.op (G.obj.map (first H).op s) =
      G.obj.map (toCoefficient H a).op s := by
    rw [← Functor.map_comp_apply, ← op_comp, pairArrow_first]
  have hq : G.obj.map l.op (G.obj.map (second H).op s) =
      G.obj.map (toCoefficient H b).op s := by
    rw [← Functor.map_comp_apply, ← op_comp, pairArrow_second]
  exact hm.symm.trans (hl.trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hp hq)))

/-- A section satisfying the genuine group law gives its actual additive sheaf morphism. -/
def homOfSection (G : AbelianSheaf.{u, u + 1} X)
    (s : G.obj.obj (op (coefficientObject H))) (hs : IsAdditiveSection H G s) :
    representedSheaf H ⟶ G where
  hom :=
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun t => G.obj.map (toCoefficient H t.down.toMul).op s)
        (fun a b => restriction_additive_section H G s hs a.down.toMul b.down.toMul))
      naturality := by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro t
        change G.obj.map
            (toCoefficient H ((Etale.forget X).map f.unop ≫ t.down.toMul)).op s =
          G.obj.map f (G.obj.map (toCoefficient H t.down.toMul).op s)
        rw [toCoefficient_comp, op_comp, Functor.map_comp]
        rfl }

/-- The inverse construction recovers the identical original universal section. -/
@[simp]
theorem homSection_homOfSection (G : AbelianSheaf.{u, u + 1} X)
    (s : G.obj.obj (op (coefficientObject H))) (hs : IsAdditiveSection H G s) :
    homSection H (homOfSection H G s hs) = s := by
  change G.obj.map (toCoefficient H (U := coefficientObject H) (𝟙 H.X)).op s = s
  rw [toCoefficient_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The original Hom parametrization is natural in every actual coefficient map. -/
@[simp]
theorem homSection_naturality {G G' : AbelianSheaf.{u, u + 1} X}
    (a : representedSheaf H ⟶ G) (q : G ⟶ G') :
    homSection H (a ≫ q) = q.hom.app (op (coefficientObject H)) (homSection H a) := rfl

variable [IsFinite H.X.hom]

/-- Actual finite represented abelian coefficients are compact over a qcqs base. -/
theorem isFinitelyPresentable_representedSheaf [CompactSpace X] [QuasiSeparatedSpace X] :
    IsFinitelyPresentable.{u + 1} (representedSheaf H) := by
  let : CompactSpace (coefficientObject H).left :=
    QuasiCompact.compactSpace_of_compactSpace H.X.hom
  let : QuasiSeparatedSpace (coefficientObject H).left :=
    quasiSeparatedSpace_of_quasiSeparated H.X.hom
  let : IsFinite (squareObject H).hom := by
    change IsFinite (pullback.fst H.X.hom H.X.hom ≫ H.X.hom)
    infer_instance
  let : CompactSpace (squareObject H).left :=
    QuasiCompact.compactSpace_of_compactSpace
      (show (squareObject H).left ⟶ X from (squareObject H).hom)
  let : QuasiSeparatedSpace (squareObject H).left :=
    quasiSeparatedSpace_of_quasiSeparated
      (show (squareObject H).left ⟶ X from (squareObject H).hom)
  apply IsCardinalPresentable.mk
  intro I _ _ D c hc
  have : IsFiltered I := isFiltered_of_isCardinalFiltered I Cardinal.aleph0.{u + 1}
  let hY := sectionCoconeIsColimit hc (coefficientObject H)
  let hV := sectionCoconeIsColimit hc (squareObject H)
  constructor
  · intro a
    obtain ⟨i, s, hs⟩ := Types.jointly_surjective_of_isColimit hY (homSection H a)
    let x := (D.obj i).obj.map (multiplication H).op s
    let y := (D.obj i).obj.map (first H).op s + (D.obj i).obj.map (second H).op s
    have hx : (c.ι.app i).hom.app (op (squareObject H)) x =
        c.pt.obj.map (multiplication H).op (homSection H a) :=
      (coefficient_restriction (c.ι.app i) (multiplication H) s).trans
        (congrArg (c.pt.obj.map (multiplication H).op) hs)
    have hy : (c.ι.app i).hom.app (op (squareObject H)) y =
        c.pt.obj.map (first H).op (homSection H a) +
          c.pt.obj.map (second H).op (homSection H a) := by
      calc
        _ = (c.ι.app i).hom.app (op (squareObject H))
              ((D.obj i).obj.map (first H).op s) +
            (c.ι.app i).hom.app (op (squareObject H))
              ((D.obj i).obj.map (second H).op s) := map_add _ _ _
        _ = c.pt.obj.map (first H).op
              ((c.ι.app i).hom.app (op (coefficientObject H)) s) +
            c.pt.obj.map (second H).op
              ((c.ι.app i).hom.app (op (coefficientObject H)) s) :=
          congrArg₂ (· + ·) (coefficient_restriction (c.ι.app i) (first H) s)
            (coefficient_restriction (c.ι.app i) (second H) s)
        _ = _ := congrArg (fun z => c.pt.obj.map (first H).op z +
          c.pt.obj.map (second H).op z) hs
    have hxy : ((sectionEvaluation (squareObject H)).mapCocone c).ι.app i x =
        ((sectionEvaluation (squareObject H)).mapCocone c).ι.app i y :=
      hx.trans ((homSection_isAdditive H a).trans hy.symm)
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hV x y).mp hxy
    let s' := (D.map f).hom.app (op (coefficientObject H)) s
    have hs' : IsAdditiveSection H (D.obj j) s' := by
      calc
        (D.obj j).obj.map (multiplication H).op s' =
            (D.map f).hom.app (op (squareObject H)) x :=
          (coefficient_restriction (D.map f) (multiplication H) s).symm
        _ = (D.map f).hom.app (op (squareObject H)) y := hf
        _ = (D.map f).hom.app (op (squareObject H))
              ((D.obj i).obj.map (first H).op s) +
            (D.map f).hom.app (op (squareObject H))
              ((D.obj i).obj.map (second H).op s) := map_add _ _ _
        _ = (D.obj j).obj.map (first H).op s' +
            (D.obj j).obj.map (second H).op s' :=
          congrArg₂ (· + ·) (coefficient_restriction (D.map f) (first H) s)
            (coefficient_restriction (D.map f) (second H) s)
    refine ⟨j, homOfSection H (D.obj j) s' hs', ?_⟩
    apply hom_ext H
    rw [homSection_naturality, homSection_homOfSection]
    have hw := congrArg
      (fun q : D.obj i ⟶ c.pt => q.hom.app (op (coefficientObject H)) s) (c.w f)
    exact hw.trans hs
  · intro i a b hab
    have h : ((sectionEvaluation (coefficientObject H)).mapCocone c).ι.app i
          (homSection H a) =
        ((sectionEvaluation (coefficientObject H)).mapCocone c).ι.app i (homSection H b) := by
      exact congrArg (homSection H) hab
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hY
      (homSection H a) (homSection H b)).mp h
    refine ⟨j, f, ?_⟩
    apply hom_ext H
    exact hf

end Group

end FiniteLocallyConstantCompactness

/-- Finite locally constant abelian sheaves on a qcqs scheme are compact in the actual
standard coefficient and filtered-index universes. The representative is constructed
internally from the original local trivializations, with no marking premise. -/
theorem isFinitelyPresentable_of_isFiniteLocallyConstant
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    IsFinitelyPresentable.{u + 1} F := by
  let R := CoefficientRepresentation.ofFiniteLocallyConstant F (stacks03RV X) hF
  let : Etale R.group.X.hom := R.etale
  let : IsFinite R.group.X.hom := R.finite
  let : IsCommMonObj R.group.X := R.commutative
  have : IsFinitelyPresentable.{u + 1} (representedSheaf R.group) :=
    FiniteLocallyConstantCompactness.isFinitelyPresentable_representedSheaf R.group
  exact isCardinalPresentable_of_iso R.iso Cardinal.aleph0.{u + 1}

end AlgebraicGeometry.Scheme.EtaleCohomology
