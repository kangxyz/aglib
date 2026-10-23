/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineStalkCoordinates
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DirectImageEvaluationGerm
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.AffineExtendedPoint

/-! # Actual common-field coordinates of finite direct-image stalks -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u
attribute [local instance] hasSheafifyLarge
open CoefficientStalkBaseChange

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsAlgClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]

omit [IsFinite f] in
private theorem baseChangedEtaleCone_π_fst (i : GeometricEtaleNeighborhood R Ω) :
    ((baseChangedEtaleCone R Ω f).π.app (op i)).left ≫
        pullback.fst (Spec.algebraMap R i.algebra) f =
      finiteAffineProjection R Ω f ≫ (specCone R Ω).π.app (op i) := by
  change (pullback.lift _ _ _) ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- The common-field coordinate retains the actual component residue field and
then applies its original field-extension stalk isomorphism. -/
def finiteAffineExtendedCoordinate (F : AbelianSheaf.{u, u + 1} X)
    (m : MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤)) :
    coefficientFiber (Spec.algebraMap R Ω) ((directImage f).obj F) ⟶
      coefficientFiber (finiteAffineExtendedPoint R Ω f m) F := by
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  let : Algebra (ResidueField B) Ω := (GeometricEtaleColimit.residueFieldEmbedding R Ω).toAlgebra
  let q : Spec (.of Γ(Y, ⊤)) ⟶ X := Y.isoSpec.inv ≫ (baseChangedEtaleCone R Ω f).pt.hom
  let ev : finiteAffineStalkTuple R Ω f F ⟶
      (finiteSourceComponentPoint Γ(Y, ⊤) B q m).presheafFiber.obj F.obj :=
    AddCommGrpCat.ofHom { toFun := fun a => a m, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact (finiteAffineDirectImageStalkIso R Ω f F).hom ≫ ev ≫
    (finiteSourceComponentStalkExtension B Γ(Y, ⊤) Ω q m).hom.app F.obj

/-- On every actual affine neighborhood, a common-field coordinate is the
original germ at the literal pulled-back point. -/
@[reassoc]
theorem germ_finiteAffineExtendedCoordinate (F : AbelianSheaf.{u, u + 1} X)
    (m : MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤))
    (i : GeometricEtaleNeighborhood R Ω) :
    (pointSmallEtale (Spec.algebraMap R Ω)).toPresheafFiber
        (etaleObject R Ω i) (stagePoint R Ω i) ((directImage f).obj F).obj ≫
        finiteAffineExtendedCoordinate R Ω f F m =
      (pointSmallEtale (finiteAffineExtendedPoint R Ω f m)).toPresheafFiber
        ((siteBaseChange f).obj (etaleObject R Ω i))
        (pointedPulledBackPoint f (finiteAffineExtendedPoint R Ω f m)
          (Spec.algebraMap R Ω) (finiteAffineExtendedPoint_comp R Ω f m)
          (etaleObject R Ω i) (stagePoint R Ω i)) F.obj := by
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  let : Algebra (ResidueField B) Ω := (GeometricEtaleColimit.residueFieldEmbedding R Ω).toAlgebra
  let A := Γ(Y, ⊤)
  let q : Spec (.of A) ⟶ X := Y.isoSpec.inv ≫ (baseChangedEtaleCone R Ω f).pt.hom
  let : Module.Finite B (Localization.AtPrime m.asIdeal) :=
    HenselianLocalRing.finite_localizationAtPrime B A m.asIdeal
  let : IsLocalHom (algebraMap B (Localization.AtPrime m.asIdeal)) := by
    apply ((local_hom_TFAE (algebraMap B (Localization.AtPrime m.asIdeal))).out 5 1).mp
    exact eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal
        (maximalIdeal (Localization.AtPrime m.asIdeal)))
  let : IsSepClosed (ResidueField (Localization.AtPrime m.asIdeal)) :=
    HenselianLocalRing.residueField_isSepClosed_localizationAtPrime B A m.asIdeal
  let D := baseChangedEtaleDiagram R Ω f
  let c := baseChangedEtaleCone R Ω f
  let pκ := finiteLimitStagePoint A B D c Y.isoSpec.symm (op i) m
  let ε := Spec.map (CommRingCat.ofHom
    (finiteLocalResidueEmbedding B (Localization.AtPrime m.asIdeal) Ω).toRingHom)
  let pΩ := pointFiberExtension (finiteSourceResiduePoint A m ≫ q) ε (D.obj (op i)) pκ
  have hb : Spec.map (CommRingCat.ofHom
      ((algebraMap (ResidueField B) Ω).comp (IsLocalRing.residue B))) = point R Ω := by
    change Spec.map (CommRingCat.ofHom
      ((GeometricEtaleColimit.residueFieldEmbedding R Ω).comp (IsLocalRing.residue B))) = _
    rw [GeometricEtaleColimit.residueFieldEmbedding_comp_residue]
    rfl
  have hpΩ : pΩ = pointedPulledBackPoint f (finiteAffineExtendedPoint R Ω f m)
      (Spec.algebraMap R Ω) (finiteAffineExtendedPoint_comp R Ω f m)
      (etaleObject R Ω i) (stagePoint R Ω i) := by
    apply Over.OverMorphism.ext
    apply Eq.trans ?_ (pointedPulledBackPoint_left f
      (finiteAffineExtendedPoint R Ω f m) (Spec.algebraMap R Ω)
      (finiteAffineExtendedPoint_comp R Ω f m) (etaleObject R Ω i)
      (stagePoint R Ω i)).symm
    apply pullback.hom_ext
    · apply Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      let r : Spec (.of (ResidueField (Localization.AtPrime m.asIdeal))) ⟶
          Spec (.of A) := finiteSourceResiduePoint A m
      let l : Y ⟶ pullback (Spec.algebraMap R i.algebra) f := (c.π.app (op i)).left
      let π : Spec (.of B) ⟶ Spec (.of i.algebra) :=
        Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.stageRingHom R Ω i))
      let z : Spec (.of Ω) ⟶ Spec (.of A) :=
        Spec.map (CommRingCat.ofHom (finiteComponentPoint B A Ω m))
      have hπ : l ≫ pullback.fst (Spec.algebraMap R i.algebra) f = p ≫ π :=
        baseChangedEtaleCone_π_fst R Ω f i
      have hspec : ε ≫ r = z := (finiteComponentPoint_spec_eq B A Ω m).symm
      have ha : Y.isoSpec.inv ≫ p = Spec.algebraMap B A :=
        (finiteSource_spec_algebraMap B p).symm
      have hz : z ≫ Spec.algebraMap B A = point R Ω :=
        (finiteComponentPoint_spec_comp B A Ω m).trans hb
      have hbase : (ε ≫ r) ≫ (Y.isoSpec.inv ≫ p) = point R Ω :=
        (congrArg (fun k => k ≫ (Y.isoSpec.inv ≫ p)) hspec).trans
          ((congrArg (fun k => z ≫ k) ha).trans hz)
      let γ : Spec (.of Ω) ⟶ Spec (.of i.algebra) :=
        Spec.map (CommRingCat.ofHom i.point.toRingHom)
      have hpoint : point R Ω ≫ π = γ := point_π R Ω i
      have hfirst : (ε ≫ (r ≫ Y.isoSpec.inv ≫ l)) ≫
          pullback.fst (Spec.algebraMap R i.algebra) f =
          ((ε ≫ r) ≫ (Y.isoSpec.inv ≫ p)) ≫ π := by
        simp only [Category.assoc]
        exact congrArg (fun k : Y ⟶ Spec (.of i.algebra) => ε ≫ r ≫ Y.isoSpec.inv ≫ k) hπ
      exact hfirst.trans ((congrArg (fun k => k ≫ π) hbase).trans hpoint)
    · apply Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      exact pΩ.w
  apply ConcreteCategory.hom_ext
  intro a
  have hκ := germ_finiteAffineDirectImageStalkIso R Ω f F i a m
  have he := finiteSourceComponentStalkExtension_germ B A Ω q m F.obj (D.obj (op i)) pκ
  change (finiteSourceComponentStalkExtension B A Ω q m).hom.app F.obj
      ((finiteAffineDirectImageStalkIso R Ω f F).hom
        ((pointSmallEtale (Spec.algebraMap R Ω)).toPresheafFiber
          (etaleObject R Ω i) (stagePoint R Ω i) ((directImage f).obj F).obj a) m) = _
  rw [hκ]
  exact (ConcreteCategory.congr_hom he a).trans
    (congrArg (fun t => (pointSmallEtale (finiteAffineExtendedPoint R Ω f m)).toPresheafFiber
      (D.obj (op i)) t F.obj a) hpΩ)

/-- The actual common-field product coordinate is precisely original stalk
unit followed by original adjunction counit, not merely an abstract isomorphism. -/
theorem finiteAffineExtendedCoordinate_eq_evaluation
    (F : AbelianSheaf.{u, u + 1} X)
    (m : MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤)) :
    finiteAffineExtendedCoordinate R Ω f F m =
      pointedDirectImageEvaluation f (finiteAffineExtendedPoint R Ω f m)
        (Spec.algebraMap R Ω) (finiteAffineExtendedPoint_comp R Ω f m) F := by
  apply (cancel_epi (stalkIso R Ω ((directImage f).obj F).obj).hom).mp
  apply colimit.hom_ext
  intro i
  let P := ((directImage f).obj F).obj
  let j := colimit.ι (sectionDiagram R Ω P) i
  let E := (stalkIso R Ω P).hom
  let k := finiteAffineExtendedCoordinate R Ω f F m
  let l := pointedDirectImageEvaluation f (finiteAffineExtendedPoint R Ω f m)
    (Spec.algebraMap R Ω) (finiteAffineExtendedPoint_comp R Ω f m) F
  have hg := ι_stalkIso_hom R Ω P i
  have he := (germ_finiteAffineExtendedCoordinate R Ω f F m i).trans
    (germ_pointedDirectImageEvaluation f (finiteAffineExtendedPoint R Ω f m)
      (Spec.algebraMap R Ω) (finiteAffineExtendedPoint_comp R Ω f m) F
      (etaleObject R Ω i) (stagePoint R Ω i)).symm
  exact (Category.assoc j E k).symm.trans
    ((congrArg (fun a => a ≫ k) hg).trans
      (he.trans ((congrArg (fun a => a ≫ l) hg).symm.trans (Category.assoc j E l))))

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
