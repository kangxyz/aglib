/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.GeometricCoverModels
public import Aglib.AlgebraicGeometry.FundamentalGroup.FiniteFieldCoverHom

/-!
# SeparableFieldHom

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

universe u
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))

/-- The cover of `X` obtained by base change to the finite separable part of the field generated
by `s`. -/
abbrev separableStageCover (s : Finset Ω) : Scheme.FiniteEtale X :=
  (baseChange p).obj (SeparableStage.finiteSeparableFieldCover K (finiteSepField K Ω s))

/-- The projection from the geometric base change to the finite separable stage selected by `s`. -/
abbrev separableStageProjection (s : Finset Ω) :
    pullback p (Spec.algebraMap K Ω) ⟶ (separableStageCover K Ω p s).obj.left :=
  geometricStageRight (Spec.algebraMap K Ω) p
    (SeparableStage.finiteSeparableFieldCover K (finiteSepField K Ω s)) (finiteSepPoint K Ω s)

/-- The map from the full finite-field stage to its separable stage, induced by the
intermediate-field extension. -/
def reversePureProjection (s : Finset Ω) :
    ((FieldLimit.schemeDiagram K Ω p).obj (op s)).left ⟶ (separableStageCover K Ω p s).obj.left :=
  (pullbackSymmetry p (Spec.algebraMap K (FieldLimit.finiteField K Ω s))).inv ≫
    SeparableStage.extensionProjection K (finiteSepField K Ω s) (FieldLimit.finiteField K Ω s) p ≫
      (pullbackSymmetry p (Spec.algebraMap K (finiteSepField K Ω s))).hom

@[reassoc] theorem reversePureProjection_base (s : Finset Ω) :
    reversePureProjection K Ω p s ≫ (separableStageCover K Ω p s).obj.hom =
      ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom := by
  change (_ ≫ _ ≫ _) ≫ pullback.snd (Spec.algebraMap K (finiteSepField K Ω s)) p =
    pullback.snd (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, SeparableStage.extensionProjection_base,
    pullbackSymmetry_inv_comp_fst]

theorem fieldProjection_reversePureProjection (s : Finset Ω) :
    FieldLimit.fieldProjection K Ω p (op s) ≫ reversePureProjection K Ω p s =
      separableStageProjection K Ω p s := by
  let eS := pullbackSymmetry p (Spec.algebraMap K (finiteSepField K Ω s))
  have h := geometricStage_sep_projection K Ω p s
  change separableStageProjection K Ω p s ≫ eS.inv =
    standardStageProjection K Ω p s ≫
      SeparableStage.extensionProjection K (finiteSepField K Ω s) (FieldLimit.finiteField K Ω s)
        p at h
  calc
    _ = (standardStageProjection K Ω p s ≫
        SeparableStage.extensionProjection K (finiteSepField K Ω s) (FieldLimit.finiteField K Ω
          s) p) ≫
          eS.hom := by simp only [reversePureProjection, standardStageProjection, Category.assoc,
            eS]
    _ = (separableStageProjection K Ω p s ≫ eS.inv) ≫ eS.hom := congrArg (fun t ↦ t ≫ eS.hom) h.symm
    _ = _ := by
      rw [Category.assoc, eS.inv_hom_id]
      exact Category.comp_id (separableStageProjection K Ω p s)

theorem reversePureProjection_isEquivalence (s : Finset Ω) :
    (baseChange (reversePureProjection K Ω p s)).IsEquivalence := by
  let d := SeparableStage.extensionProjection K (finiteSepField K Ω s) (FieldLimit.finiteField K
    Ω s) p
  let : (baseChange d).IsEquivalence :=
    SeparableStage.extensionProjection_isEquivalence K (finiteSepField K Ω s)
      (FieldLimit.finiteField K Ω s) p
  apply PurelyInseparable.Global.baseChange_isEquivalence_of_isoSquare
    (pullbackSymmetry p (Spec.algebraMap K (FieldLimit.finiteField K Ω s)))
    (pullbackSymmetry p (Spec.algebraMap K (finiteSepField K Ω s)))
    (reversePureProjection K Ω p s) d
  simp only [reversePureProjection, Iso.hom_inv_id_assoc]
  rfl

/-- The canonical identification of successive base change through the separable stage with
geometric base change of `U`. -/
def separableFieldBaseChangeIso (s : Finset Ω) (U : Scheme.FiniteEtale X) :
    (baseChange (separableStageProjection K Ω p s)).obj
        ((baseChange (separableStageCover K Ω p s).obj.hom).obj U) ≅
      (baseChange (pullback.fst p (Spec.algebraMap K Ω))).obj U :=
  ObjectProperty.isoMk _
    (FieldCoverDescent.overCompIso (separableStageCover K Ω p s).obj.hom
      (separableStageProjection K Ω p s) (pullback.fst p (Spec.algebraMap K Ω))
      (geometricStageRight_snd _ _ _ _) U.obj)

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- A morphism between geometric pullbacks descends to a finite SEPARABLE
field stage, with the original literal pullback comparison equation. -/
theorem exists_separable_field_cover_hom (U V : Scheme.FiniteEtale X)
    (q : (baseChange (pullback.fst p (Spec.algebraMap K Ω))).obj U ⟶
      (baseChange (pullback.fst p (Spec.algebraMap K Ω))).obj V) :
    ∃ (s : Finset Ω)
      (g : (baseChange (separableStageCover K Ω p s).obj.hom).obj U ⟶
        (baseChange (separableStageCover K Ω p s).obj.hom).obj V),
      (baseChange (separableStageProjection K Ω p s)).map g ≫
          (separableFieldBaseChangeIso K Ω p s V).hom =
        (separableFieldBaseChangeIso K Ω p s U).hom ≫ q := by
  obtain ⟨s, gE, hgE⟩ := FieldCoverDescent.exists_finite_field_cover_hom K Ω p U V q
  let a := (separableStageCover K Ω p s).obj.hom
  let d := reversePureProjection K Ω p s
  let k := ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom
  let c := FieldLimit.fieldProjection K Ω p (op s)
  let b := separableStageProjection K Ω p s
  let π := pullback.fst p (Spec.algebraMap K Ω)
  have hda : d ≫ a = k := reversePureProjection_base K Ω p s
  have hcd : c ≫ d = b := fieldProjection_reversePureProjection K Ω p s
  have hba : b ≫ a = π := geometricStageRight_snd _ _ _ _
  have hck : c ≫ k = π := FieldLimit.fieldProjection_base K Ω p (op s)
  let ε (W : Scheme.FiniteEtale X) := FieldCoverDescent.overCompIso a d k hda W.obj
  let P (W : Scheme.FiniteEtale X) := FieldCoverDescent.overCompIso k c π hck W.obj
  let Q (W : Scheme.FiniteEtale X) := FieldCoverDescent.overCompIso a b π hba W.obj
  let η (W : Scheme.FiniteEtale X) := FieldCoverDescent.overCompIso d c b hcd
    ((Over.pullback a).obj W.obj)
  have H (W : Scheme.FiniteEtale X) : (Over.pullback c).map (ε W).hom ≫ (P W).hom =
      (η W).hom ≫ (Q W).hom :=
    FieldCoverDescent.overCompIso_assoc a d c k b π hda hcd hba hck W.obj
  let : (baseChange d).IsEquivalence := reversePureProjection_isEquivalence K Ω p s
  let qE : (baseChange d).obj ((baseChange a).obj U) ⟶
      (baseChange d).obj ((baseChange a).obj V) :=
    ObjectProperty.homMk ((ε U).hom ≫ gE.hom ≫ (ε V).inv)
  let g : (baseChange a).obj U ⟶ (baseChange a).obj V :=
    (baseChange d).preimage qE
  have hg : (baseChange d).map g = qE := Functor.map_preimage _ _
  have hg' : (Over.pullback d).map g.hom ≫ (ε V).hom = (ε U).hom ≫ gE.hom := by
    have hh := congrArg (fun t ↦ t.hom) hg
    change (Over.pullback d).map g.hom = (ε U).hom ≫ gE.hom ≫ (ε V).inv at hh
    rw [hh]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hgc := congrArg (Over.pullback c).map hg'
  rw [Functor.map_comp, Functor.map_comp] at hgc
  have hE : (Over.pullback c).map gE.hom ≫ (P V).hom = (P U).hom ≫ q.hom :=
    congrArg (fun t ↦ t.hom) hgE
  have hn := FieldCoverDescent.overCompIso_naturality d c b hcd g.hom
  change (Over.pullback c).map ((Over.pullback d).map g.hom) ≫ (η V).hom =
    (η U).hom ≫ (Over.pullback b).map g.hom at hn
  refine ⟨s, g, ?_⟩
  apply ObjectProperty.hom_ext
  change (Over.pullback b).map g.hom ≫ (Q V).hom = (Q U).hom ≫ q.hom
  apply (cancel_epi (η U).hom).mp
  calc
    (η U).hom ≫ ((Over.pullback b).map g.hom ≫ (Q V).hom) =
        ((Over.pullback c).map ((Over.pullback d).map g.hom) ≫ (η V).hom) ≫ (Q V).hom := by
      rw [hn, Category.assoc]
    _ = (Over.pullback c).map ((Over.pullback d).map g.hom) ≫
        ((Over.pullback c).map (ε V).hom ≫ (P V).hom) := by
      rw [Category.assoc, ← H V]
    _ = ((Over.pullback c).map (ε U).hom ≫ (Over.pullback c).map gE.hom) ≫ (P V).hom := by
      rw [← Category.assoc, hgc]
    _ = (Over.pullback c).map (ε U).hom ≫ ((P U).hom ≫ q.hom) := by
      rw [Category.assoc, hE]
    _ = ((η U).hom ≫ (Q U).hom) ≫ q.hom := by rw [← Category.assoc, H U]
    _ = (η U).hom ≫ ((Q U).hom ≫ q.hom) := Category.assoc _ _ _

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ea91084810164fc5cc8d1ea5704cbc2422d60bcd89875da6987edb25d08bb655.
Definitions, hypotheses and universes are retained modulo native names. -/
