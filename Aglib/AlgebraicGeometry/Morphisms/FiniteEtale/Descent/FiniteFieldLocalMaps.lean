/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverAffine
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverCharts
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverMorphisms

/-! Actual local maps in the original field system, and restriction of a descent witness. -/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange baseChangeComp)
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
universe u

/-- Restrict a cover reconstruction isomorphism along an actual commutative square. -/
def restrictDescentIso {S T U V : Scheme.{u}} (f : T ⟶ S) (a : V ⟶ U)
    (l : U ⟶ S) (r : V ⟶ T) (h : a ≫ l = r ≫ f)
    (M : Scheme.FiniteEtale S) (Y : Scheme.FiniteEtale T) (e : (baseChange f).obj M ≅ Y) :
    (baseChange a).obj ((baseChange l).obj M) ≅ (baseChange r).obj Y :=
  (baseChangeComp l a).symm.app M ≪≫
    eqToIso (congrArg (fun k ↦ (baseChange k).obj M) h) ≪≫
    (baseChangeComp f r).app M ≪≫ (baseChange r).mapIso e

section Field
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  {U V : Scheme.{u}} (pU : U ⟶ Spec (.of K)) (pV : V ⟶ Spec (.of K))
  (q : U ⟶ V) (hq : q ≫ pV = pU)

/-- The morphism between the `s`-stages of `U` and `V` induced by `q`, using
the structural equation `hq : q ≫ pV = pU`. -/
def stageMap (s : Finset Ω) :
    ((FieldLimit.schemeDiagram K Ω pU).obj (op s)).left ⟶
      ((FieldLimit.schemeDiagram K Ω pV).obj (op s)).left :=
  pullback.map (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) pU
    (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) pV
      (𝟙 _) q (𝟙 _) (by simp) (by simpa using hq.symm)

/-- The base change of `q` along `Spec Ω ⟶ Spec K`, with projections `q` and
the identity on `Spec Ω`, using `hq`. -/
def geometricMap : pullback pU (Spec.algebraMap K Ω) ⟶ pullback pV (Spec.algebraMap K Ω) :=
  pullback.map _ _ _ _ q (𝟙 _) (𝟙 _) (by simpa using hq.symm) (by simp)

@[reassoc (attr := simp)] theorem stageMap_fst (s : Finset Ω) :
    stageMap K Ω pU pV q hq s ≫
      pullback.fst (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) pV =
        pullback.fst (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) pU := by
  simp [stageMap]

@[reassoc (attr := simp)] theorem stageMap_snd (s : Finset Ω) :
    stageMap K Ω pU pV q hq s ≫
      ((FieldLimit.schemeDiagram K Ω pV).obj (op s)).hom =
        ((FieldLimit.schemeDiagram K Ω pU).obj (op s)).hom ≫ q := by
  change stageMap K Ω pU pV q hq s ≫
    pullback.snd (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) pV =
      pullback.snd (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) pU ≫ q
  simp [stageMap]

@[reassoc (attr := simp)] theorem geometricMap_fst :
    geometricMap K Ω pU pV q hq ≫ pullback.fst pV (Spec.algebraMap K Ω) =
      pullback.fst pU (Spec.algebraMap K Ω) ≫ q := by simp [geometricMap]

@[reassoc (attr := simp)] theorem geometricMap_snd :
    geometricMap K Ω pU pV q hq ≫ pullback.snd pV (Spec.algebraMap K Ω) =
      pullback.snd pU (Spec.algebraMap K Ω) := by simp [geometricMap]

@[reassoc] theorem geometricMap_projection (s : Finset Ω) :
    geometricMap K Ω pU pV q hq ≫ FieldLimit.fieldProjection K Ω pV (op s) =
      FieldLimit.fieldProjection K Ω pU (op s) ≫ stageMap K Ω pU pV q hq s := by
  apply pullback.hom_ext (f := Spec.algebraMap K (FieldLimit.finiteField K Ω s)) (g := pV)
  · simp [fieldProjection_field, Category.assoc]
  · change _ ≫ ((FieldLimit.schemeDiagram K Ω pV).obj (op s)).hom =
      _ ≫ ((FieldLimit.schemeDiagram K Ω pV).obj (op s)).hom
    simp [FieldLimit.fieldProjection_base, FieldLimit.fieldProjection_base_assoc, Category.assoc]

@[reassoc] theorem geometricMap_comp_of_triangle
    {W : Scheme.{u}} (pW : W ⟶ Spec (.of K)) (r : V ⟶ W) (hr : r ≫ pW = pV)
    (t : U ⟶ W) (ht : t ≫ pW = pU) (hqr : q ≫ r = t) :
    geometricMap K Ω pU pV q hq ≫ geometricMap K Ω pV pW r hr =
      geometricMap K Ω pU pW t ht := by
  apply pullback.hom_ext
  · simp only [Category.assoc, geometricMap_fst, geometricMap_fst_assoc]
    rw [hqr]
  · simp

end Field

section Projection
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K))

@[reassoc] theorem fieldProjection_transition {s t : (Finset Ω)ᵒᵖ} (a : s ⟶ t) :
    FieldLimit.fieldProjection K Ω p s ≫ ((FieldLimit.schemeDiagram K Ω p).map a).left =
      FieldLimit.fieldProjection K Ω p t :=
  (standardFieldCone K Ω p).w a

/-- Move one local model from its own stage to a specified larger finite subset. -/
def enlargeStage {s t : Finset Ω} (h : s ⊆ t)
    (M : Scheme.FiniteEtale (((FieldLimit.schemeDiagram K Ω p).obj (op s)).left)) :
    Scheme.FiniteEtale (((FieldLimit.schemeDiagram K Ω p).obj (op t)).left) :=
  (baseChange ((FieldLimit.schemeDiagram K Ω p).map (homOfLE h).op).left).obj M

/-- Transport the reconstruction isomorphism `e` from stage `s` to the enlarged
stage `t`, using `h : s ⊆ t` and compatibility of the field projections. -/
def enlargeStageIso {s t : Finset Ω} (h : s ⊆ t)
    (M : Scheme.FiniteEtale (((FieldLimit.schemeDiagram K Ω p).obj (op s)).left))
    (Y : Scheme.FiniteEtale (pullback p (Spec.algebraMap K Ω)))
    (e : (baseChange (FieldLimit.fieldProjection K Ω p (op s))).obj M ≅ Y) :
    (baseChange (FieldLimit.fieldProjection K Ω p (op t))).obj
      (enlargeStage K Ω p h M) ≅ Y :=
  (baseChangeComp ((FieldLimit.schemeDiagram K Ω p).map (homOfLE h).op).left
    (FieldLimit.fieldProjection K Ω p (op t))).symm.app M ≪≫
    eqToIso (congrArg (fun k ↦ (baseChange k).obj M)
      (fieldProjection_transition K Ω p (homOfLE h).op)) ≪≫ e

end Projection
end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3edb44d4b2507d4ce9f92ff281d34eb4ca1db128a825e86967c2b223360960cd.
Definitions, hypotheses and universes are retained modulo native names. -/
