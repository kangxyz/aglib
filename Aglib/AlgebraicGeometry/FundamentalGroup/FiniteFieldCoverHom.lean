/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldTransport

/-!
# Actual finite-field-stage morphisms between pulled-back finite étale covers

This interface applies the frozen tail-Hom descent to the empty original field stage.
It preserves the given covers of X and the literal field-limit projection. No object
descent or separability hypothesis is used.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
universe u

/-- Associativity of the explicit canonical comparisons, characterized by their projections. -/
@[reassoc] theorem overCompIso_assoc
    {A B C T : Scheme.{u}} (a : B ⟶ A) (b : C ⟶ B) (c : T ⟶ C)
    (ab : C ⟶ A) (bc : T ⟶ B) (d : T ⟶ A)
    (hab : b ≫ a = ab) (hbc : c ≫ b = bc) (hl : bc ≫ a = d) (hr : c ≫ ab = d)
    (W : Over A) :
    (Over.pullback c).map (overCompIso a b ab hab W).hom ≫ (overCompIso ab c d hr W).hom =
      (overCompIso b c bc hbc ((Over.pullback a).obj W)).hom ≫ (overCompIso a bc d hl W).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_obj_left, Over.pullback_obj_hom, Over.comp_left,
      Over.pullback_map_left, Category.assoc, overCompIso_hom_fst, limit.lift_π_assoc,
      PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app]
    exact (overCompIso_hom_fst_assoc b c bc hbc ((Over.pullback a).obj W)
      (pullback.fst W.hom a)).symm
  · exact (Over.w _).trans (Over.w _).symm

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K))

/-- Compare successive base change through the actual finite field stage with the
original standard-order geometric base change. -/
def fieldBaseChangeIso (s : Finset Ω) (U : Scheme.FiniteEtale X) :
    (baseChange (FieldLimit.fieldProjection K Ω p (op s))).obj
        ((baseChange ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom).obj U) ≅
      (baseChange (pullback.fst p (Spec.algebraMap K Ω))).obj U :=
  ObjectProperty.isoMk _
    (overCompIso ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom
      (FieldLimit.fieldProjection K Ω p (op s)) (pullback.fst p (Spec.algebraMap K Ω))
      (FieldLimit.fieldProjection_base K Ω p (op s)) U.obj)

@[reassoc (attr := simp)] theorem fieldBaseChangeIso_hom_fst (s : Finset Ω)
  (U : Scheme.FiniteEtale X) :
    (fieldBaseChangeIso K Ω p s U).hom.hom.left ≫
      pullback.fst U.obj.hom (pullback.fst p (Spec.algebraMap K Ω)) =
        pullback.fst (pullback.snd U.obj.hom ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom)
          (FieldLimit.fieldProjection K Ω p (op s)) ≫
        pullback.fst U.obj.hom ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom :=
  overCompIso_hom_fst _ _ _ _ _

variable [Algebra.IsAlgebraic K Ω] [CompactSpace X] [QuasiSeparatedSpace X]

/-- A morphism between the actual geometric pullbacks of two covers of a qcqs scheme
comes from a morphism between their pullbacks to one original finite field stage. -/
theorem exists_finite_field_cover_hom (U V : Scheme.FiniteEtale X)
    (q : (baseChange (pullback.fst p (Spec.algebraMap K Ω))).obj U ⟶
      (baseChange (pullback.fst p (Spec.algebraMap K Ω))).obj V) :
    ∃ (s : Finset Ω)
      (g : (baseChange ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom).obj U ⟶
        (baseChange ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom).obj V),
      (baseChange (FieldLimit.fieldProjection K Ω p (op s))).map g ≫
          (fieldBaseChangeIso K Ω p s V).hom =
        (fieldBaseChangeIso K Ω p s U).hom ≫ q := by
  let D := fieldSchemeDiagram K Ω p
  let c := standardFieldCone K Ω p
  let i : (Finset Ω)ᵒᵖ := op ∅
  let a := ((FieldLimit.schemeDiagram K Ω p).obj i).hom
  let r := pullback.fst p (Spec.algebraMap K Ω)
  let U₀ := (Over.pullback a).obj U.obj
  let V₀ := (Over.pullback a).obj V.obj
  let e (W : Scheme.FiniteEtale X) := overCompIso a (c.π.app i) r
    (FieldLimit.fieldProjection_base K Ω p i) W.obj
  let q₀ : (Over.pullback (c.π.app i)).obj U₀ ⟶
      (Over.pullback (c.π.app i)).obj V₀ := (e U).hom ≫ q.hom ≫ (e V).inv
  have : CompactSpace U₀.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd U.obj.hom a)
  have : QuasiSeparatedSpace U₀.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd U.obj.hom a)
  have : LocallyOfFinitePresentation V₀.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd V.obj.hom a))
  have {j k : (Finset Ω)ᵒᵖ} (t : j ⟶ k) : IsAffineHom (D.map t) :=
    inferInstanceAs (IsAffineHom ((FieldLimit.schemeDiagram K Ω p).map t).left)
  obtain ⟨j, g₀, hg₀⟩ := exists_tail_overHom D c (standardFieldConeIsLimit K Ω p) i U₀ V₀ q₀
  let b := D.map j.hom
  let k := ((FieldLimit.schemeDiagram K Ω p).obj j.left).hom
  let η (W : Scheme.FiniteEtale X) := overCompIso a b k
    (Over.w ((FieldLimit.schemeDiagram K Ω p).map j.hom)) W.obj
  let ε (W : Scheme.FiniteEtale X) := overCompIso k (c.π.app j.left) r
    (FieldLimit.fieldProjection_base K Ω p j.left) W.obj
  let τ (W : Scheme.FiniteEtale X) := overCompIso b (c.π.app j.left) (c.π.app i) (c.w j.hom)
    ((Over.pullback a).obj W.obj)
  have H (W : Scheme.FiniteEtale X) : (Over.pullback (c.π.app j.left)).map (η W).hom ≫ (ε W).hom =
      (τ W).hom ≫ (e W).hom := overCompIso_assoc _ _ _ _ _ _ _ _ _ _ _
  let g : (baseChange k).obj U ⟶ (baseChange k).obj V :=
    ObjectProperty.homMk ((η U).inv ≫ g₀ ≫ (η V).hom)
  refine ⟨j.left.unop, g, ?_⟩
  apply ObjectProperty.hom_ext
  change (Over.pullback (c.π.app j.left)).map ((η U).inv ≫ g₀ ≫ (η V).hom) ≫
      (ε V).hom = (ε U).hom ≫ q.hom
  simp only [Functor.map_comp, Category.assoc]
  rw [H]
  have hg : (Over.pullback (c.π.app j.left)).map g₀ ≫ (τ V).hom =
      (τ U).hom ≫ (e U).hom ≫ q.hom ≫ (e V).inv := hg₀
  rw [← Category.assoc _ (τ V).hom, hg]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc (τ U).hom (e U).hom, ← H U]
  simp

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 bc7633d3b2c65472cd359bf3c222ec4dd0cf538d828693565a42aea758bd729e.
Definitions, hypotheses and universes are retained modulo native names. -/
