/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverMorphisms
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalExplicitDescent

/-! Explicit base-change comparison maps used to keep all finite stages in one index. -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two successive pullbacks, compared using a specified equality of composites. -/
def overCompIso {A B T : Scheme.{u}} (a : B ⟶ A) (b : T ⟶ B) (c : T ⟶ A)
    (h : b ≫ a = c) (U : Over A) :
    (Over.pullback b).obj ((Over.pullback a).obj U) ≅ (Over.pullback c).obj U :=
  Over.isoMk (pullbackLeftPullbackSndIso U.hom a b ≪≫ pullback.congrHom rfl h)
    (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)] theorem overCompIso_hom_fst
    {A B T : Scheme.{u}} (a : B ⟶ A) (b : T ⟶ B) (c : T ⟶ A)
    (h : b ≫ a = c) (U : Over A) :
    (overCompIso a b c h U).hom.left ≫ pullback.fst U.hom c =
      pullback.fst (pullback.snd U.hom a) b ≫ pullback.fst U.hom a := by
  subst c
  simp [overCompIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)] theorem overCompIso_hom_snd
    {A B T : Scheme.{u}} (a : B ⟶ A) (b : T ⟶ B) (c : T ⟶ A)
    (h : b ≫ a = c) (U : Over A) :
    (overCompIso a b c h U).hom.left ≫ pullback.snd U.hom c =
      pullback.snd (pullback.snd U.hom a) b := Over.w _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] theorem overCompIso_naturality
    {A B T : Scheme.{u}} (a : B ⟶ A) (b : T ⟶ B) (c : T ⟶ A)
    (h : b ≫ a = c) {U V : Over A} (q : U ⟶ V) :
    (Over.pullback b).map ((Over.pullback a).map q) ≫ (overCompIso a b c h V).hom =
      (overCompIso a b c h U).hom ≫ (Over.pullback c).map q := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [Over.pullback_map_left, Category.assoc]
  · exact (Over.w _).trans (Over.w _).symm

/-- Natural comparison for successive actual pullback functors. -/
def overCompNatIso {A B T : Scheme.{u}} (a : B ⟶ A) (b : T ⟶ B) (c : T ⟶ A)
    (h : b ≫ a = c) : Over.pullback a ⋙ Over.pullback b ≅ Over.pullback c :=
  NatIso.ofComponents (overCompIso a b c h) (fun q ↦ overCompIso_naturality a b c h q)

section GeneralLimit
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  (i : I) (U V : Over (D.obj i))
  [CompactSpace U.left] [QuasiSeparatedSpace U.left]
  [LocallyOfFinitePresentation V.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Actual Hom descent above the fixed original stage, with both endpoints base changed. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem tail_overHom_of_hom
    (q : (Over.pullback (c.π.app i)).obj U ⟶ (Over.pullback (c.π.app i)).obj V)
    (j : Over i) (a : pullback (D.map j.hom) U.hom ⟶ V.left)
    (ha : a ≫ V.hom = pullback.snd (D.map j.hom) U.hom ≫ U.hom)
    (hqa : ((tailSourceCone D c i U).π.app j).left ≫ a =
      (pullbackSymmetry (c.π.app i) U.hom).hom ≫ q.left ≫ pullback.fst V.hom (c.π.app i)) :
    ∃ (g : (Over.pullback (D.map j.hom)).obj U ⟶
      (Over.pullback (D.map j.hom)).obj V),
      (Over.pullback (c.π.app j.left)).map g ≫
          (overCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) V).hom =
        (overCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) U).hom ≫ q := by
  let e := pullbackSymmetry (c.π.app i) U.hom
  let z := e.hom ≫ q.left ≫ pullback.fst V.hom (c.π.app i)
  let ej := pullbackSymmetry U.hom (D.map j.hom)
  let g : (Over.pullback (D.map j.hom)).obj U ⟶
      (Over.pullback (D.map j.hom)).obj V :=
    Over.homMk (pullback.lift (ej.hom ≫ a) (pullback.snd U.hom (D.map j.hom)) (by
      rw [Category.assoc, ha, pullbackSymmetry_hom_comp_snd_assoc, pullback.condition]))
  refine ⟨g, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, overCompIso_hom_fst]
    change ((Over.pullback (c.π.app j.left)).map g).left ≫
        pullback.fst (pullback.snd V.hom (D.map j.hom)) (c.π.app j.left) ≫
          pullback.fst V.hom (D.map j.hom) =
      (overCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) U).hom.left ≫
        q.left ≫ pullback.fst V.hom (c.π.app i)
    have hgmap : ((Over.pullback (c.π.app j.left)).map g).left ≫
        pullback.fst (pullback.snd V.hom (D.map j.hom)) (c.π.app j.left) =
      pullback.fst (pullback.snd U.hom (D.map j.hom)) (c.π.app j.left) ≫ g.left :=
      pullback.lift_fst _ _ _
    rw [← Category.assoc, hgmap, Category.assoc]
    change pullback.fst (pullback.snd U.hom (D.map j.hom)) (c.π.app j.left) ≫
        (pullback.lift (ej.hom ≫ a) (pullback.snd U.hom (D.map j.hom)) _ ≫
          pullback.fst V.hom (D.map j.hom)) = _
    rw [pullback.lift_fst]
    have H : (overCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) U).hom.left ≫
        e.inv ≫ ((tailSourceCone D c i U).π.app j).left =
      pullback.fst (pullback.snd U.hom (D.map j.hom)) (c.π.app j.left) ≫ ej.hom := by
      apply pullback.hom_ext <;>
        simp [tailSourceCone, tailSourceDiagram, Cone.overPost, Over.pullback_map_left,
          e, ej, Category.assoc, pullback.condition]
    calc
      _ = (overCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) U).hom.left ≫
          e.inv ≫ ((tailSourceCone D c i U).π.app j).left ≫ a := by
            simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ a) H.symm
      _ = _ := by rw [hqa]; simp
  · exact (Over.w _).trans (Over.w _).symm
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hc in
/-- Actual Hom descent above the fixed original stage, with both endpoints base changed. -/
theorem exists_tail_overHom
    (q : (Over.pullback (c.π.app i)).obj U ⟶ (Over.pullback (c.π.app i)).obj V) :
    ∃ (j : Over i) (g : (Over.pullback (D.map j.hom)).obj U ⟶
      (Over.pullback (D.map j.hom)).obj V),
      (Over.pullback (c.π.app j.left)).map g ≫
          (overCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) V).hom =
        (overCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) U).hom ≫ q := by
  let e := pullbackSymmetry (c.π.app i) U.hom
  let z := e.hom ≫ q.left ≫ pullback.fst V.hom (c.π.app i)
  have hq : q.left ≫ pullback.snd V.hom (c.π.app i) =
      pullback.snd U.hom (c.π.app i) := Over.w q
  have hz : z ≫ V.hom = pullback.snd (c.π.app i) U.hom ≫ U.hom := by
    dsimp [z]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc q.left,
      hq, ← Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.condition]
  obtain ⟨j, a, ha, hqa⟩ := exists_tail_hom D c hc i U V z hz
  obtain ⟨g, hg⟩ := tail_overHom_of_hom D c i U V q j a ha hqa
  exact ⟨j, g, hg⟩

end GeneralLimit
end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 9b72a7d38b44b7d843eb5650e1a03f574775e42b018a1be8b052c41b69cbf7f6.
Definitions, hypotheses and universes are retained modulo native names. -/
