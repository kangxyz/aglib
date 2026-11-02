/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes
public import Aglib.AlgebraicGeometry.Descent.FiniteType.EventualClosedImmersion

/-! # Closed arrows of the original finite-presentation models

The native model comparison transports the original closed immersion to its
literal limit base change. The existing eventual-closed-immersion theorem then
makes the very same stage arrow closed after one rebase. No replacement
embedding or immersion certificate is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FinitePresentationDescent.Model.Map

universe u

variable {S S₀ Z W : Scheme.{u}} {π : S ⟶ S₀} {t : Z ⟶ S} {s : W ⟶ S}
  {M : Model π t} {N : Model π s} {m : Over.mk t ⟶ Over.mk s}

/-- The literal base-first arrow of a model map of an original closed
immersion is itself closed. -/
theorem isClosedImmersion_baseChange (a : Map M N m) [IsClosedImmersion m.left] :
    IsClosedImmersion (Scheme.baseChangeOverHom π a.hom) := by
  have h : ((Over.pullback π).map a.hom).left =
      M.overIso.hom.left ≫ m.left ≫ N.overIso.inv.left := by
    apply (cancel_mono N.overIso.hom.left).mp
    have hnat := congrArg Over.Hom.left a.overIso_naturality
    simpa only [Over.comp_left, Category.assoc, ← Over.comp_left,
      Iso.inv_hom_id, Over.id_left, Category.comp_id] using hnat
  let : IsIso M.overIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map M.overIso.hom))
  let : IsIso N.overIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget S).map N.overIso.inv))
  let : IsClosedImmersion ((Over.pullback π).map a.hom).left := by
    rw [h]
    infer_instance
  rw [Scheme.baseChangeOverHom_eq_overPullback]
  infer_instance

/-- The same actual model arrow becomes a closed immersion at a later stage.
All original comparison maps and the original arrow are retained. -/
theorem exists_rebase_isClosedImmersion
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {Z W : Scheme.{u}} {t : Z ⟶ c.pt} {s : W ⟶ c.pt}
    {M : Model (c.π.app i) t} {N : Model (c.π.app i) s}
    {m : Over.mk t ⟶ Over.mk s} (a : Map M N m) [IsClosedImmersion m.left] :
    ∃ j : Over i, IsClosedImmersion (a.rebase D c i j).hom.left := by
  let : CompactSpace M.X := QuasiCompact.compactSpace_of_compactSpace M.f
  let : CompactSpace N.X := QuasiCompact.compactSpace_of_compactSpace N.f
  let : QuasiSeparatedSpace M.X := quasiSeparatedSpace_of_quasiSeparated M.f
  let : QuasiSeparatedSpace N.X := quasiSeparatedSpace_of_quasiSeparated N.f
  let : LocallyOfFiniteType (a.hom.left ≫ N.f) := by
    have hw : a.hom.left ≫ N.f = M.f := a.hom.w
    rw [hw]
    infer_instance
  let : LocallyOfFiniteType a.hom.left := locallyOfFiniteType_of_comp a.hom.left N.f
  let : IsClosedImmersion (Scheme.baseChangeOverHom (c.π.app i) a.hom) :=
    a.isClosedImmersion_baseChange
  let : CompactSpace (Over.mk M.f).left := ‹CompactSpace M.X›
  let : CompactSpace (Over.mk N.f).left := ‹CompactSpace N.X›
  let : QuasiSeparatedSpace (Over.mk M.f).left := ‹QuasiSeparatedSpace M.X›
  let : QuasiSeparatedSpace (Over.mk N.f).left := ‹QuasiSeparatedSpace N.X›
  obtain ⟨j, hj⟩ := Scheme.exists_isClosedImmersion_baseChangeOverHom_of_isLimit D c hc i a.hom
  refine ⟨j, ?_⟩
  rw [Scheme.baseChangeOverHom_eq_overPullback] at hj
  rw [← Category.assoc] at hj
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsClosedImmersion) _ _).mp
    ((MorphismProperty.cancel_right_of_respectsIso (@IsClosedImmersion) _ _).mp hj)

/-- Finitely many original closed model arrows become closed at one common
stage. The source and target models are rebased, never replaced, and the
empty family is included by the cofiltered finite-cone construction. -/
theorem exists_common_rebase_isClosedImmersion
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type*} [Finite J] {Z W : J → Scheme.{u}}
    {t : ∀ j, Z j ⟶ c.pt} {s : ∀ j, W j ⟶ c.pt}
    {M : ∀ j, Model (c.π.app i) (t j)} {N : ∀ j, Model (c.π.app i) (s j)}
    {m : ∀ j, Over.mk (t j) ⟶ Over.mk (s j)} (a : ∀ j, Map (M j) (N j) (m j))
    [∀ j, IsClosedImmersion (m j).left] :
    ∃ k : Over i, ∀ j, IsClosedImmersion ((a j).rebase D c i k).hom.left := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose k hk using fun j => (a j).exists_rebase_isClosedImmersion D c hc i
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let q (j : J) : l ⟶ k j := (hl (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  refine ⟨l, fun j => ?_⟩
  have hj : IsClosedImmersion
      ((Over.pullback (D.map (k j).hom)).map (a j).hom).left := hk j
  have hiter : IsClosedImmersion
      ((Over.pullback (D.map (q j).left)).map
        ((Over.pullback (D.map (k j).hom)).map (a j).hom)).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
      (D.map (q j).left) ((Over.pullback (D.map (k j).hom)).map (a j).hom) hj
  let e := Over.pullbackComp (D.map (q j).left) (D.map (k j).hom)
  have hleft : IsIso (e.hom.app (Over.mk (M j).f)).left :=
    inferInstanceAs (IsIso ((Over.forget (D.obj l.left)).map
      (e.hom.app (Over.mk (M j).f))))
  have hright : IsIso (e.inv.app (Over.mk (N j).f)).left :=
    inferInstanceAs (IsIso ((Over.forget (D.obj l.left)).map
      (e.inv.app (Over.mk (N j).f))))
  have he : ((Over.pullback (D.map (q j).left ≫ D.map (k j).hom)).map
      (a j).hom).left =
      (e.hom.app (Over.mk (M j).f)).left ≫
        ((Over.pullback (D.map (q j).left)).map
          ((Over.pullback (D.map (k j).hom)).map (a j).hom)).left ≫
        (e.inv.app (Over.mk (N j).f)).left := by
    have hnat : (Over.pullback (D.map (q j).left ≫ D.map (k j).hom)).map
        (a j).hom = e.hom.app (Over.mk (M j).f) ≫
        (Over.pullback (D.map (q j).left)).map
          ((Over.pullback (D.map (k j).hom)).map (a j).hom) ≫
        e.inv.app (Over.mk (N j).f) := by
      apply (cancel_mono (e.hom.app (Over.mk (N j).f))).mp
      simp only [Category.assoc, Iso.inv_hom_id_app]
      exact e.hom.naturality (a j).hom
    exact congrArg Over.Hom.left hnat
  have hclosed : IsClosedImmersion
      ((Over.pullback (D.map (q j).left ≫ D.map (k j).hom)).map (a j).hom).left := by
    rw [he]
    exact MorphismProperty.comp_mem (@IsClosedImmersion) _ _ inferInstance
      (MorphismProperty.comp_mem (@IsClosedImmersion) _ _ hiter inferInstance)
  have hbase : D.map (q j).left ≫ D.map (k j).hom = D.map l.hom := by
    rw [← D.map_comp, Over.w (q j)]
  exact (congrArg (fun b : D.obj l.left ⟶ D.obj i =>
    IsClosedImmersion ((Over.pullback b).map (a j).hom).left) hbase).mp hclosed

end AlgebraicGeometry.Scheme.FinitePresentationDescent.Model.Map
