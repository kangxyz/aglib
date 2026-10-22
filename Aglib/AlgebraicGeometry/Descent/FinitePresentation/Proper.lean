/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ProperModification
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Separated
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.WeakAffine

/-!
# Proper arithmetic stages

A finite-type qcqs stage morphism whose pullback to the limit is proper
is proper after a later transition, when the stage bases are Noetherian
affine schemes. The limit base is unrestricted. The modification required
in the proof is constructed by weak Chow, not supplied as a hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
  [∀ i, IsLocallyNoetherian (D.obj i)] (c : Cone D) (hc : IsLimit c)

include hc in
/-- The separated finite-type case of eventual properness, with weak Chow
constructed over the original affine stage. -/
theorem exists_isProper_baseChange_of_isLimit_of_isSeparated (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsProper (pullback.fst (c.π.app i) f)] :
    ∃ j : Over i, IsProper (pullback.fst (D.map j.hom) f) := by
  have {j k : I} (r : j ⟶ k) : IsAffineHom (D.map r) := inferInstance
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have : LocallyOfFiniteType (Over.mk f).hom := inferInstanceAs (LocallyOfFiniteType f)
  have : QuasiCompact (Over.mk f).hom := inferInstanceAs (QuasiCompact f)
  obtain ⟨Y, P, p, q, hp, hs, hq, hP⟩ :=
    Chow.exists_immersion_proper_modification (Over.mk f)
  let := hp
  let := hs
  let := hq
  let := hP
  have : IsProper ((Over.pullback (c.π.app i)).obj (Over.mk f)).hom := by
    change IsProper (pullback.snd f (c.π.app i))
    rw [← pullbackSymmetry_hom_comp_fst f (c.π.app i)]
    infer_instance
  obtain ⟨j, hj⟩ := exists_isProper_overPullback_of_modification D c hc i p q
  have : IsProper (pullback.snd f (D.map j.hom)) := hj
  refine ⟨j, ?_⟩
  rw [← pullbackSymmetry_hom_comp_snd (D.map j.hom) f]
  infer_instance

include hc in
/-- Properness descends to an actual later arithmetic stage. No flatness,
injectivity, or Noetherian hypothesis is imposed on the limiting base. -/
theorem exists_isProper_baseChange_of_isLimit (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
    [IsProper (pullback.fst (c.π.app i) f)] :
    ∃ j : Over i, IsProper (pullback.fst (D.map j.hom) f) := by
  have {j k : I} (r : j ⟶ k) : IsAffineHom (D.map r) := inferInstance
  obtain ⟨j, hj⟩ := exists_isSeparated_baseChange_of_isLimit D c hc i f
  let := hj
  let E : Over j.left ⥤ Scheme.{u} := Over.forget j.left ⋙ D
  let d : Cone E := c.whisker (Over.forget j.left)
  have hd : IsLimit d := (Functor.Initial.isLimitWhiskerEquiv (Over.forget j.left) c).symm hc
  have (k : Over j.left) : IsAffine (E.obj k) := inferInstanceAs (IsAffine (D.obj k.left))
  have (k : Over j.left) : IsLocallyNoetherian (E.obj k) :=
    inferInstanceAs (IsLocallyNoetherian (D.obj k.left))
  let k₀ : Over j.left := Over.mk (𝟙 j.left)
  let f' : pullback (D.map j.hom) f ⟶ E.obj k₀ := pullback.fst (D.map j.hom) f
  have : IsProper (pullback.fst (d.π.app k₀) f') := by
    change IsProper (pullback.fst (c.π.app j.left) (pullback.fst (D.map j.hom) f))
    rw [← (isPullback_baseChangeCone D c i f j).flip.isoPullback_inv_fst]
    infer_instance
  obtain ⟨k, hk⟩ := exists_isProper_baseChange_of_isLimit_of_isSeparated E d hd k₀ f'
  change IsProper (pullback.fst (D.map k.hom.left) (pullback.fst (D.map j.hom) f)) at hk
  let := hk
  refine ⟨Over.mk (k.hom.left ≫ j.hom), ?_⟩
  change IsProper (pullback.fst (D.map (k.hom.left ≫ j.hom)) f)
  rw [D.map_comp, ← pullbackRightPullbackFstIso_inv_fst (D.map j.hom) f (D.map k.hom.left)]
  infer_instance

end AlgebraicGeometry.Scheme
