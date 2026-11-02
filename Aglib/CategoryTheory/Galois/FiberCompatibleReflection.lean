/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Galois.FiberCompatible
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Reflection of Galoisness through the original deck map -/

@[expose] public noncomputable section

namespace CategoryTheory.PreGaloisCategory

universe c h d j v

variable {C : Type c} [Category.{h} C] [GaloisCategory C]
  {D : Type d} [Category.{j} D] [GaloisCategory D]
  (F : C ⥤ FintypeCat.{v}) [FiberFunctor F]
  (G : D ⥤ FintypeCat.{v}) [FiberFunctor G]
  (T : C ⥤ D) (e : F ≅ T ⋙ G)
  (Y : C) [IsConnected Y] [IsGalois (T.obj Y)]

include e in
/-- Lift transitivity through the actual surjective map on deck transformations. -/
theorem isGalois_of_fiberCompatible_of_mapAut_surjective
    (h : Function.Surjective (Functor.mapAut Y T)) : IsGalois Y := by
  apply (isGalois_iff_pretransitive F Y).mpr
  constructor
  intro x y
  let ε := compatibleFiberEquiv F G T e Y
  obtain ⟨τ, hτ⟩ := (evaluation_aut_bijective_of_isGalois G (T.obj Y)
    (ε x)).surjective (ε y)
  obtain ⟨σ, rfl⟩ := h τ
  refine ⟨σ, ε.injective ?_⟩
  exact (compatibleFiberEquiv_mapAut F G T e Y σ x).trans hτ

include e in
/-- Full faithfulness supplies precisely the required original deck preimages. -/
theorem isGalois_of_fiberCompatible_of_fullyFaithful [T.Full] [T.Faithful] :
    IsGalois Y := by
  apply isGalois_of_fiberCompatible_of_mapAut_surjective F G T e Y
  intro τ
  refine ⟨T.preimageIso τ, ?_⟩
  apply Iso.ext
  exact T.map_preimage τ.hom

include e in
/-- Reflection preserves the order of the original deck groups. -/
theorem card_aut_of_fiberCompatible_of_mapAut_surjective
    (h : Function.Surjective (Functor.mapAut Y T)) :
    Nat.card (Aut Y) = Nat.card (Aut (T.obj Y)) := by
  let : IsGalois Y := isGalois_of_fiberCompatible_of_mapAut_surjective F G T e Y h
  exact (card_aut_obj_of_fiberCompatible F G T e Y).symm

end CategoryTheory.PreGaloisCategory
