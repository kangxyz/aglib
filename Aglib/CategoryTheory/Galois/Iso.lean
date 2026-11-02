/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Galois.GaloisObjects

/-! # Galoisness under an actual object isomorphism

The native `Aut.autMulEquivOfIso` is the only deck-group transport used.
-/

@[expose] public noncomputable section

namespace CategoryTheory.PreGaloisCategory

universe c h v

variable {C : Type c} [Category.{h} C]

/-- Connectedness transports through the supplied original object isomorphism. -/
theorem isConnected_of_iso {X Y : C} (e : X ≅ Y) [IsConnected X] : IsConnected Y where
  notInitial h := IsConnected.notInitial (h.ofIso e.symm)
  noTrivialComponent Z i _ h := by
    let : IsIso (i ≫ e.inv) := IsConnected.noTrivialComponent Z (i ≫ e.inv) h
    have hi : i = (i ≫ e.inv) ≫ e.hom := by simp
    rw [hi]
    infer_instance

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{v}) [FiberFunctor F]

include F

/-- Conjugation by the original isomorphism transports Galoisness. -/
theorem isGalois_of_iso {X Y : C} (e : X ≅ Y) [IsGalois X] : IsGalois Y := by
  let : IsConnected Y := isConnected_of_iso e
  apply (isGalois_iff_pretransitive F Y).mpr
  constructor
  intro x y
  let ε : F.obj X ≃ F.obj Y := FintypeCat.equivEquivIso.symm (F.mapIso e)
  obtain ⟨σ, hσ⟩ := (evaluation_aut_bijective_of_isGalois F X (ε.symm x)).surjective (ε.symm y)
  refine ⟨Aut.autMulEquivOfIso e σ, ?_⟩
  change F.map (e.inv ≫ σ.hom ≫ e.hom) x = y
  simp only [Functor.map_comp, FintypeCat.comp_apply]
  change ε (F.map σ.hom (ε.symm x)) = y
  exact (congrArg ε hσ).trans (ε.apply_symm_apply y)

end CategoryTheory.PreGaloisCategory
