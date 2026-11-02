/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Generators.GlobalSections

/-!
# Global generation after restriction with section lifting

For an actual map `φ : F ⟶ M` and a scheme morphism `i`, surjectivity on global
sections of `φ` and of the original restriction unit at `M` implies
surjectivity on global sections of `i^* φ`. If the actual target `i^* M` is
globally generated, the original pulled-back map is therefore an epimorphism.
No hypothesis on the morphism `i`, finiteness or local freeness is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X E : Scheme.{u}} (i : E ⟶ X) {F M : X.Modules} (φ : F ⟶ M)

/-- Section surjectivity and lifting through the actual restriction unit give
surjectivity on sections of the original pulled-back morphism. -/
theorem pullback_app_top_surjective_of_unit_app_top_surjective
    (hφ : Function.Surjective (φ.val.app (op ⊤)))
    (hunit : Function.Surjective
      (((pullbackPushforwardAdjunction i).unit.app M).val.app (op ⊤))) :
    Function.Surjective (((pullback i).map φ).val.app (op ⊤)) := by
  intro s
  obtain ⟨m, hm⟩ := hunit s
  obtain ⟨v, hv⟩ := hφ m
  refine ⟨((pullbackPushforwardAdjunction i).unit.app F).val.app (op ⊤) v, ?_⟩
  have hn := congrArg (fun k => k.val.app (op ⊤) v)
    ((pullbackPushforwardAdjunction i).unit.naturality φ)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  refine hn.symm.trans ?_
  exact (congrArg (((pullbackPushforwardAdjunction i).unit.app M).val.app (op ⊤)) hv).trans hm

/-- Generation of the actual restriction target turns section lifting into
epimorphy of the original restricted map. -/
theorem epi_pullback_of_sections_and_unit_surjective
    (hφ : Function.Surjective (φ.val.app (op ⊤)))
    (hunit : Function.Surjective
      (((pullbackPushforwardAdjunction i).unit.app M).val.app (op ⊤)))
    [Epi (globalSectionsEval ((pullback i).obj M))] :
    Epi ((pullback i).map φ) :=
  epi_of_unitHom_factor _
    (exists_unitHom_factor_of_surjective _
      (pullback_app_top_surjective_of_unit_app_top_surjective i φ hφ hunit))

end AlgebraicGeometry.Scheme.Modules
