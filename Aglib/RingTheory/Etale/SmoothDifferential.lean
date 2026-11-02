/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Etaleness from equal smooth differential ranks

The original Jacobi-Zariski maps prove formal etaleness of an unramified
algebra map when the source and target differential modules over a common
base are finite free of equal rank and the target is formally smooth over
that base. No flatness premise for the map is used.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Nontrivial B] [FormallyUnramified A B]
  [Module.Free A Ω[A⁄R]] [Module.Finite A Ω[A⁄R]]
  [Module.Free B Ω[B⁄R]] [Module.Finite B Ω[B⁄R]]

/-- The actual differential base-change map is bijective for an unramified
map between finite free differential modules of equal rank. -/
theorem mapBaseChange_bijective_of_formallyUnramified_of_finrank_eq
    (h : Module.finrank A Ω[A⁄R] = Module.finrank B Ω[B⁄R]) :
    Function.Bijective (KaehlerDifferential.mapBaseChange R A B) := by
  let : Nontrivial A := (algebraMap A B).domain_nontrivial
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
    (LinearMap.surjective_iff_eq_zero_of_exact
      (KaehlerDifferential.exact_mapBaseChange_map R A B)).mpr
        (by ext x; exact Subsingleton.elim _ _)
  apply OrzechProperty.bijective_of_surjective_of_finrank_le _ hs
  rw [Module.finrank_baseChange, h]

/-- Equal finite free differential ranks and formal smoothness over the
common base upgrade formal unramifiedness to formal etaleness. -/
theorem formallyEtale_of_formallyUnramified_of_finrank_eq
    [FormallySmooth R B]
    (h : Module.finrank A Ω[A⁄R] = Module.finrank B Ω[B⁄R]) :
    FormallyEtale A B := by
  have hd : H1Cotangent.δ R A B = 0 :=
    (LinearMap.injective_iff_eq_zero_of_exact
      (H1Cotangent.exact_δ_mapBaseChange R A B)).mp
        (mapBaseChange_bijective_of_formallyUnramified_of_finrank_eq R A B h).injective
  have hi : Function.Injective (H1Cotangent.δ R A B) :=
    (LinearMap.injective_iff_eq_zero_of_exact (H1Cotangent.exact_map_δ R A B)).mpr
      (LinearMap.ext fun x => by rw [Subsingleton.elim x 0]; exact map_zero _)
  have : Subsingleton (H1Cotangent A B) :=
    ⟨fun x y => hi (by rw [hd]; rfl)⟩
  exact ⟨inferInstance, inferInstance⟩

end Algebra
