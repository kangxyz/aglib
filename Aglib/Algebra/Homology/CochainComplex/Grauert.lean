/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.BaseChange.Grauert

/-!
# The reduced local constant-rank criterion for original cochain homology

Local constancy of a degree's actual residue-field homology dimension gives
freeness of its original homology and invertibility of the original mate
after every ring map. Only the term in that degree must be finite, and the
next term must be finite flat. The source complex can be unbounded and the
ring need not be Noetherian. The proof specializes the native short complex;
no new homology or base-change map is defined.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Module

namespace CochainComplex

universe u v

variable {R : Type u} [CommRing R] [IsReduced R] [IsLocalRing R]

/-- Constant original degreewise fibre homology rank makes the original homology free
over a reduced local ring. Finiteness of the present term and finite flatness of the next
term suffice; no lower bound, upper bound or preceding-term finiteness is needed. -/
theorem free_homology_of_isLocallyConstant_residueField_finrank
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ)
    [Module.Finite R (K.X i)] [Module.Finite R (K.X (i + 1))]
    [Module.Flat R (K.X (i + 1))]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj K).homology i))) : Module.Free R (K.homology i) := by
  have hn : (ComplexShape.up ℤ).next i = i + 1 := (ComplexShape.up ℤ).next_eq' rfl
  let : Module.Finite R (K.sc i).X₂ := by
    change Module.Finite R (K.X i)
    infer_instance
  let : Module.Finite R (K.sc i).X₃ := by
    change Module.Finite R (K.X ((ComplexShape.up ℤ).next i))
    rw [hn]
    infer_instance
  let : Module.Flat R (K.sc i).X₃ := by
    change Module.Flat R (K.X ((ComplexShape.up ℤ).next i))
    rw [hn]
    infer_instance
  exact (K.sc i).free_homology_of_isLocallyConstant_residueField_finrank h

universe w

/-- Under the reduced local constant-rank criterion, the unchanged degreewise homology
base-change mate is invertible after every ring map, including larger target universes. -/
theorem extendScalarsHomologyMap_isIso_of_isLocallyConstant_residueField_finrank
    {B : Type w} [CommRing B] (σ : R →+* B)
    (K : CochainComplex (ModuleCat.{max u v w} R) ℤ) (i : ℤ)
    [Module.Finite R (K.X i)] [Module.Finite R (K.X (i + 1))]
    [Module.Flat R (K.X (i + 1))]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj K).homology i))) :
    IsIso (extendScalarsHomologyMap.{u, max u v, w, 0} σ K i) := by
  have hn : (ComplexShape.up ℤ).next i = i + 1 := (ComplexShape.up ℤ).next_eq' rfl
  let : Module.Finite R (K.sc i).X₂ := by
    change Module.Finite R (K.X i)
    infer_instance
  let : Module.Finite R (K.sc i).X₃ := by
    change Module.Finite R (K.X ((ComplexShape.up ℤ).next i))
    rw [hn]
    infer_instance
  let : Module.Flat R (K.sc i).X₃ := by
    change Module.Flat R (K.X ((ComplexShape.up ℤ).next i))
    rw [hn]
    infer_instance
  exact ShortComplex.homologyBaseChangeMap_isIso_of_isLocallyConstant_residueField_finrank.{u,
    v, w} σ (K.sc i) h

end CochainComplex
