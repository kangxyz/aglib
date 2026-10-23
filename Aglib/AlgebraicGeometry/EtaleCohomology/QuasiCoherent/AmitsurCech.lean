/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AmitsurExactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AmitsurProducts

/-! # The original singleton spectrum Čech complex is exact in positive degree -/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Apply a coefficient to an opposite diagram comparison before specializing its objects. -/
def rightOpSectionsIso {C D E A : Type*} [Category* C] [Category* D]
    [Category* E] [Category* A] (F : C ⥤ D) (G : Dᵒᵖ ⥤ E)
    (N : Cᵒᵖ ⥤ E) (e : F.op ⋙ G ≅ N) (P : Eᵒᵖ ⥤ A) :
    F ⋙ G.rightOp ⋙ P ≅ N.rightOp ⋙ P := by
  let e' : (F.op ⋙ G).rightOp ≅ N.rightOp := {
    hom := e.inv.rightOp
    inv := e.hom.rightOp
    hom_inv_id := by rw [← NatTrans.rightOp_comp, e.hom_inv_id, NatTrans.rightOp_id]
    inv_hom_id := by rw [← NatTrans.rightOp_comp, e.inv_hom_id, NatTrans.rightOp_id] }
  exact Functor.isoWhiskerRight e' P

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (F : (Spec (CommRingCat.of R)).Modules) [F.IsQuasicoherent]

/-- The original Amitsur sections are the sections of the actual singleton Čech nerve. -/
def amitsurCechSectionsIso : amitsurSections R F S ≅
    (cechNerveTerminalFrom ((algSpec (CommRingCat.of R)).obj
      (op (CommAlgCat.of R S)))).rightOp ⋙ additiveSectionsPresheaf (Spec (.of R)) F :=
  rightOpSectionsIso (Algebra.Amitsur.conerve R S) (algSpec (CommRingCat.of R))
    _ (amitsurSpecCechIso R S) (additiveSectionsPresheaf (Spec (.of R)) F)

/-- Faithfully flat affine singleton covers have exact original section Čech complexes. -/
theorem spectrumCech_exactAt_succ [Module.FaithfullyFlat R S] (n : ℕ) :
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj
      ((cechNerveTerminalFrom ((algSpec (CommRingCat.of R)).obj
        (op (CommAlgCat.of R S)))).rightOp ⋙
          additiveSectionsPresheaf (Spec (.of R)) F)).ExactAt (n + 1) :=
  (amitsurSectionsComplex_exactAt_succ R F S n).of_iso
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).mapIso
      (amitsurCechSectionsIso R S F))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
