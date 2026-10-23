/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Conerve
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Spectra of the original Amitsur conerve are the actual Čech powers

The native wide algebraic pushout is a coproduct because the base algebra is
initial. Applying the original `algSpec` functor gives the categorical products
in `Over (Spec R)`, with the original indexed projections and all simplicial maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The original algebraic Amitsur inclusions, viewed as an opposite product cone. -/
def amitsurTermFan (n : ℕ) :
    Fan (fun _ : Fin (n + 1) => op (CommAlgCat.of R S)) :=
  Fan.mk (op (Algebra.Amitsur.term R S n)) (fun i => (Algebra.Amitsur.ι R S n i).op)

/-- The original wide pushout over the initial base algebra is a coproduct. -/
def amitsurTermFanIsLimit (n : ℕ) : IsLimit (amitsurTermFan R S n) := by
  refine Fan.IsLimit.mk _
    (fun c => (WidePushout.desc (CommAlgCat.isInitialSelf.to c.pt.unop)
      (fun i => (c.proj i).unop) (fun _ => CommAlgCat.isInitialSelf.hom_ext _ _)).op) ?_ ?_
  · intro c i
    apply Quiver.Hom.unop_inj
    exact WidePushout.ι_desc _ _ _ _ _
  · intro c f hf
    apply Quiver.Hom.unop_inj
    apply Algebra.Amitsur.term_hom_ext
    intro i
    calc
      _ = (c.proj i).unop := congrArg Quiver.Hom.unop (hf i)
      _ = _ := (WidePushout.ι_desc
        (fun _ : Fin (n + 1) => (Algebra.Amitsur.unitArrow R S).hom)
        (CommAlgCat.isInitialSelf.to c.pt.unop)
        (fun j : Fin (n + 1) => (c.proj j).unop)
        (fun _ => CommAlgCat.isInitialSelf.hom_ext _ _) i).symm

/-- The original spectrum factors form an actual limiting product cone over `Spec R`. -/
def amitsurSpecFanIsLimit (n : ℕ) :
    IsLimit (Fan.mk
      ((algSpec (CommRingCat.of R)).obj (op (Algebra.Amitsur.term R S n)))
      (fun i : Fin (n + 1) =>
        (algSpec (CommRingCat.of R)).map (Algebra.Amitsur.ι R S n i).op)) := by
  letI : PreservesLimitsOfSize.{0, 0} (algSpec (CommRingCat.of R)) :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec
  exact isLimitFanMkObjOfIsLimit (algSpec (CommRingCat.of R))
    (fun _ : Fin (n + 1) => op (CommAlgCat.of R S))
    (fun i => (Algebra.Amitsur.ι R S n i).op)
    (amitsurTermFanIsLimit R S n)

/-- The actual spectrum of each original conerve term is its categorical Čech power. -/
def amitsurSpecProductIso (n : ℕ) :
    (algSpec (CommRingCat.of R)).obj (op (Algebra.Amitsur.term R S n)) ≅
      ∏ᶜ fun _ : Fin (n + 1) =>
        (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) :=
  (amitsurSpecFanIsLimit R S n).conePointUniqueUpToIso (productIsProduct _)

/-- The product comparison retains every original indexed algebra factor. -/
@[reassoc (attr := simp)]
theorem amitsurSpecProductIso_hom_π (n : ℕ) (i : Fin (n + 1)) :
    (amitsurSpecProductIso R S n).hom ≫ Pi.π _ i =
      (algSpec (CommRingCat.of R)).map (Algebra.Amitsur.ι R S n i).op :=
  (amitsurSpecFanIsLimit R S n).conePointUniqueUpToIso_hom_comp (productIsProduct _) ⟨i⟩

/-- The original spectrum conerve is the native product Čech nerve, including all faces. -/
def amitsurSpecCechIso :
    (Algebra.Amitsur.conerve R S).op ⋙ algSpec (CommRingCat.of R) ≅
      cechNerveTerminalFrom
        ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S))) := by
  refine NatIso.ofComponents (fun n => amitsurSpecProductIso R S n.unop.len) ?_
  intro n m f
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, amitsurSpecProductIso_hom_π,
    Functor.comp_map, Functor.op_map, cechNerveTerminalFrom, Pi.lift_comp_π,
    ← Functor.map_comp, ← op_comp, Algebra.Amitsur.ι_map]

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
