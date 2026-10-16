/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Partial and transported nullhomotopies of module complexes

These ordinary cochain constructions require no perfectness. A homotopy
identity above a degree and a supplied lower zero-term bound give an actual
nullhomotopy. Actual natural isomorphisms transport nullhomotopies, and exact
open restriction preserves acyclicity.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalHomotopyStep.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `c8b9d1747230f9415b9c1ad06766bdc61e6282892879088c2ac394fe7d68836f`.
Selected declaration ranges: 44–47.
Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalNullHomotopy.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `cc23fba72767c558490cb186c433ddfc9cffd0858baca40544082563b33b8067`.
Selected declaration ranges: 41–45, 48–57, 61–73.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex.HomComplex
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

variable {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}

/-- The componentwise homotopy identity holds in degrees strictly above n. -/
def HomotopyAbove (f : K ⟶ L) (α : Cochain K L (-1)) (n : ℤ) : Prop :=
  ∀ p : ℤ, n < p → f.f p =
    α.v p (p - 1) (by omega) ≫ L.d (p - 1) p +
      K.d p (p + 1) ≫ α.v (p + 1) p (by omega)

theorem acyclic_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K : CochainComplex X.Modules ℤ} (hK : K.Acyclic) : ((restrict j).obj K).Acyclic := by
  intro n
  change ((K.sc n).map (Scheme.Modules.restrictFunctor j)).Exact
  exact (show (K.sc n).Exact from hK n).map (Scheme.Modules.restrictFunctor j)

/-- A natural isomorphism of functors transports actual nullhomotopies. -/
def nullHomotopyOfNatIso {X Y : Scheme.{u}} {F G : CochainComplex X.Modules ℤ
    ⥤ CochainComplex Y.Modules ℤ}
    (e : F ≅ G) {K L : CochainComplex X.Modules ℤ} {f : K ⟶ L}
    (h : Homotopy (F.map f) 0) : Homotopy (G.map f) 0 := by
  have he : G.map f = (e.inv.app K ≫ F.map f) ≫ e.hom.app L := by
    rw [Category.assoc, e.hom.naturality]
    simp
  exact (Homotopy.ofEq he).trans
    (((h.compLeft (e.inv.app K)).compRight (e.hom.app L)).trans
      (Homotopy.ofEq (by simp)))

/-- Once the approximation is correct down to the lower bound of the
source, it is an actual chain homotopy to zero. -/
def nullHomotopyOfAbove {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (α : Cochain K L (-1)) (a : ℤ)
    (hα : HomotopyAbove f α (a - 1)) (hb : ∀ p : ℤ, p < a → IsZero (K.X p)) :
    Homotopy f 0 := by
  refine (Cochain.equivHomotopy f 0).symm ⟨α, ?_⟩
  rw [Cochain.ofHom_zero, add_zero]
  apply Cochain.ext₀
  intro p
  rw [δ_v (-1) 0 (by simp) α p p (by simp) (p - 1) (p + 1) rfl rfl]
  simp only [Cochain.ofHom_v, Int.negOnePow_zero, one_smul]
  by_cases hp : a ≤ p
  · exact hα p (by omega)
  · exact (hb p (by omega)).eq_of_src _ _

end AlgebraicGeometry.Scheme.Modules.Complex
