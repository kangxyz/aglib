/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverGroupQuotients
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverSheafPoint

/-! Actual geometric-point fibres preserve the constructed finite-group
quotients. The argument factors through the left-adjoint sheaf-point functor
and reflects colimits through the fully faithful finite-type universe lift. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleH1

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)

universe u
variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X)

theorem coverFiber_preservesSmallFiniteGroupQuotients (hRV : Stacks03RV X)
    (G : Type) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (fiberToFinite s) := by
  let := coverSectionSheaf_preservesSmallFiniteGroupQuotients hRV G
  have : PreservesColimitsOfShape (SingleObj G)
      (fiberToFinite s ⋙ FintypeCat.incl ⋙ uliftFunctor.{u + 1}) :=
    preservesColimitsOfShape_of_natIso (coverSheafPointFiberIso s)
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (fiberToFinite s) (FintypeCat.incl ⋙ uliftFunctor.{u + 1})

theorem coverFiber_preservesFiniteGroupQuotients (hRV : Stacks03RV X)
    (G : Type u) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (fiberToFinite s) := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  let := coverFiber_preservesSmallFiniteGroupQuotients s hRV G'
  exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm _

/-- The frozen geometric reflection theorem supplies this exact dictionary,
without any Galois-category assumption. -/
theorem coverFiber_reflectsIsomorphisms [ConnectedSpace X] :
    (fiberToFinite s).ReflectsIsomorphisms where
  reflects f := isIso_of_bijective_fiber s f (ConcreteCategory.bijective_of_isIso _)

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 52c8e3d3acc01c8c07527afc772e93f7afa32c4ff521c41fec75c38a5ab0bb58.
Definitions, hypotheses and universes are retained modulo native names. -/
