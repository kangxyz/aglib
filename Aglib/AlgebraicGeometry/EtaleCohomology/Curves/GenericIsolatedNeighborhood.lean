/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinBaseChangeIndex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinBaseChange
public import Aglib.AlgebraicGeometry.Stalk.DiscreteSectionsNaturality

/-!
# Actual generic pullbacks of isolated generic neighborhoods

An open neighborhood containing only one component-generic point has at most
one generic point itself. Its actual generic pullback is consequently a
one-point Artinian scheme when nonempty, including its nilpotents. Equality
of units on that pullback can be checked at its single original stalk.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

/-- An open neighborhood isolated from other generics has at most one generic point. -/
theorem genericPoints_subsingleton_of_isolated_open {U : Scheme.{u}} (W : U.Opens)
    (η : genericPoints U) (hW : ∀ θ : genericPoints U, θ.val ∈ W → θ = η) :
    Subsingleton (genericPoints W.toScheme) := by
  constructor
  intro ξ ζ
  have hξ := hW ⟨W.ι ξ.val, genericPoint_map_flat W.ι ξ⟩ ξ.val.property
  have hζ := hW ⟨W.ι ζ.val, genericPoint_map_flat W.ι ζ⟩ ζ.val.property
  exact Subtype.ext (W.ι.isEmbedding.injective
    (congrArg (fun θ : genericPoints U => θ.val) (hξ.trans hζ.symm)))

variable {U X : Scheme.{u}} [IsNoetherian X] (f : U ⟶ X) [Etale f]
  (W : U.Opens) [QuasiCompact (W.ι ≫ f)] (η : genericPoints U)
  (hW : ∀ θ : genericPoints U, θ.val ∈ W → θ = η)

include η hW

/-- The actual whole generic pullback of the isolated neighborhood has at most one point. -/
theorem genericArtinBaseChange_subsingleton_of_isolated_open :
    Subsingleton (pullback (W.ι ≫ f) (genericArtinMap X) : Scheme.{u}) := by
  let : Subsingleton (genericPoints W.toScheme) :=
    genericPoints_subsingleton_of_isolated_open W η hW
  exact ⟨fun p q => (genericArtinBaseChangeIndexEquiv (W.ι ≫ f)).injective
    (Subsingleton.elim _ _)⟩

/-- On this actual infinitesimal pullback, one original unit germ detects equality. -/
theorem genericArtinBaseChange_units_eq_of_germ
    (p : (pullback (W.ι ≫ f) (genericArtinMap X) : Scheme.{u}))
    (a b : Γ(pullback (W.ι ≫ f) (genericArtinMap X), ⊤)ˣ)
    (h : Units.map ((pullback (W.ι ≫ f) (genericArtinMap X)).presheaf.germ
      ⊤ p trivial).hom.toMonoidHom a =
      Units.map ((pullback (W.ι ≫ f) (genericArtinMap X)).presheaf.germ
        ⊤ p trivial).hom.toMonoidHom b) : a = b := by
  let : IsArtinianScheme (pullback (W.ι ≫ f) (genericArtinMap X)) :=
    genericArtinBaseChange_isArtinian (W.ι ≫ f)
  let : Subsingleton (pullback (W.ι ≫ f) (genericArtinMap X) : Scheme.{u}) :=
    genericArtinBaseChange_subsingleton_of_isolated_open f W η hW
  apply (Scheme.globalUnits_eq_iff_germs a b).2
  intro q
  have hqp : q = p := Subsingleton.elim _ _
  subst q
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
