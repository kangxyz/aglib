/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.FiniteResolution
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain.NormalizedPresentation

/-!
# Literal normalized resolution from genuine original initial cones

The existing ordinary chain is transported through its explicit terminal
isomorphism. Regularity, proper birational geometry and every original
regular-open isomorphism are retained without identifying the constructed
ordinary and normalized schemes.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing Localization.Away
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint

/-- Honest initial full cones over an earlier complete base yield a literal
normalized-point chain with regular terminal, proper birational original map,
and an isomorphism over every original regular open. -/
theorem exists_regular_normalizedPointBlowupChain_of_initial_cones_of_complete_base
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsNagataRing.{u, 0} R) (hdR : ringKrullDim R = 2)
    (hRat : NormalModificationH1Vanishing R)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsDominant f]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hcones : ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
      ∃ (t : maximalIdeal (X.presheaf.stalk x))
        (g : Fin 2 → maximalIdeal (X.presheaf.stalk x))
        (q : MvPolynomial (Fin 3) (ResidueField (X.presheaf.stalk x))),
        Ideal.span (Set.range fun i =>
          (CaseOne.orderedGenerators t g i : X.presheaf.stalk x)) =
            maximalIdeal (X.presheaf.stalk x) ∧
        q ≠ 0 ∧ q.IsHomogeneous 2 ∧
        RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q})
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (hdA : ringKrullDim A = 2)
    (a : A →+* R) [IsLocalHom a]
    (hinj : Function.Injective a) (hres : (ResidueField.map a).Finite) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (_ : NormalizedPointBlowupChain g),
      IsProper g ∧ IsIntegral Y ∧ IsDominant g ∧ BirationalOver g (𝟙 X) ∧
      RegularStalks Y ∧
      ∀ U : X.Opens, (∀ x : X, x ∈ U → IsRegularLocalRing (X.presheaf.stalk x)) →
        IsIso (g ∣_ U) := by
  obtain ⟨T, k, c, hT, hnormal, hopen⟩ :=
    exists_regular_pointBlowupChain_of_initial_cones_of_complete_base
      R hR hdR hRat f hX hff hcones A hdA a hinj hres
  obtain ⟨Y, g, d, E, _hlen, hE⟩ := c.exists_normalizedPresentation inferInstance hnormal
  have hEg : E.inv ≫ k = g := by
    calc
      E.inv ≫ k = E.inv ≫ (E.hom ≫ g) := congrArg (fun h : T ⟶ X => E.inv ≫ h) hE.symm
      _ = g := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsProper k := c.isProper inferInstance
  have hproper : IsProper g :=
    Eq.mp (congrArg (fun h : Y ⟶ X => IsProper h) hEg)
      (inferInstance : IsProper (E.inv ≫ k))
  have hbir : BirationalOver g (𝟙 X) :=
    (E.inv.birationalOver k g hEg).trans (c.birationalOver inferInstance)
  refine ⟨Y, g, d, hproper, d.isIntegral inferInstance, d.isDominant inferInstance,
    hbir, hT.of_isOpenImmersion E.inv, ?_⟩
  intro U hU
  let : IsIso (k ∣_ U) := hopen U hU
  have hcomposite : IsIso ((E.inv ≫ k) ∣_ U) := by
    have hi : IsIso ((E.inv ∣_ k ⁻¹ᵁ U) ≫ (k ∣_ U)) := inferInstance
    exact Eq.mpr (congrArg
      (fun h : ((E.inv ≫ k) ⁻¹ᵁ U).toScheme ⟶ U.toScheme => IsIso h)
      (morphismRestrict_comp E.inv k U)) hi
  exact Eq.mp (congrArg (fun h : Y ⟶ X => IsIso (h ∣_ U)) hEg) hcomposite

end AlgebraicGeometry.Scheme.RationalDoublePoint
