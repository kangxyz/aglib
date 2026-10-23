/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.FiniteCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Strata
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.DominantDetection
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Actual reduced integral strata for constructible coefficients

A constructible coefficient on a Noetherian scheme admits a finite covering
family of integral locally closed schemes with finite locally constant original
restrictions. The pieces are the actual reduced induced closed schemes of the
topological irreducible components of the original locally closed strata.
Native nonreduced component schemes are not identified with these pieces.

Dominant field points of these integral pieces jointly detect maps into the
original coefficient. The field points and all inverse images remain literal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u

attribute [local instance] hasSheafifyLarge

/-- The actual vanishing ideal of the given topological irreducible component. -/
def reducedComponentIdeal (S : Scheme.{u}) (Z : irreducibleComponents S) :
    S.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨Z.val, isClosed_of_mem_irreducibleComponents Z.val Z.property⟩

/-- The reduced induced scheme of the given actual irreducible component. -/
def reducedComponent (S : Scheme.{u}) (Z : irreducibleComponents S) : Scheme.{u} :=
  (reducedComponentIdeal S Z).subscheme

/-- The original closed subscheme map of the reduced component. -/
def reducedComponentι (S : Scheme.{u}) (Z : irreducibleComponents S) :
    reducedComponent S Z ⟶ S :=
  (reducedComponentIdeal S Z).subschemeι

/-- Reducedness follows on the original quotient affine cover. -/
theorem reducedComponent_isReduced (S : Scheme.{u}) (Z : irreducibleComponents S) :
    IsReduced (reducedComponent S Z) := by
  let I := reducedComponentIdeal S Z
  have hred (U : S.affineOpens) :
      IsReduced (I.subschemeCover.openCover.X U) := by
    have hrad : (I.ideal U).IsRadical := by
      change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' Z.val)).IsRadical
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    have : _root_.IsReduced (Γ(S, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp hrad
    change IsReduced (Spec (.of (Γ(S, U) ⧸ I.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover I.subscheme I.subschemeCover.openCover hred

/-- The actual reduced component is integral, without Noetherianity. -/
theorem reducedComponent_isIntegral (S : Scheme.{u}) (Z : irreducibleComponents S) :
    IsIntegral (reducedComponent S Z) := by
  have : IsReduced (reducedComponent S Z) := reducedComponent_isReduced S Z
  have : IrreducibleSpace (reducedComponent S Z) := Subtype.irreducibleSpace Z.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The original reduced component map has exactly the specified component image. -/
theorem reducedComponentι_range (S : Scheme.{u}) (Z : irreducibleComponents S) :
    Set.range (reducedComponentι S Z) = Z.val :=
  (reducedComponentIdeal S Z).range_subschemeι

/-- A finite covering family of actual integral locally closed schemes with
finite locally constant restrictions of the original coefficient. -/
structure FiniteIntegralLocallyClosedCover {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) where
  /-- The index lies in the original scheme universe. -/
  index : Type u
  /-- There are finitely many pieces. -/
  finite_index : Finite index
  /-- The actual integral locally closed schemes. -/
  stratum : index → Scheme.{u}
  /-- Their original maps to the base. -/
  inclusion : ∀ i, stratum i ⟶ X
  /-- Each map is an actual locally closed immersion. -/
  immersion : ∀ i, IsImmersion (inclusion i)
  /-- Each actual piece is integral and hence reduced. -/
  integral : ∀ i, IsIntegral (stratum i)
  /-- The original images cover every point of the base. -/
  covers : ∀ x : X, ∃ i, ∃ y : stratum i, inclusion i y = x
  /-- The coefficient restrictions are the original inverse images. -/
  locally_constant : ∀ i, IsFiniteLocallyConstant ((inverseImage (inclusion i)).obj F)

/-- Reduce the irreducible components of the already produced finite locally
closed cover; the original restrictions and covering maps are retained. -/
def finiteIntegralLocallyClosedCover {X : Scheme.{u}} [IsNoetherian X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F) :
    FiniteIntegralLocallyClosedCover F := by
  let t := finiteLocallyClosedCover F hF
  have : Finite t.index := t.finite_index
  have (i : t.index) : IsImmersion (t.inclusion i) := t.immersion i
  have (i : t.index) : NoetherianSpace (t.stratum i) :=
    (t.inclusion i).isEmbedding.isInducing.noetherianSpace
  have (i : t.index) : Finite (irreducibleComponents (t.stratum i)) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      (α := t.stratum i)).to_subtype
  refine {
    index := Σ i : t.index, irreducibleComponents (t.stratum i)
    finite_index := inferInstance
    stratum := fun q => reducedComponent (t.stratum q.1) q.2
    inclusion := fun q => reducedComponentι (t.stratum q.1) q.2 ≫ t.inclusion q.1
    immersion := ?_
    integral := fun q => reducedComponent_isIntegral (t.stratum q.1) q.2
    covers := ?_
    locally_constant := ?_ }
  · intro q
    have : IsClosedImmersion (reducedComponentι (t.stratum q.1) q.2) :=
      inferInstanceAs (IsClosedImmersion (reducedComponentIdeal (t.stratum q.1) q.2).subschemeι)
    infer_instance
  · intro x
    obtain ⟨i, y, hy⟩ := t.covers x
    let Z : irreducibleComponents (t.stratum i) :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    have hr : y ∈ Set.range (reducedComponentι (t.stratum i) Z) := by
      rw [reducedComponentι_range]
      exact mem_irreducibleComponent
    obtain ⟨z, hz⟩ := hr
    exact ⟨⟨i, Z⟩, z, (congrArg (t.inclusion i) hz).trans hy⟩
  · intro q
    exact (isFiniteLocallyConstant_iff_of_iso
      ((inverseImageComp (t.inclusion q.1) (reducedComponentι (t.stratum q.1) q.2)).app F)).mpr
        (isFiniteLocallyConstant_pullback (reducedComponentι (t.stratum q.1) q.2)
          (t.locally_constant q.1))

namespace FiniteIntegralLocallyClosedCover

variable {X : Scheme.{u}} {F : AbelianSheaf.{u, u + 1} X}
  (t : FiniteIntegralLocallyClosedCover F)

/-- The actual integral stratum inverse images are jointly faithful. -/
theorem jointlyFaithful_inverseImages :
    JointlyFaithful (fun i => inverseImage (t.inclusion i)) := by
  have (i : t.index) : IsImmersion (t.inclusion i) := t.immersion i
  exact jointlyFaithful_immersionInverseImages t.stratum t.inclusion t.covers

/-- Original pullback to dominant field points of the integral covering
strata detects equality of maps into the original constructible coefficient. -/
theorem fieldPoint_inverseImages_map_injective
    (K : t.index → Type u) [∀ i, Field (K i)]
    (ζ : ∀ i, Spec (.of (K i)) ⟶ t.stratum i) [∀ i, IsDominant (ζ i)]
    (G : AbelianSheaf.{u, u + 1} X) :
    Function.Injective (fun a : G ⟶ F =>
      fun i => (inverseImage (ζ i ≫ t.inclusion i)).map a) := by
  intro a b hab
  apply t.jointlyFaithful_inverseImages.map_injective
  intro i
  have : IsIntegral (t.stratum i) := t.integral i
  apply inverseImage_map_injective_of_finiteLocallyConstant_of_isDominant (ζ i)
    ((inverseImage (t.inclusion i)).obj F) (t.locally_constant i)
    ((inverseImage (t.inclusion i)).obj G)
  let e := inverseImageComp (t.inclusion i) (ζ i)
  apply (cancel_epi (e.hom.app G)).mp
  calc
    e.hom.app G ≫ (inverseImage (ζ i)).map ((inverseImage (t.inclusion i)).map a) =
        (inverseImage (ζ i ≫ t.inclusion i)).map a ≫ e.hom.app F :=
      (e.hom.naturality a).symm
    _ = (inverseImage (ζ i ≫ t.inclusion i)).map b ≫ e.hom.app F :=
      congrArg (fun k => k ≫ e.hom.app F) (congrFun hab i)
    _ = e.hom.app G ≫ (inverseImage (ζ i)).map ((inverseImage (t.inclusion i)).map b) :=
      e.hom.naturality b

end FiniteIntegralLocallyClosedCover
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
