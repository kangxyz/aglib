/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.StrictHenselianBaseChangeSection
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootSectionDescent
public import Aglib.RingTheory.Henselian.StrictHenselization.RootPoint
public import Aglib.RingTheory.Henselian.StrictHenselization.SeparablyClosedResidue
public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteLocalFactors

/-! # The specified original root-cover point through strict base change

The original field point evaluates both literal roots at zero. Its complete
root-change triangle constructs the needed geometric point, and the actual
finite local root algebra is strictly Henselian. The resulting section and
its specified original value descend through the original root-stage cone.
No colimit domain, Noetherianity or faithful flatness is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
  [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
  (N : ℕ) (hN : 0 < N) (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)

local notation "C" => GeometricEtaleColimit R Ω
local notation "T" => RootAlgebra N f
local notation "S" => RootAlgebra N (algebraMap R C f)

/-- Construct the original root-cover lift through the specified point using
the original chosen field and the literal strict-local root algebra. -/
theorem exists_rootColimit_lift_through_closedPoint
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of T)) [IsFinite p] [Etale p] :
    letI : IsLocalRing T := parameterRoot_isLocalRing R f hf N hN
    letI : IsLocalRing S := GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
    ∀ y : Z, p y = IsLocalRing.closedPoint T →
    ∃ a : Spec (.of S) ⟶ Z,
      a ≫ p = Spec.map (CommRingCat.ofHom (rootBaseChangeHom C N f).toRingHom) ∧
      a (IsLocalRing.closedPoint S) = y := by
  let : IsLocalRing T := parameterRoot_isLocalRing R f hf N hN
  let : IsLocalRing S := GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
  let : Module.Finite C S := root_finite N hN (algebraMap R C f)
  let : HenselianLocalRing S := HenselianLocalRing.of_finite_local_algebra C S
  let : IsSepClosed (IsLocalRing.ResidueField S) :=
    HenselianLocalRing.residueField_isSepClosed_of_finite_local_algebra C S
  let : IsLocalHom (GeometricEtaleColimit.rootPoint R Ω N hN f hf).toRingHom :=
    GeometricEtaleColimit.rootPoint_isLocalHom R Ω N hN f hf
  let : IsLocalHom (Algebra.Kummer.rootPoint R Ω N hN f hf).toRingHom :=
    Algebra.Kummer.rootPoint_isLocalHom R Ω N hN f hf
  let u := Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.rootPoint R Ω N hN f hf).toRingHom)
  let u₀ := Spec.map (CommRingCat.ofHom (Algebra.Kummer.rootPoint R Ω N hN f hf).toRingHom)
  let g := Spec.map (CommRingCat.ofHom (rootBaseChangeHom C N f).toRingHom)
  have hd : (default : Spec (.of Ω)) = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  have hu : u default = IsLocalRing.closedPoint S := by
    rw [hd]
    exact AlgebraicGeometry.Spec_closedPoint
  have hu₀ : u₀ default = IsLocalRing.closedPoint T := by
    rw [hd]
    exact AlgebraicGeometry.Spec_closedPoint
  have hsq : u ≫ g = u₀ := by
    dsimp only [u, g, u₀]
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom
      (GeometricEtaleColimit.rootPoint_comp R Ω N hN f hf))
  have hg : g (IsLocalRing.closedPoint S) = IsLocalRing.closedPoint T := by
    have h := congrArg (fun q : Spec (.of Ω) ⟶ Spec (.of T) => q default) hsq
    change g (u default) = u₀ default at h
    rwa [hu, hu₀] at h
  intro y hy
  exact FiniteEtale.exists_lift_through_closedPoint_of_strictHenselian S Ω p g u hu y
    (hy.trans hg.symm)

/-- The constructed pointed lift reaches a genuine etale neighborhood after
any prescribed stage, with both original structural and comparison equations. -/
theorem exists_rootStage_lift_through_closedPoint
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of T)) [IsFinite p] [Etale p]
    (X₀ : GeometricEtaleNeighborhood R Ω) :
    letI : IsLocalRing T := parameterRoot_isLocalRing R f hf N hN
    letI : IsLocalRing S := GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
    ∀ y : Z, p y = IsLocalRing.closedPoint T →
    ∃ a : Spec (.of S) ⟶ Z,
      a ≫ p = Spec.map (CommRingCat.ofHom (rootBaseChangeHom C N f).toRingHom) ∧
      a (IsLocalRing.closedPoint S) = y ∧
      ∃ (Y : GeometricEtaleNeighborhood R Ω) (_ : X₀ ⟶ Y)
        (b : (rootDiagram R Ω N f).obj (op Y) ⟶ Z),
        b ≫ p = (rootStructure R Ω N f).app (op Y) ∧
        (rootCone R Ω N f).π.app (op Y) ≫ b = a := by
  let : IsLocalRing T := parameterRoot_isLocalRing R f hf N hN
  let : IsLocalRing S := GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
  intro y hy
  obtain ⟨a, ha, hay⟩ := exists_rootColimit_lift_through_closedPoint R Ω N hN f hf p y hy
  exact ⟨a, ha, hay, exists_rootStage_lift R Ω N f p a ha X₀⟩

end AlgebraicGeometry.Scheme.Kummer
