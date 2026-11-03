/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Finite.Trace
public import Aglib.AlgebraicGeometry.Cohomology.Proper.ScalarTorsion
public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber
public import Aglib.AlgebraicGeometry.Surfaces.Birational.FiniteDomination
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Regular

/-!
# Uniform original structure-H1 bounds under finite separable extension

One fixed trace discriminant, chosen before all models, combines the actual
finite dominating diagram, original cohomology maps and fixed scalar-torsion
bound. The bound is transferred from the original lower ring, rather than
assumed for the upper models. The original residue degree is retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.FiniteTraceCoordinates

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- A single natural length bound for the original structural cohomology of
every supplied normal proper birational integral model. -/
def NormalModificationH1Bounded (A : Type u) [CommRing A] [IsDomain A] : Prop :=
  ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f],
    NormalStalks X → IsIso (CommRingCat.ofHom (functionFieldMap f)) →
      letI := moduleCohomologyModuleOfHom X (FiniteTraceCoordinates.structureScalar f)
        (structureModule X) 1
      Module.length A (Sheaf.H.{u + 1} (moduleAddSheaf X (structureModule X)) 1) ≤
        (N : ℕ∞)

private theorem finiteExtension_discriminant_nonzero
    (A B : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [FaithfulSMul A B] [IsIntegrallyClosed A]
    (hsep : letI := baseMapDominant A B
      letI := functionFieldMapAlgebra (baseMap A B)
      Algebra.IsSeparable (spectrumField A) (spectrumField B)) :
    fixedDiscriminant A B ≠ 0 ∧ algebraMap A B (fixedDiscriminant A B) ≠ 0 := by
  let := spectrumFieldAlgebra A
  let := spectrumFieldAlgebra B
  let := spectrumFieldFractionRing A
  let := spectrumFieldFractionRing B
  let := baseMapDominant A B
  let := baseFieldAlgebra A B
  let := upperFieldAlgebra A B
  let := upperFieldTower A B
  let := baseFieldTower A B
  let : Algebra.IsSeparable (spectrumField A) (spectrumField B) := hsep
  have hd : fixedDiscriminant A B ≠ 0 :=
    Algebra.TraceLattice.discriminant_ne_zero A B (spectrumField A) (spectrumField B)
  refine ⟨hd, ?_⟩
  intro hz
  exact hd (FaithfulSMul.algebraMap_injective A B
    (hz.trans (algebraMap A B).map_zero.symm))

private theorem finiteExtension_functionFieldMap_finite
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    (functionFieldMap f).Finite := by
  let q := pullback.snd f (Y.fromSpecStalk (genericPoint Y))
  let : IsIso (Scheme.genericFibreMap f) := Scheme.genericFibreMap_isIso f
  have hfinite : IsFinite (Scheme.genericFibreMap f ≫ q) := inferInstance
  have hcomp : Scheme.genericFibreMap f ≫ q =
      Spec.map (CommRingCat.ofHom (functionFieldMap f)) := by
    dsimp only [q, Scheme.genericFibreMap]
    exact pullback.lift_snd _ _ _
  rw [hcomp] at hfinite
  exact (IsFinite.SpecMap_iff _).mp hfinite

private theorem finiteExtension_structureScalar_comp
    {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (h : Y ⟶ X) (f : X ⟶ Spec (.of A)) :
    FiniteTraceCoordinates.structureScalar (h ≫ f) =
      h.appTop.hom.comp (FiniteTraceCoordinates.structureScalar f) := by
  simp only [FiniteTraceCoordinates.structureScalar, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_assoc]

private theorem finiteExtension_structureH1_length_le
    {B : Type u} [CommRing B] {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y]
    (h : Y ⟶ T) [IsProper h] [IsDominant h]
    (hT : NormalStalks T)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap h)))
    (α : B →+* Γ(T, ⊤)) (β : B →+* Γ(Y, ⊤))
    (hβ : β = h.appTop.hom.comp α) :
    letI := moduleCohomologyModuleOfHom T α (structureModule T) 1
    letI := moduleCohomologyModuleOfHom Y β (structureModule Y) 1
    Module.length B (Sheaf.H.{u + 1} (moduleAddSheaf T (structureModule T)) 1) ≤
      Module.length B (Sheaf.H.{u + 1} (moduleAddSheaf Y (structureModule Y)) 1) := by
  subst β
  let := moduleCohomologyModuleOfHom T α (structureModule T) 1
  let := moduleCohomologyModuleOfHom Y (h.appTop.hom.comp α) (structureModule Y) 1
  exact Module.length_le_of_injective
    (moduleCohomologyMapAlongLinear h α
      (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) 1)
    (moduleCohomologyMapAlongLinear_unit_injective_of_isProper_birational T α h hT hff)

/-- Universal original-model vanishing gives the uniform bound zero. -/
theorem normalModificationH1Bounded_of_vanishing
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : RationalSingularities.NormalModificationH1Vanishing A) :
    NormalModificationH1Bounded A := by
  refine ⟨0, ?_⟩
  intro X hX f hf hd hN hff
  let := moduleCohomologyModuleOfHom X (FiniteTraceCoordinates.structureScalar f)
        (structureModule X) 1
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X (structureModule X)) 1) :=
    hA X f hN hff
  exact (Module.length_eq_zero (R := A)).le

/-- Uniform H1 boundedness transfers along the original finite separable
local algebra, using one fixed trace discriminant and original residue degree. -/
theorem normalModificationH1Bounded_of_finite_separable
    (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsLocalRing B]
    [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]
    [IsLocalHom (algebraMap A B)]
    (hNagA : IsNagataRing.{u, 0} A) (hNagB : IsNagataRing.{u, 0} B)
    (hdimA : ringKrullDim A = 2) (hdimB : ringKrullDim B = 2)
    (hsep : letI := baseMapDominant A B
      letI := functionFieldMapAlgebra (baseMap A B)
      Algebra.IsSeparable (spectrumField A) (spectrumField B))
    (hboundA : NormalModificationH1Bounded A) : NormalModificationH1Bounded B := by
  obtain ⟨N_A, hN_A⟩ := hboundA
  obtain ⟨_, hdB⟩ := finiteExtension_discriminant_nonzero A B hsep
  let d := fixedDiscriminant A B
  obtain ⟨N_d, hN_d⟩ := exists_uniform_structureH1_scalarTorsion_length_bound
    B hNagB hdimB (algebraMap A B d) hdB
  let e : ℕ := Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  have he : Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) =
      (e : ℕ∞) := Module.length_eq_finrank _ _
  refine ⟨N_d * e + degree A B * N_A, ?_⟩
  intro T hT g hgproper hgdom hTN hgff
  let : IsIntegral T := hT
  let : IsProper g := hgproper
  let : IsDominant g := hgdom
  let s := baseMap A B
  let : IsDominant s := baseMapDominant A B
  let : IsFinite s := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite A B))
  obtain ⟨X, Y, hIX, hIY, rest⟩ :=
    Birational.FiniteDomination.exists_finite_domination A B
      (FaithfulSMul.algebraMap_injective A B) s rfl hdimA.le hNagA
      (finiteExtension_functionFieldMap_finite s) g hgff
  let : IsIntegral X := hIX
  let : IsIntegral Y := hIY
  obtain ⟨a, b, π, h, ha, hb, hh, rest⟩ := rest
  let : IsDominant a := ha
  let : IsDominant b := hb
  let : IsDominant h := hh
  obtain ⟨hXN, hYN, haproper, hbproper, hhproper, hπfinite, hπdom,
    haff, hbff, hhff, hbg, hsq⟩ := rest
  let : IsProper a := haproper
  let : IsProper b := hbproper
  let : IsProper h := hhproper
  let : IsFinite π := hπfinite
  let : IsDominant π := hπdom
  let := moduleCohomologyModuleOfHom X (FiniteTraceCoordinates.structureScalar a)
    (structureModule X) 1
  let := moduleCohomologyModuleOfHom Y (FiniteTraceCoordinates.structureScalar b)
    (structureModule Y) 1
  let := moduleCohomologyModuleOfHom T (FiniteTraceCoordinates.structureScalar g)
    (structureModule T) 1
  have hscalar : FiniteTraceCoordinates.structureScalar b =
      h.appTop.hom.comp (FiniteTraceCoordinates.structureScalar g) :=
    (congrArg (fun z => FiniteTraceCoordinates.structureScalar z) hbg).symm.trans
      (finiteExtension_structureScalar_comp h g)
  have hTY := finiteExtension_structureH1_length_le h hTN hhff
    (FiniteTraceCoordinates.structureScalar g) (FiniteTraceCoordinates.structureScalar b) hscalar
  have htrace := finiteTraceCohomology_length_le A B π hXN a b haff hbff hsq 1
  have hbase := hN_A X a hXN haff
  have htorsion := hN_d b hbff hYN
  calc
    Module.length B (Sheaf.H.{u + 1} (moduleAddSheaf T (structureModule T)) 1) ≤
        Module.length B (Sheaf.H.{u + 1} (moduleAddSheaf Y (structureModule Y)) 1) := hTY
    _ ≤ Module.length B
          (Submodule.torsionBy B
            (Sheaf.H.{u + 1} (moduleAddSheaf Y (structureModule Y)) 1) (algebraMap A B d)) *
            Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) +
          (degree A B : ℕ∞) *
            Module.length A (Sheaf.H.{u + 1} (moduleAddSheaf X (structureModule X)) 1) :=
      htrace
    _ ≤ (N_d : ℕ∞) * (e : ℕ∞) + (degree A B : ℕ∞) * (N_A : ℕ∞) := by
      rw [he]
      exact add_le_add (mul_le_mul' htorsion le_rfl) (mul_le_mul' le_rfl hbase)
    _ = ((N_d * e + degree A B * N_A : ℕ) : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]

/-- A regular local surface has a zero uniform original-model H1 bound. -/
theorem normalModificationH1Bounded_of_regularLocal
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2) :
    letI : IsDomain A := IsRegularLocalRing.isDomain_of_regularLocal A
    NormalModificationH1Bounded A := by
  let : IsDomain A := IsRegularLocalRing.isDomain_of_regularLocal A
  exact normalModificationH1Bounded_of_vanishing A
    (RationalSingularities.normalModificationH1Vanishing_of_regularLocal A hd)

end AlgebraicGeometry.Scheme.Cohomology
