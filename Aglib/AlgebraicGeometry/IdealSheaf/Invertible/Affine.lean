/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Affine
public import Aglib.RingTheory.Localization.ModulePresentation
public import Aglib.RingTheory.Ideal.RegularPrincipal
public import Aglib.RingTheory.RegularLocalRing.ArtinianQuotient
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Flat
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor

/-!
# Local bases and regular generators for actual affine ideals

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/CartierLocality.lean`, SHA-256
  `d11c4ffb39327cd751cb517541e51344ca708630381facd0620868347b548718`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open Module
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Hom

/-- A singleton basis on a principal localization supplies the actual local
free presentation of the associated sheaf. -/
def tildeBasicOpenBasisIso {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (r : R) (b : Basis PUnit.{u + 1} (Localization.Away r) (LocalizedModule.Away r M)) :
    SheafOfModules.free
        (R := (show (Spec R).Opens from PrimeSpectrum.basicOpen r).toScheme.ringCatSheaf)
        PUnit.{u + 1} ≅
      (tilde M).restrict (show (Spec R).Opens from PrimeSpectrum.basicOpen r).ι :=
  affineBasicOpenLocalizedBasisIso (tilde M) r
    (b.map (_root_.LocalizedModule.localizedModuleEquiv (.powers r) (tilde.isoTop M).toLinearEquiv))

/-- An Artinian quotient of a Noetherian affine ring whose maximal local rings
are regular of dimension one has invertible actual kernel sheaf. -/
theorem artinianQuotientIdeal_isLocallyRankOne
    {R S : CommRingCat.{u}} [IsNoetherianRing R] [IsArtinianRing S]
    (φ : R ⟶ S) (hsurj : Function.Surjective φ.hom)
    (hlocal : ∀ (P : Ideal R) [P.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime P) ∧
        ringKrullDim (Localization.AtPrime P) = 1) :
    IsLocallyRankOne (Spec R) (idealModule (Spec.map φ)) := by
  let I := RingHom.ker φ.hom
  let M := ModuleCat.of R I
  let κ := {r : R // Nonempty (Basis PUnit.{u + 1}
    (Localization.Away r) (LocalizedModule.Away r I))}
  let U : κ → (Spec R).Opens := fun r ↦ PrimeSpectrum.basicOpen r.val
  have hcov : IsOpenCover U := .mk (by
    apply top_le_iff.mp
    intro p _
    obtain ⟨r, hr, hb⟩ := _root_.Ideal.artinianQuotientIdeal_localizedBasis φ.hom hsurj hlocal p
    exact Opens.mem_iSup.mpr ⟨⟨r, hb⟩, hr⟩)
  let q := localGeneratorsOfCoverFreeIso U hcov (fun _ ↦ PUnit.{u + 1})
    (fun r ↦ tildeBasicOpenBasisIso M r.val r.property.some)
  have hM : IsLocallyRankOne (Spec R) (tilde M) :=
    ⟨q, inferInstance, fun _ ↦ ⟨Equiv.refl _⟩⟩
  exact isLocallyRankOne_of_iso (Spec R) (affineIdealIso φ) hM

/-- Local singleton bases of the ring kernel give local singleton bases of
its actual kernel sheaf. -/
theorem affineIdeal_rankOne_of_localizedBasis
    {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hb : ∀ P : PrimeSpectrum A, ∃ s : A, s ∉ P.asIdeal ∧ Nonempty
      (Basis PUnit.{u + 1} (Localization.Away s)
        (LocalizedModule.Away s (RingHom.ker φ.hom)))) :
    IsLocallyRankOne (Spec A) (idealModule (Spec.map φ)) := by
  let I := RingHom.ker φ.hom
  let M := ModuleCat.of A I
  let κ := {s : A // Nonempty (Basis PUnit.{u + 1}
    (Localization.Away s) (LocalizedModule.Away s I))}
  let U : κ → (Spec A).Opens := fun s ↦ PrimeSpectrum.basicOpen s.val
  have hcov : IsOpenCover U := .mk (by
    apply top_le_iff.mp
    intro P _
    obtain ⟨s, hs, hbs⟩ := hb P
    exact Opens.mem_iSup.mpr ⟨⟨s, hbs⟩, hs⟩)
  let q := localGeneratorsOfCoverFreeIso U hcov (fun _ ↦ PUnit.{u + 1})
    (fun s ↦ tildeBasicOpenBasisIso M s.val s.property.some)
  have hM : IsLocallyRankOne (Spec A) (tilde M) :=
    ⟨q, inferInstance, fun _ ↦ ⟨Equiv.refl _⟩⟩
  exact isLocallyRankOne_of_iso (Spec A) (affineIdealIso φ) hM

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

open scoped nonZeroDivisors
variable {D X : Scheme.{u}} (i : D ⟶ X)

/-- On a unit chart of the actual ideal module, its ring-theoretic section kernel is free of
rank one. The comparison uses `idealSectionsEquiv`, so it is the kernel of the displayed
structure-sheaf map. -/
def idealKernelEquivOfLocalUnit (W U : X.Opens) (hUW : U ≤ W)
    (e : (idealModule i).over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    RingHom.ker (i.app U).hom ≃ₗ[Γ(X, U)] Γ(X, U) :=
  (idealSectionsEquiv i U).symm.trans
    (((PresheafOfModules.evaluation (X.ringCatSheaf.over W).obj
      (op (Over.mk (homOfLE hUW)))).mapIso
      ((SheafOfModules.forget _).mapIso e)).toLinearEquiv)

/-- A local unit presentation of the actual ideal sheaf makes its section kernel finite. -/
theorem idealKernel_fg_of_local_unit (W U : X.Opens) (hUW : U ≤ W)
    (e : (idealModule i).over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    (RingHom.ker (i.app U).hom).FG := by
  let : Module.Finite Γ(X, U) (RingHom.ker (i.app U).hom) :=
    Module.Finite.equiv (idealKernelEquivOfLocalUnit i W U hUW e).symm
  exact Module.Finite.iff_fg.mp inferInstance

/-- Local rank one of the actual ideal produces affine charts with a regular generator of
its actual ring kernel. Neither a closed-immersion assumption nor a base is needed. -/
theorem exists_affine_regular_idealGenerator_of_isLocallyRankOne
    (hI : IsLocallyRankOne X (idealModule i)) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ a : Γ(X, U), IsSMulRegular Γ(X, U) a ∧
        RingHom.ker (i.app U).hom = Ideal.span {a} := by
  obtain ⟨W, hxW, ⟨e⟩⟩ :=
    (isLocallyRankOne_iff_local_unit X (idealModule i)).mp hI x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  exact ⟨U, hU, hxU, _root_.Ideal.ideal_exists_regular_generator _
    (idealKernelEquivOfLocalUnit i W U hUW e)⟩

end AlgebraicGeometry.Scheme.Hom
end
