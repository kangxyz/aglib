/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.RootCover
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.Torsor
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.RepresentedTorsor

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.RootCover` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1a7364496462af48d5b1344af5196696b5841a85473b635257383990275814af`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual polynomial root covers and small-etale Kummer surjectivity

C4/C5 support, `K2-018#lem:k2018-geometric-exact-order`, mathematical basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For every actual scheme and positive globally invertible n, the constructed
finite-etale surjective cover T^n-a supplies a root of each unit section.
The literal image sieve is proved covering on the actual small-etale site,
so the actual sheaf nth-power map is Epi. This PROVES the previously named
EtalePowerSurjectivity family; no form of 03PL is retained as an assumption
by this proof. The argument works over arbitrary schemes.

The polynomial cover's represented set sheaf is then identified with the
existing extension-fibre root torsor through their actual unit-root section
coordinates. Naturality and equivariance use literal pullback and positive
multiplication by roots of unity. The canonical Ext classes consequently
agree, without 03AJ. The parameter h in the reusable isomorphism permits
compatibility with the existing API; the proved family above supplies it.
Field Kummer identification, curve-pair descent/sign and Bockstein
normalization remain separate applications. This generic file imports no
WeightTwo or essay consumer.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme.Group
namespace GroupCohomology.Kummer.RootCover
open AlgebraicGeometry.Scheme.EtaleH1 Kummer.Coefficients Kummer.Torsor
universe u

/-- Actual finite-etale root covers prove local surjectivity of the power map. -/
theorem power_epi (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) : Epi (power X n) := by
  apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} (power X n)).mp
  constructor
  intro U t
  change _ ∈ X.smallGrothendieckTopology @Etale U
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology]
  intro x
  letI : NeZero n := ⟨hn.ne'⟩
  let a := (unitsSections X (op U) t).toMul
  have hi : IsUnit (n : Γ(U.left, ⊤)) := by
    simpa only [map_natCast] using hinv.map U.hom.appTop.hom
  let Y := AlgebraicGeometry.Scheme.Group.RootCover.cover U.left n hn hi a
  haveI : Surjective Y.obj.hom := AlgebraicGeometry.Scheme.Group.RootCover.cover_surjective
      U.left n hn hi a
  let V : X.Etale := Scheme.Etale.mk (Y.obj.hom ≫ U.hom)
  let f : V ⟶ U := MorphismProperty.Over.homMk Y.obj.hom rfl (by trivial)
  obtain ⟨y, hy⟩ := (surjective_iff Y.obj.hom).mp inferInstance x
  refine ⟨V, f, y, ?_, inferInstanceAs (Etale Y.obj.hom), hy⟩
  obtain ⟨b, hb⟩ := AlgebraicGeometry.Scheme.Group.RootCover.cover_hasRoot U.left n hn hi a
  refine ⟨(unitsSections X (op V)).symm (Additive.ofMul b), ?_⟩
  apply (unitsSections X (op V)).injective
  apply Additive.toMul.injective
  rw [power_apply, AddEquiv.apply_symm_apply, unitsSections_naturality]
  exact hb

/-- The formerly explicit 03PL family is now proved for the actual small site. -/
theorem etalePowerSurjectivity : EtalePowerSurjectivity.{u} := power_epi

variable (h : EtalePowerSurjectivity.{u}) (X : Scheme.{u}) (n : ℕ)
variable (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (a : Γ(X, ⊤)ˣ)
variable [NeZero n]
local instance : Surjective (AlgebraicGeometry.Scheme.Group.RootCover.cover X n hn hinv
    a).obj.hom :=
  AlgebraicGeometry.Scheme.Group.RootCover.cover_surjective X n hn hinv a

/-- The sectionwise identification of the polynomial root cover with the Kummer root torsor. -/
def sectionEquiv (U : X.Etaleᵒᵖ) :
    (finiteRepresentedSetSheaf (AlgebraicGeometry.Scheme.Group.RootCover.cover X n hn hinv
        a)).obj.obj U ≃
      (rootTorsor h X n hn hinv a).carrier.obj.obj U :=
  Equiv.ulift.trans ((AlgebraicGeometry.Scheme.Group.RootCover.sectionsEquiv X n a
    ((Scheme.Etale.forget X).obj U.unop)).trans (rootSectionsEquiv h X n hn hinv a U).symm)

@[simp] theorem sectionEquiv_coordinates (U : X.Etaleᵒᵖ)
    (p : (Scheme.Etale.forget X).obj U.unop ⟶ AlgebraicGeometry.Scheme.Group.RootCover.scheme X
        n a) :
    (rootSectionsEquiv h X n hn hinv a U (sectionEquiv h X n hn hinv a U (ULift.up p))).val =
      (AlgebraicGeometry.Scheme.Group.RootCover.sectionsEquiv X n a _ p).val := by
  exact congrArg Subtype.val ((rootSectionsEquiv h X n hn hinv a U).apply_symm_apply _)

/-- The sheaf isomorphism between the represented polynomial root cover and the root torsor. -/
def sheafIso : finiteRepresentedSetSheaf (AlgebraicGeometry.Scheme.Group.RootCover.cover X n hn
    hinv a) ≅
    (rootTorsor h X n hn hinv a).carrier :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U => (sectionEquiv h X n hn hinv a U).toIso)
    (fun {U V} f => by
      ext p
      apply (rootSectionsEquiv h X n hn hinv a V).injective
      apply Subtype.ext
      change (rootSectionsEquiv h X n hn hinv a V
        (sectionEquiv h X n hn hinv a V (ULift.up ((Scheme.Etale.forget X).map f.unop ≫
            p.down)))).val =
        (rootSectionsEquiv h X n hn hinv a V
          ((rootTorsor h X n hn hinv a).carrier.obj.map f
            (sectionEquiv h X n hn hinv a U p))).val
      rw [sectionEquiv_coordinates, rootSections_naturality]
      cases p
      rw [sectionEquiv_coordinates]
      exact AlgebraicGeometry.Scheme.Group.RootCover.sectionsEquiv_naturality X n a _ _))

/-- The equivariant isomorphism from the polynomial root-cover torsor to the Kummer root torsor. -/
def torsorIso : Scheme.EtaleH1.Torsor.Iso
    (torsorOfSchemeAction (MultiplicativeGroup.rootsGroupScheme X n)
      (AlgebraicGeometry.Scheme.Group.RootCover.cover X n hn hinv a)
      (AlgebraicGeometry.Scheme.Group.RootCover.coverTorsorAction X n hn hinv a))
    (rootTorsor h X n hn hinv a) where
  carrierIso := sheafIso h X n hn hinv a
  equivariant U z p := by
    apply (rootSectionsEquiv h X n hn hinv a U).injective
    apply Subtype.ext
    change (rootSectionsEquiv h X n hn hinv a U
      (sectionEquiv h X n hn hinv a U (ULift.up
        ((AlgebraicGeometry.Scheme.Group.RootCover.coverTorsorAction X n hn hinv a).act
            z.down.toMul p.down)))).val =
      (rootSectionsEquiv h X n hn hinv a U ((rootTorsor h X n hn hinv a).action U z
        (sectionEquiv h X n hn hinv a U p))).val
    rw [sectionEquiv_coordinates, rootSections_action]
    cases p
    rw [sectionEquiv_coordinates]
    exact AlgebraicGeometry.Scheme.Group.RootCover.torsorAction_sections X n a _ _ _


universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The polynomial scheme torsor and the original positive extension-fibre
torsor have the same canonical Ext class, without a classification premise. -/
theorem rootClass_eq_scheme : rootClass h X n hn hinv a =
    torsorExtClass (torsorOfSchemeAction (MultiplicativeGroup.rootsGroupScheme X n)
      (AlgebraicGeometry.Scheme.Group.RootCover.cover X n hn hinv a)
      (AlgebraicGeometry.Scheme.Group.RootCover.coverTorsorAction X n hn hinv a)) :=
  (torsorExtClass_iso (torsorIso h X n hn hinv a)).symm

end GroupCohomology.Kummer.RootCover
