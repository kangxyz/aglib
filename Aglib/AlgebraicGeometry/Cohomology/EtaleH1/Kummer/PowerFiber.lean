/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.RootCover
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.PowerFiber` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`8f9ad72402ef35c721f8dcc3e57b2c874f3ceb29d64e45afa0a22787b21fcc89`.
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
# Actual fibres of power-equivariant multiplicative torsors

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

Input data are an actual Gm sheaf torsor, an actual sheaf map to Gm, and
its equivariance under the already constructed literal nth-power map.
The zero fibre is constructed as a genuine subsheaf. Its action is the
actual root inclusion acting on the original torsor; exact kernel sections
prove unique transport. At positive globally invertible level, local
nonemptiness follows from the proved power-map epimorphism and transitivity
of actual small-etale covering sieves. Thus the fibre is an actual mu_n
torsor. No standard-theorem family, Picard object, pair classification or H1
comparison is assumed. The frame-power application supplies its actual map
and equivariance separately. This generic module imports no Curves/Picard.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite
namespace GroupCohomology.Kummer.PowerFiber
open AlgebraicGeometry.Scheme.EtaleH1 Kummer.Coefficients
universe u
variable {X : Scheme.{u}} (n : ℕ) (P : Torsor (gm X))
variable (φ : P.carrier ⟶ underlyingSetSheaf (gm X))

def value (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) : (gm X).obj.obj U := φ.hom.app U s

theorem value_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s : P.carrier.obj.obj U) :
    value P φ V (P.carrier.obj.map f s) = (gm X).obj.map f (value P φ U s) :=
  ConcreteCategory.congr_hom (φ.hom.naturality f) s

def powerFiberSubfunctor : Subfunctor P.carrier.obj where
  obj U := {s | value P φ U s = 0}
  map {U V} f s hs := by
    change value P φ V (P.carrier.obj.map f s) = 0
    rw [value_naturality, hs, map_zero]

theorem powerFiber_isSheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (powerFiberSubfunctor P φ).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff (J := Scheme.smallEtaleTopology X) (powerFiberSubfunctor P φ)
    ((isSheaf_iff_isSheaf_of_type _ _).mp P.carrier.property)).2
  intro U s hs
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    (underlyingSetSheaf (gm X)).property).isSeparated _ hs).ext
  intro V f hf
  change (gm X).obj.map f.op (value P φ U s) = (gm X).obj.map f.op 0
  rw [map_zero, ← value_naturality]
  exact hf

def powerFiberSheaf : SetSheaf X :=
  ⟨(powerFiberSubfunctor P φ).toFunctor, powerFiber_isSheaf P φ⟩

variable (hφ : ∀ U a s, value P φ U (P.action U a s) =
  (power X n).hom.app U a + value P φ U s)

/-- A genuine power-equivariant Gm-torsor map has an actual μ_n fibre torsor. -/
def powerFiberTorsor (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) : Torsor (mu X n) where
  carrier := powerFiberSheaf P φ
  action U a s := ⟨P.action U ((inclusion X n).hom.app U a) s.val, by
    change value P φ U (P.action U ((inclusion X n).hom.app U a) s.val) = 0
    rw [hφ, s.property]
    have hz : (power X n).hom.app U ((inclusion X n).hom.app U a) = 0 :=
      congrArg (fun q => q.hom.app U a) (inclusion_power X n)
    rw [hz, add_zero]⟩
  zero_action U s := by apply Subtype.ext; change P.action U _ s.val = s.val; rw [map_zero,
      P.zero_action]
  add_action U a b s := by
    apply Subtype.ext
    change P.action U _ s.val = P.action U _ (P.action U _ s.val)
    rw [map_add, P.add_action]
  naturality {U V} f a s := by
    apply Subtype.ext
    change P.carrier.obj.map f (P.action U ((inclusion X n).hom.app U a) s.val) =
      P.action V ((inclusion X n).hom.app V ((mu X n).obj.map f a)) (P.carrier.obj.map f s.val)
    rw [P.naturality, inclusion_naturality]
  unique_transport U s t := by
    obtain ⟨a, ha, hu⟩ := P.unique_transport U s.val t.val
    have hp : (power X n).hom.app U a = 0 := by
      have ht := congrArg (value P φ U) ha
      rw [hφ, s.property, t.property, add_zero] at ht
      exact ht
    refine ⟨rootSection X n U a hp, ?_, ?_⟩
    · apply Subtype.ext
      change P.action U ((inclusion X n).hom.app U (rootSection X n U a hp)) s.val = t.val
      rw [inclusion_rootSection, ha]
    · intro b hb
      apply inclusion_app_injective X n U
      rw [inclusion_rootSection]
      exact hu _ (congrArg Subtype.val hb)
  locally_nonempty U := by
    let : Epi (power X n) := GroupCohomology.Kummer.RootCover.power_epi X n
        hn hinv
    let : Sheaf.IsLocallySurjective (power X n) :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} (power X n)).mpr inferInstance
    apply (Scheme.smallEtaleTopology X).transitive (P.locally_nonempty U)
    intro V f hf
    obtain ⟨s⟩ := hf
    refine (Scheme.smallEtaleTopology X).superset_covering ?_
      (Presheaf.imageSieve_mem (Scheme.smallEtaleTopology X) (power X n).hom
        (-value P φ (op V) s))
    rintro W g ⟨a, ha⟩
    refine ⟨⟨P.action (op W) a (P.carrier.obj.map g.op s), ?_⟩⟩
    change value P φ (op W) (P.action (op W) a (P.carrier.obj.map g.op s)) = 0
    rw [hφ, ha, map_neg]
    rw [value_naturality, neg_add_cancel]


end GroupCohomology.Kummer.PowerFiber
