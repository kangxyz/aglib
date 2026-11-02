/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootCover
public import Aglib.CategoryTheory.Sites.Torsor.KernelFiber

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.PowerFiber` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`8f9ad72402ef35c721f8dcc3e57b2c874f3ceb29d64e45afa0a22787b21fcc89`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
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
open AlgebraicGeometry.Scheme.EtaleCohomology Kummer.Coefficients
universe u
variable {X : Scheme.{u}} (n : ℕ) (P : Torsor (gm X))
variable (φ : P.carrier ⟶ underlyingSetSheaf (gm X))

/-- The value of the given torsor-to-multiplicative-sheaf map on a section. -/
def value (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) : (gm X).obj.obj U :=
  CategoryTheory.Sheaf.kernelFiberValue P φ U s

theorem value_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s : P.carrier.obj.obj U) :
    value P φ V (P.carrier.obj.map f s) = (gm X).obj.map f (value P φ U s) :=
  CategoryTheory.Sheaf.kernelFiber_value_naturality P φ f s

/-- The subfunctor of torsor sections mapped to zero in the additive multiplicative sheaf. -/
def powerFiberSubfunctor : Subfunctor P.carrier.obj :=
  CategoryTheory.Sheaf.kernelFiberSubfunctor P φ

theorem powerFiber_isSheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (powerFiberSubfunctor P φ).toFunctor :=
  CategoryTheory.Sheaf.kernelFiber_isSheaf P φ

/-- The subsheaf forming the zero fibre of the given map to the multiplicative sheaf. -/
def powerFiberSheaf : SetSheaf X :=
  CategoryTheory.Sheaf.kernelFiberSheaf P φ

variable (hφ : ∀ U a s, value P φ U (P.action U a s) =
  (power X n).hom.app U a + value P φ U s)

/-- A genuine power-equivariant Gm-torsor map has an actual μ_n fibre torsor. -/
def powerFiberTorsor (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) : Torsor (mu X n) := by
  let : Epi (power X n) := GroupCohomology.Kummer.RootCover.power_epi X n hn hinv
  let : Sheaf.IsLocallySurjective (power X n) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} (power X n)).mpr inferInstance
  exact CategoryTheory.Sheaf.kernelFiberTorsor P φ (inclusion X n) (power X n)
    (inclusion_power X n) (kernelIsLimit X n) hφ


end GroupCohomology.Kummer.PowerFiber
