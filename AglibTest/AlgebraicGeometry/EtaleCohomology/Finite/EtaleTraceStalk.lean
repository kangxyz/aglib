/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleTraceStalk

/-! Original local graph SUM on germs and actual cofinal splitting charts. -/

open AlgebraicGeometry.Scheme.EtaleCohomology

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.exists_refining_finiteEtale_trace_chart'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_refining_finiteEtale_trace_chart

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleSheafTrace_germ_local'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteEtaleSheafTrace_germ_local

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleSheafTrace_stalk'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteEtaleSheafTrace_stalk
