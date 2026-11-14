# A046156 - limit set of the digit-cube-sum map, kernel-verified in Lean 4

[![CI](https://github.com/gaudinfrederic/oeis-A046156/actions/workflows/ci.yml/badge.svg)](https://github.com/gaudinfrederic/oeis-A046156/actions/workflows/ci.yml)

Machine-checked formalization of
[OEIS A046156](https://oeis.org/A046156): *"Limit set for
operation of repeatedly replacing a number with the sum of the
cubes of its digits."* (Schroeppel; keywords
`nonn,fini,full,base`). Writing `cubeSum n` for the sum of the
cubes of the decimal digits of `n` (the map of
[OEIS A055012](https://oeis.org/A055012)), this repository
proves, for **every** natural number `m`:

```lean
theorem A046156_seq (m : ℕ) :
  (∃ k, 0 < k ∧ Nat.iterate cubeSum k m = m) ↔
    m ∈ [0, 1, 55, 133, 136, 153, 160, 217, 244, 250, 352,
         370, 371, 407, 919, 1459]

theorem A046156 (n : ℕ) :
  ∃ k, Nat.iterate cubeSum k n ∈ NUMATT156
```

The biconditional means the published list of 16 values is
**exactly** the set of periodic points - not merely checked on
a range. The statement is unconditional: `0` is a genuine
fixed point in both conventions (`0^3 = 0`, and
`Nat.digits 10 0 = []` gives `cubeSum 0 = 0`), matching the
OEIS data which lists `0`. Convergence is proved too: every
orbit reaches the set.

## What is proved (kernel-checked, zero `sorry`)

- **Descent bound** (`cubeSum_le`, `A046156_bound`, in
  `A046156Defs`): `cubeSum n <= 729 * (number of digits)`, so
  every orbit of a number with more than 4 digits decreases;
  `desc4` then forces every orbit below `10^4`.
- **Exhaustive finite certificate** (`basin_all156`,
  reassembled from `basin_chunk156_0`/`basin_chunk156_1` in
  `A046156Basin0`/`A046156Basin1`): the residual case reduces
  to the `1001 = C(14,4)` sorted digit-multisets of length
  `<= 4` enumerated by `genMultisets 4 0`; each is checked by
  **kernel `decide`** to reach one of the 16 attractor
  multiset-classes `ATT156` within fuel `32`
  (`reachesATT156 32 M = true`). The `decide` is split into 2
  files (500 + 501 multisets) because a monolithic check is
  too heavy for the kernel.
- **Cycle structure** (`mem156_periodic`, `periodic156_mem`):
  membership in the 16 classes maps to the numeric values
  (`att156_maps`); `fin_cases` + `decide` certify the exact
  cycle decomposition - 6 fixed points `{0,1,153,370,371,407}`
  (the companion entry A046197), two 2-cycles `{136,244}` and
  `{919,1459}`, two 3-cycles `{55,250,133}` and
  `{160,217,352}`.
- **Spec/audit layer**: `Spec_A046156` (pure `abbrev`
  statement, no tactics), `Check_Spec_A046156` (closure
  `proven_spec_a046156 : SpecPropA046156 := A046156_seq`), and
  `Check_AntiVacuite_A046156` (N3: the cycles verified
  numerically, anchors `cubeSum 10 = 1` / `cubeSum 0 = 0`,
  ablation `cubeSum 99999 = 3645 < 10^4`, non-member `2`
  excluded).

## Scope

- Mathematics: the entry carries `fini,full`; the limit set
  itself is classical (computations and bound arguments are
  documented on the related OEIS entries). What is certified
  here is the **machine verification by the Lean kernel** of
  the complete limit set as an unconditional biconditional,
  conventions included.
- Beyond the theorem: no asymptotics, no base-generalization
  is included.

## Status

- Lean toolchain `v4.35.0`, mathlib `v4.35.0` (pinned manifest)
- `lake build` - exit 0, **zero `sorry`** (forbidden-construct
  scan `scan_n6.py` clean on every shipped file)
- `#print axioms` - `[propext, Classical.choice, Quot.sound]`,
  the three standard axioms only. **No `native_decide`, no
  `sorryAx`.** `lake check --paranoid` replays the export in
  the independent checkers (CI).

## Contents

- `A046253Defs.lean` - shared digit-multiset machinery:
  `genMultisets`, `sortedAll`, `mem_gen` (generator
  completeness), `digitsFuel` bridge lemmas
- `A014080Defs.lean` - shared digit/power-sum layer used by
  `A046156Defs`
- `A046156Defs.lean` - `cubeSum`, `cubeSumM`, `phiC`,
  `iterateC`, `ATT156`, `reachesATT156`; bounds `cubeSum_le`,
  `A046156_bound`, `sortedAll_length_le4`
- `A046156Basin0.lean` / `A046156Basin1.lean` - kernel
  certificates `basin_chunk156_0` / `basin_chunk156_1`: the
  `1001` multisets in 2 slices of `500` + `501`, each
  `reachesATT156 32 M = true` by `decide`
- `A046156.lean` - reassembly `basin_all156`, conjugation
  `conj_iterateC`, main theorems `A046156` (convergence) and
  `A046156_seq` (verbatim biconditional), cycle lemmas
- `Spec_A046156.lean`, `Check_Spec_A046156.lean`,
  `Check_AntiVacuite_A046156.lean` - spec / closure /
  non-vacuity audit files
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` -
  pinned build configuration (all 9 modules in
  `defaultTargets`, the `lake check --paranoid` perimeter)
- `scan_n6.py` - forbidden-construct scanner (state-machine
  comment/string filter, then token search)
- `LICENSE` - Apache 2.0

## Reproduce (auditor check)

```bash
lake exe cache get # fetch pinned mathlib oleans
lake build # builds all 9 libs, exit 0
lake check --paranoid # multi-kernel replay (leanchecker+nanoda+lean4lean)
python scan_n6.py # forbidden-construct scan, exit 0 = clean
lake env lean Check_AntiVacuite_A046156.lean # prints the axioms audit
```

Expected `#print axioms` output on every audited declaration
(`A046156`, `A046156_seq`, `basin_chunk156_0`,
`basin_chunk156_1`, `proven_spec_a046156`, `sat156_c3`):

```
'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Provenance

Developed under the the present formalization program (multi-session OEIS
conjecture formalization effort). The OEIS statement was
checked verbatim by independent external review before
packaging (unanimous on statement fidelity,
2026-11-07) - advisory; the proofs here are checked
by Lean. Statement: Richard C. Schroeppel; the descent bound
`cubeSum n <= 729 * digits` is the classical argument
documented on the related OEIS entries, formalized here.
Checked on continuous integration (kernel `decide`
certificates, zero error, zero `sorry`).
