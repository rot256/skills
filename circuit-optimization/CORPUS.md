# Surveyed corpus

The references state laws and prices without naming the systems they were measured in, so that the corpus can grow
without the documents turning into a survey. This file is the bookkeeping that makes that possible: **what has already
been read**, so a future pass can skip it or deliberately re-read it.

Nothing here belongs in `references/`. Do not cite it from a technique.

## Read in full

| system | what was mined from it |
|---|---|
| Plonky3 | AIR/quotient cost model, symbolic degree inference, LogUp degree formula, Poseidon2/Keccak/SHA-256 AIRs, periodic columns, selector pricing |
| SP1 | shard ceilings and the two-ceiling analysis, gas model, per-AIR cost oracle, word/limb operations, precompile economics, memory and register model, audit findings |
| OpenVM | adapter/core split, chip specialisation, memory offline checker, range/var-range/range-tuple primitives, encoder, mod-builder, SHA-2 family, measured PR deltas |
| stwo + stwo-cairo | circle/log-space degree quantisation, machine-generated components, padding by row repetition, relation tracker, component specialisation |
| Cairo / Stone | diluted form, suffix-sum flag packing, undefined-behaviour column reuse, quadratic-AIR discipline, periodic columns |
| powdr | constraint-system optimiser passes, degree bounds for identities vs bus interactions, autoprecompiles |
| ZisK | bus-term fusion rule, airgroup values, padding cancellation by a countable bus term, secondary machines |
| Miden VM | degree-9 budget, opcode layout by degree class, aggregate flags, sorted range check with jumps, chiplet economics |
| Valida | register-file deletion, instruction-indexed pc, comparison gadgets, bitwise identities |
| RISC Zero | implicit timestamps, dual-register coalescing, segment polynomials, x0 redirection |
| Jolt | prefix-suffix decomposable tables, per-cycle pricing, operand interleaving |
| Binius | virtual vs committed columns, structured columns, degree-1 free line |
| halo2 | selector combining, decomposition family, spread tables, ECC completeness argument, cost model, permutation chunking |
| Kimchi | hard wire budget and the 88-bit limb derivation, gate chaining, foreign-field multiplication, rotation gate design log |
| Plonky2 | selector groups, routed vs advice wires, gate packing, degree self-minimisation, circuit-wide maxima |
| Barretenberg | selector multiplexing and bitpatterns, delta-range gate, memory/ROM relations, bigfield lazy-reduction bounds, lookup-table design, co-processor deferral |

## Read in part

Nexus, Ligetron, zkEVM circuits, Risc0 recursion, Lasso/Shout papers, HyperPlonk, Sangria, ProtoGalaxy, Nova, ethSTARK,
LogUp, Plookup.

## Not yet read

Anything not listed above. When you add a system, add a row here and fold what it teaches into the existing sections --
**a new system should mostly produce new *conditions* on existing laws, not new sections.** If it produces a genuinely
new law, that is the interesting outcome and it deserves its own entry.
