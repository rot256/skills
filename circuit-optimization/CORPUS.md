# Surveyed Corpus

The references state laws and prices without naming every measured system, so the corpus can grow without turning the technique files into a survey.
This file records what has been read, so a future pass can skip it or deliberately re-read it.

Nothing here belongs in `references/`. Do not cite it from a technique.

## Read in Full

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
| Binius64 at commit `3f96163` | ZERO, word-AND, integer-multiply, and binary-field-multiply classes; independent power-of-two allocation; shifted affine operands; compiled cost statistics; fusion, CSE, DCE, zero folding, and scratch pooling |
| halo2 | selector combining, decomposition family, spread tables, ECC completeness argument, cost model, permutation chunking |
| Kimchi | hard wire budget and the 88-bit limb derivation, gate chaining, foreign-field multiplication, rotation gate design log |
| Plonky2 | selector groups, routed vs advice wires, gate packing, degree self-minimisation, circuit-wide maxima |
| Barretenberg | selector multiplexing and bitpatterns, delta-range gate, memory/ROM relations, bigfield lazy-reduction bounds, lookup-table design, co-processor deferral |

## Papers Read in Full

| paper | what was mined from it |
|---|---|
| Boyar, Matthews, Peralta, "Logic Minimization Techniques with Applications to Cryptology", J. Cryptology 2013 | multiplicative complexity as a cost function, the two-step method, sequential multi-output synthesis with output permutation, the multi-output degree bound, AES S-box at 32 AND, GF(2^4) inversion at 5 AND |
| Turan, Peralta, "The Multiplicative Complexity of Boolean Functions on Four and Five Variables", LightSec 2015 | affine invariance, affine-class counts, multiplicative complexity at most 3 on four variables and at most 4 on five, the Mirwald-Schnorr quadratic result, the counting bound |
| Testa, Soeken, Amaru, De Micheli, "Reducing the Multiplicative Complexity in Logic Networks for Cryptography and Security Applications", DAC 2019 | the XAG representation, affine-class cut rewriting, the six-input database |
| Testa, Soeken, Riener, Amaru, De Micheli, "A Logic Synthesis Toolbox for Reducing the Multiplicative Complexity in Logic Networks", DATE 2020 | the three passes and all measured AND counts |
| Liu, Li, Chen, Wang, "A Don't-Care-Based Approach to Reducing the Multiplicative Complexity in Logic Networks", IEEE TCAD 41(11), 2022 | the free-AND theorem, SAT don't-care detection, why implication weakens in an XAG |
| Boyar, Peralta, "Tight bounds for the multiplicative complexity of symmetric functions", TCS 396, 2008 | Hamming weight exactly n - HW(n) |
| Soeken, "Determining the Multiplicative Complexity of Boolean Functions using SAT", 2020 | the exact-synthesis frontier |
| Sonmez Turan, "Optimizing Implementations of Boolean Functions", BFA 2023 / NIST 2024 | homogeneous-degree decomposition, affine transforms, and the modified Paar heuristic for shared submonomials; no benchmark comparison or optimality guarantee |
| Lee, Meher, "Efficient Bit-Parallel Multipliers over Finite Fields GF(2^m)", Computers and Electrical Engineering 2010 | retained variable translation, both triangular basis conversions, the LPB multiplier core, Theorems 1 and 3, and Theorem 2 with an explicit full-degree hypothesis; corrected Theorem 4 with its missing trace condition, rejected Eq. (14), the converter AND count, and the Type-1/2/3 composite formulas and savings, and found bad entries in Table 1 and Appendix (b) |
| Ballet, Rolland, "Multiplication Algorithm in a Finite Field and Tensor Rank of the Multiplication", Journal of Algebra 2004 | ordinary bilinear tensor rank, the $2n-1$ bilinear lower bound, the $N_1+3N_2$ evaluation/interpolation construction, and characteristic-two tower bounds with recursive subfield repricing |
| Ballet et al., "On the Tensor Rank of Multiplication in Finite Extensions of Finite Fields and Related Issues in Algebraic Geometry", 2019 | exact tensor and symmetric-rank definitions, equality regimes for the $2n-1$ bound, tower composition, code lower bounds, generalized evaluation with higher-degree places and local coefficients, normal bases, constructivity limits, and a catalogue of unproved older claims |
| Cascudo, Giunta, "On Interactive Oracle Proofs for Boolean R1CS Statements", 2021 | reverse multiplication-friendly embeddings, Boolean-row-product packing, required image and kernel relations, batched modular linear checks, padding and soundness costs, and the boundary between Boolean R1CS packing and word-native systems |
| Arnon et al., "Succinct Arguments over Towers of Binary Fields", ePrint 2023/1784 | per-column tower fields, small-field commitments, block packing, virtual polynomials, binary-tower PLONK relations, shift and pack evaluators, characteristic-two lookup timestamps, integer gadgets, and full commitment/opening caveats |
| Diamond, Posen, "Polylogarithmic Proofs for Multilinears over Binary Towers", ePrint 2024/504, revised 2026 | coefficient packing versus ground-field extraction, tensor-algebra ring switching, ring-switching soundness, additive-NTT and FRI basis alignment, oracle skipping, Merkle caps, and unique-decoding limitations |
| "Jolt-b: Recursion Friendly Jolt with Basefold Commitment", ePrint 2024/1131 | same-point opening batching, Basefold implementation choices, recursion cost, and a position argument for using binary fields selectively in Boolean-essential precompiles; no new Boolean gate optimizer or supported binary-tower benchmark |
| Liu, Zhang, "Efficient SNARKs for Boolean Circuits via Sumcheck over Tower Fields", ePrint 2025/594 | deterministic tower-basis rounds, random large-field tail rounds, degree-dependent level grouping, tower zerocheck, base-field witness preservation, basis switching for commitment, and the boundary between sumcheck acceleration and Boolean gate optimization |
| Bagad, Domb, Thaler, "The Sum-Check Protocol over Fields of Small Characteristic", ePrint 2024/1046 | base/base-extension/extension cost separation, delayed challenge folding, product expansion and interpolation prefixes, switch-round and memory tradeoffs, characteristic-dependent interpolation conditions, and an incomplete research implementation without the final commitment opening check |
| Bagad, Dao, Domb, Thaler, "Speeding Up Sum-Check Proving", ePrint 2025/1117 | small-small/small-large/large-large pricing, delayed large partial evaluations, equality-polynomial factoring, split equality tables, switch-round formulas, and a limited three-round open implementation rather than a generic paper implementation |
| Koschatko et al., "Poseidon(2)b: Binary Field Versions of Poseidon/Poseidon2", ePrint 2025/1893 rev. 2, 2026 | Frobenius-sparse exponentiation, structured internal linear layers, full versus partial nonlinear rounds, Binius committed/virtual-column costs, current Sage/Rust tooling, and unresolved binary-subspace-trail analysis |
| Cui et al., "RainHash2.0: Hardware- and Arithmetization-Friendly Hash Function", ePrint 2026/1441 | inverse-or-zero relations, tower-recursive inversion, byte/word field switching, rotation-based linear layers, separate Binius/VOLE/hardware cost models, extensive open tooling, and a fresh security argument resting partly on round-independence and regularity assumptions |
| Maitin-Shepard, "Optimal Software-Implemented Itoh-Tsujii Inversion for GF(2^m)", ePrint 2015/028 | addition-chain inversion, exact field-multiplication and Frobenius counts, the distinction between multiplication-minimum and architecture-minimum chains, basis dependence, and the absence of zero handling or a ZK cost model |
| Sall, Hasan, "On Efficient Normal Bases over Binary Fields", 2024 | cyclic-shift Frobenius maps, Gaussian and algebraic-group normal-basis constructions, separate multiplication-table and field-operation complexity measures, extension-basis constructions, existence conditions, and companion Magma feasibility tooling |
| Ashur et al., "Vision Mark-32: A New Binary Field-Based Hash Function for Zero Knowledge Proof Systems", ePrint 2024/633 | quadratic-tower norm inversion, fixed linearized affine maps, additive-NTT MDS construction, separate hardware and proof-cost boundaries, heuristic algebraic-security estimates, and the absence of concrete Binius constraint accounting or a Mark-32-specific open implementation |
| Haaswijk, "SAT-Based Exact Synthesis for Multi-Level Logic Networks", PhD thesis, 2019, and Haaswijk et al., "SAT-Based Exact Synthesis: Encodings, Topology Families, and Parallelism", TCAD 2020 | CEGAR and care sets, fixed-budget optimality, topology families and parallel scheduling, scalability limits, Percy, and the boundary between direct-fanin AIG topology searches and affine-fanin XAG synthesis |
| Couveignes, Ezome, "The Equivariant Complexity of Multiplication in Finite Field Extensions", J. Algebra 2023 | equivariant block rank versus ordinary tensor rank, normal-basis convolution realization, the exact coefficientwise-product expansion, scalar extension and restriction, geometric constructions, asymptotic existence results, and inline Sage examples |
| Bernasconi, Cimato, Ciriani, Molteni, "Multiplicative Complexity of XOR Based Regular Functions", IEEE TC 2022 | exact autosymmetry quotient invariance, affine-hull D-reduction, exact affine-space membership complexity, combined reductions, heuristic experimental boundaries, single-output scope, and the public experiment-data repository |

## Read in Part

Nexus, Ligetron, zkEVM circuits, Risc0 recursion, Lasso/Shout papers, HyperPlonk, Sangria, ProtoGalaxy, Nova, ethSTARK, LogUp, Plookup, Freivalds' matrix-product verifier, and Schwartz's polynomial identity test.

## Primary Open Resource Queue

These are the next primary sources to mine when a concrete circuit exposes the corresponding bottleneck.

| scope | resource | what to mine |
|---|---|---|
| GF(2) exact synthesis | [Soeken, "Determining the Multiplicative Complexity of Boolean Functions using SAT"](https://eprint.iacr.org/2020/530) | abstract XAG encoding, symmetry breaking, lower-budget UNSAT certificates, and postprocessing after the AND optimum is fixed |
| scalable structural rewriting | [Chatterjee, Brayton, Mishchenko, "DAG-Aware AIG Rewriting"](https://people.eecs.berkeley.edu/~alanmi/publications/2006/dac06_rwr.pdf) | feasible cuts, canonical classes, precomputed replacements, structural sharing, and level-preserving acceptance |
| open-source synthesis implementation | [Berkeley ABC](https://github.com/berkeley-abc/abc) | rewriting, refactoring, resubstitution, don't-care computation, SAT sweeping, and pass orchestration; reprice every pass because its native AIG objective is not XAG AND count |
| open-source XAG implementation | [mockturtle](https://github.com/lsils/mockturtle) and [its XAG optimization documentation](https://mockturtle.readthedocs.io/en/latest/algorithms/xag_optimization.html) | XAG algebraic rewriting, resubstitution, refactoring, cut enumeration, and equivalence checking |
| open-source exact synthesis implementation | [Percy and the EPFL logic-synthesis showcase](https://github.com/lsils/lstools-showcase) | exact synthesis APIs, truth-table front ends, and small-function databases |
| bilinear GF(2^n) arithmetic | [Ballet, Chaumine, Pieltant, Rolland, "On the Tensor Rank of Multiplication in Finite Extensions of Finite Fields"](https://arxiv.org/abs/1107.1184) | distinctions between tensor rank, bilinear complexity, symmetric bilinear complexity, and finite-parameter construction bounds |
| interpolation constructions | [Chudnovsky and Chudnovsky, "Algebraic Complexities and Algebraic Curves over Finite Fields"](https://pmc.ncbi.nlm.nih.gov/articles/PMC304516/) | evaluation/interpolation multiplication algorithms and asymptotic upper bounds |
| PLONKish large-field backend | [PLONK](https://eprint.iacr.org/2019/953) and [Plookup](https://eprint.iacr.org/2020/315) | selector, permutation, grand-product, table, and row costs that replace scalar Boolean gate counts |
| AIR/STARK backend | [Ben-Sasson et al., "Scalable, Transparent, and Post-Quantum Secure Computational Integrity"](https://starkware.co/wp-content/uploads/2022/05/STARK-paper.pdf) | trace width, transition and boundary constraints, composition degree, domain blowup, and verifier/prover tradeoffs |
| cross-arithmetization formalism | [Maller et al., "Customizable Constraint Systems for Succinct Arguments"](https://eprint.iacr.org/2023/552) | embeddings of R1CS, PLONKish, and AIR-style relations and which costs survive the translation |
| data-parallel Boolean GKR | [Hu et al., "GKR for Boolean Circuits with Sub-linear RAM Operations"](https://eprint.iacr.org/2025/717) | layer and wiring regularity, bit packing, precomputed sumcheck data, word-RAM assumptions, and applicability beyond synthetic regular circuits |
| small-field sumcheck | ["Packed Sumcheck over Fields of Small Characteristic"](https://eprint.iacr.org/2025/719) | packed prover representation, extension-field challenges, extraction or ground-field guarantees, and the exact operations that remain linear in the packed width |
| general sumcheck implementation | [Ingonyama super-sumcheck](https://github.com/ingonyama-zk/super-sumcheck) | collapsing-array versus precomputation tradeoffs, parallel memory access, and backend-agnostic profiling of products of MLEs |
| Sage Boolean-function analysis | [sboxU](https://github.com/lpp-crypto/sboxU) | affine-equivalence and vectorial-Boolean-function utilities that can front-end exact synthesis without becoming the optimizer itself |

## Not yet Read

Anything not listed above.
When adding a system, record it here and fold its lessons into existing techniques where possible.
A genuinely new law deserves its own technique entry.
