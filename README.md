# recursion-topology-fv

A Lean4 formalization of the overall recursive architecture of a modern zkVM.

This repo is the final piece of the puzzle to be able to utter end-to-end statements about zkVMs like:
*"This zkVM has 128-bit provable security"*

This repo, in the future, will take as input the intermediate SNARKs of the zkVM, as well as its topology, and any
global arguments (related to state and memory accounting). For now, we are proving the security of a simplified
*Vanilla zkVM*, documented in the included whitepaper (`docs/vanillaVM.pdf`)

The goal for any zkVM is to prove its **correct-trace extractability (CTE)**: that an accepting final proof lets an
extractor recover a full, valid execution trace of its execution. Reducing this way its security to explicit
cryptographic hardness assumptions.

> **Status: v1.** The VanillaVM security is proven but we are idealizing some parts of the proof (see
> [Idealization](#idealization) below).
> Todo for v2:
>   - Figure out a better recursion axiomatization
>   - Introduce adversary advantages and runtimes

----

## Idealization

The proof is idealized in two places:

### Recursion: straight-line extraction composes

Every SNARK layer is assumed to have a *straight-line* extractor: it extracts a valid witness off the pair
`(statement, proof)`, without using rewinding or an oracle (`KnowledgeSound` in [`ArgumentSystem.lean`](VanillaZkVM/Preliminaries/ArgumentSystem.lean)).

Hash-based SNARKs in reality only have such extractors in the random oracle model (ROM). However, recursion-based architectures cannot be examined in the ROM, as each layer's random oracle needs to beinstantiated in the circuit verifier.

In this repo, we essentially take as input argument systems that are straight-line extractable in the ROM, and consider them to be straight-line extractable in the plain model.

This is false and it's an axiom we want to improve in v2.

### Perfect, probability-free crypto

The crypto layer is **perfect / probability-free**.

Currently, cryptographic building blocks are idealized as *perfect* to simplify everything.  For instance,
collision-resistance is just defined as being injective; knowledge soundness is `∃ extractor, ∀ accepting (x,p),
witness valid`. There is no security parameter, no `negl`, no running time yet.

We plan to improve this in v2 by introducing adversary advantages, and explicit algorithm runtimes.

More details can be found in [IDEALIZATION.md](https://github.com/ethereum/recursion-topology-fv/blob/main/IDEALIZATION.md).

## Project layout

**Library.** Generic code, shared by every VM.

- `VanillaZkVM/Preliminaries/`: Generic cryptography, definitions only (argument systems, commitments, traces)
- `VanillaZkVM/Specification/`: What a zkVM is and what it must prove (CTE)
- `VanillaZkVM/VMs/*.lean`: Shared VM building blocks (state, memory, ISA, bus, step contract)
- `VanillaZkVM/VMs/NonDeterministic/`: Generic wrapper that adds private input to any zkVM

**Example VMs.**

- `VanillaZkVM/VMs/TwoStep/`: Minimal two-layer VM, with and without a bus
- `VanillaZkVM/VMs/MultiStep/`: Recursive multi-step VM resembling the VanillaVM recursion architecture
- `VanillaZkVM/VMs/VanillaVM/`: The Vanilla VM of the whitepaper

Dependencies should point one way: `Preliminaries/` → `Specification/` → `VMs/`.

## Build

```bash
lake exe cache get
lake build
```

Requires the toolchain pinned in `lean-toolchain` and Mathlib `v4.32.0-rc1` (see `lakefile.toml`).
Every PR must keep `lake build` green and satisfy `#print axioms` ⊆ `{propext, Classical.choice,
Quot.sound}`.

## License

Apache License 2.0. See [LICENSE](LICENSE).
