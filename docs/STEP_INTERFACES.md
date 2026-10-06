# Step-interface contract

This is the interface shared by the memory, ISA, and bus work.

The contract prevents modules from growing unrelated predicates all called
"step." It fixes the semantic direction of the two bridge arguments while
leaving their concrete operation and witness types to their owning modules.

## Canonical interfaces

The Lean declaration `StepInterface V` has the following fields:

```text
V.step
  : V.State -> V.State -> Prop

represents
  : CommittedState -> V.State -> Prop

stepCommitted
  : CommittedState -> CommittedState -> Prop

```

`V.step` is the single canonical step predicate.
`ISA.System.step` is the predicate assigned to that field by a concrete
Vanilla `ZkVM`; it must not become a second, disconnected top-level execution
relation. `TwoStep.System.toZkVM` makes this assignment in the public two-layer
toy, and `VanillaVM.System.toZkVM` reuses it in the assembled recursive VM.

`stepCommitted` relates two committed states. Operation-specific data and
opening proofs may be carried by internal predicates. In the two-layer toy,
`ISA.System.committedOperation` checks the explicit `MemStep` against the
program-selected operation. `ISA.System.committedStep` then says that some such
`MemStep` exists, so callers of the public relation need not pass it explicitly.

`Bus.System` separately supplies

```text
stepWithBus
  : CommittedState -> CommittedState -> BusEvidence -> Prop
```

where `BusEvidence` contains one segment's bus and the memory-opening data for
one transition. Before the bridge is used, `Bus.System.segment_extract` proves
that the step, Keccak, Poseidon, and range proofs all refer to that same segment
bus. This theorem is independent of how segment proofs are later combined.
`stepWithBus` then requires both the step check and all three chip checks. The
reusable `stepWithBus_committedOperation` theorem derives the canonical
committed ISA operation for the same recovered `MemStep`; a concrete VM uses
that same value to prove the weaker `BusBridge` statement that a suitable
`MemStep` exists.
Keeping the bus predicate out of `StepInterface` lets the memory interface be
instantiated without inventing unused bus data.

## Frozen bridge statement

For `I : StepInterface V`, the bus bridge is

```text
I.BusBridge stepWithBus :=
  forall C1 C2 and bus evidence b,
    stepWithBus C1 C2 b ->
    stepCommitted C1 C2.
```

For one segment, the step, Keccak, Poseidon, and range-proof extractors each
return a bus. All four buses have the same committed digest, so collision
resistance proves that they are equal. Different segments have separate bus
commitments and may use different buses; the proof neither compares nor
equates them.

## Ownership

| Layer | Designated module | Required realization |
|---|---|---|
| Memory reconstruction | `recursion-topology-fv/VMs/Memory.lean` + concrete VM module | `VMs/Memory.lean` defines `CommitInv`, the memory-only step predicates, and `trace_mem_extract`. The concrete VM packages the appropriate committed relation as a `StepInterface`; `VMs/TwoStep/TwoStep.lean` supplies the current instance. |
| ISA semantics | `recursion-topology-fv/VMs/ISA.lean` | Define `ISA.System.step`, connect explicit committed-memory witnesses through `ISA.System.committedOperation`, and assign it directly to both the toy and assembled `ZkVM` instances. |
| Segment bus | `recursion-topology-fv/VMs/Bus.lean` + concrete VM connection modules | `Bus.System.stepWithBus` combines the segment step check with the three chip checks. `Bus.System.stepWithBus_committedOperation` proves the implication to the committed ISA operation while preserving the recovered `MemStep`, and `Bus.System.segment_extract` proves that the four buses recovered for one segment are equal. Neither theorem chooses how segments are combined. `VMs/TwoStep/WithBus.lean` demonstrates the non-recursive connection; `VMs/VanillaVM/VanillaVM.lean` derives the recursive leaf extractor from the same segment theorem. |

No other module should introduce a different, unrelated public execution
predicate between two states.
Internal helper predicates with additional witness arguments are permitted, but
the module must expose them through this contract.
