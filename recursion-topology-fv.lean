-- Preliminaries: generic cryptography and shared helpers.
import «recursion-topology-fv».Preliminaries.ArgumentSystem        -- Relation, ArgumentSystem, Extractor, KnowledgeSound
import «recursion-topology-fv».Preliminaries.VectorCommitment      -- memory commitment + binding notions
import «recursion-topology-fv».Preliminaries.HashCommitment        -- bus commitment + collision resistance
import «recursion-topology-fv».Preliminaries.Trace                 -- reusable trace concatenation (concatTrace / chain_flatten)

-- Specification: the abstract target the concrete VMs must meet.
import «recursion-topology-fv».Specification.Zkvm                  -- abstract zkVM system and trace validity
import «recursion-topology-fv».Specification.Cte                   -- R*, CTE, and CTE ↔ knowledge soundness

-- VMs: concrete machinery and instances.
import «recursion-topology-fv».VMs.State                           -- Word/Addr/Byte, VM state, committed VM state
import «recursion-topology-fv».VMs.Memory                          -- committed/full-memory step lift and trace reconstruction
import «recursion-topology-fv».VMs.ISA                             -- representative five-class plain ISA
import «recursion-topology-fv».VMs.Bus                             -- reusable one-segment bus and chip-proof extraction
import «recursion-topology-fv».VMs.TwoStep.TwoStep                 -- minimal two-relation zkVM instantiating the abstract one
import «recursion-topology-fv».VMs.TwoStep.WithBus                 -- connects the reusable bus to the two-layer VM
import «recursion-topology-fv».VMs.MultiStep.MultiStep             -- binary-recursion-tree zkVM (convert / combine / embed)
import «recursion-topology-fv».VMs.VanillaVM.VanillaVM             -- recursive zkVM with bus-checked segments and main CTE theorem
import «recursion-topology-fv».VMs.NonDeterministic.Wrapper        -- add a private input to any zkVM via an outer proof layer

/-!
# recursion-topology-fv — umbrella module

The development is layered `Preliminaries → Specification → VMs`, and the imports
above are grouped accordingly. Every arrow in the module graph points up that
list; there are no back-edges.

* `Preliminaries/` — scheme-independent cryptography and the generic
  trace-concatenation helper.
* `Specification/` — what a zkVM is and what it must prove:
  `ZkVM`, `TraceValid`, `Rstar`, `CTE`, `cte_iff_knowledgeSound`.
* `VMs/` — concrete VM machinery: state vocabulary, committed-memory
  reconstruction, the representative ISA, the per-segment bus,
  the two-step variants, the multi-step recursion tower, the final recursive VM
  with bus-checked segments that instantiate the specification, and the
  private-input wrapper that turns any of them into a non-deterministic VM.

The concrete sanity models are available separately from
`«recursion-topology-fv».Sanity`.
-/
