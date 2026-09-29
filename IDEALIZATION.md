# Notes on Idealization

In this repository, we (over-)idealize many cryptographic concepts. We explain below in detail.
We are of course aware that this is far from being cryptographically accurate, and we may change this in the future.

### Perfect model without probabilities and running times

*Summary*. We do not work with probabilities and running times, and instead assume perfect, error-free idealizations.

*Example Code*. Recall that a hash function family is collision-resistant if it is hard to find two distinct inputs mapping to the same output. Currently, we idealize this as follows:
```lean
def CollisionResistant (H : HashCommitment) : Prop :=
  ∀ b b' : H.Domain, H.hash b = H.hash b' → b = b'
```
Note that this essentially means we require injectivity. Of course, compressing hash functions cannot be injective (but we never explicitly require it to be compressing in the lean code). A more proper definition would give an efficient adversary a hash key and then ask it to find a collision.

*Rationale*. We may change this in the future and add probabilities, explicit adversaries, and running times, but for now the rationale is as follows: main goal of this lean project is to formalize that the recursive topology -- with all of its relations -- is structurally proving the right thing, i.e., the relations compose to ultimately yield correctness of the computation. We decided that to get quickly towards that goal -- without distraction by probabilities and running times -- such an idealization is a good first step.


### No use of security parameter, negligible functions, polynomial time

*Summary*. The code does not use or define an asymptotic security parameter, negligible functions, or polynomial time.

*Rationale*. Clearly, as we do not talk about running times or success probabilities at all, using negligible functions or polynomial time is not necessary. Also, ultimately the systems we deploy in practice will not be asymptotic objects but rather concrete objects with concrete security levels. Thus, even when we introduce proper formalism for probabilities and running times, we would most likely not follow an asymptotic treatment. The only argument for it may be to meaningfully talk about "constant depth" vs "logarithmic depth" vs "polynomial depth" of recursion.

### Notions of knowledge soundness

*Summary*. The current notion of knowledge soundness is idealized and not achievable for succinct arguments.

*Example Code.* Our current definition of knowledge soundness looks like this:
```lean
def KnowledgeSound {R : Relation} (AS : ArgumentSystem R) : Prop :=
  ∃ E : Extractor R AS, ∀ (x : R.Stmt) (p : AS.Proof),
    AS.verify x p → R.rel x (E.extract x p)
```
That means that there is one universal extractor that can turn any verifying statement-proof pair into a valid witness.
Note that again, the proof does not need to be efficiently generated, and even if it would (if OWFs exist), there is a compression argument showing that such a strong notion of extraction is not possible. However, nothing in the code forces the proof to be succinct, so assuming this definition is not the same as assuming False.

*Rationale.* The same rationale as for the perfect model above.

*Other notions for the future.*
This is most likely the most important thing to change in the future. Assuming, we use probabilities, adversaries, and running times at some point, here are some options:
- Non-universal extractor (i.e., for every adversary, there is one extractor), and this extractor gets the adversary's coins. This notion seems plausibly achievable but is often insufficient in applications: adversaries in practice do not pick their statements and forged proofs just based on random coins, but also based on inputs that they observe from the environment, e.g., public keys of other users.
- Non-universal extractor, extractor gets adversary's coins, and both adversary and extractor get a joint auxiliary input. The quantifiers are: for every adversary, there is one extractor, so that for every auxiliary input, ... . This models the side information obtained from the environment, but unfortunately there are impossibilities with respect to that model (see [this paper](https://eprint.iacr.org/2014/402)) unless we restrict the auxiliary input in some way. How to restrict it in a meaningful way is still under active discussion.

Note that the SNARKs used in practice are proven knowledge-sound in the random oracle model, and so we need some *heuristic* to say that this implies the notion of knowledge soundness that we pick. We cannot use knowledge-soundness in the random oracle model in this Lean project, as this would require SNARKs to work for relativized relations, which is [not possible in general](https://eprint.iacr.org/2024/728.pdf).
