require import Real.
abstract theory IdentificationProtocol.

type sk_t.
type pk_t.

module type G = {
  proc generate () : sk_t * pk_t
}.

module type P = {
  proc setup (secret : sk_t) : unit
}.

module type V = {
  proc setup (image : pk_t) : unit
  proc output () : bool
}.

module type I (Prover: P, Verifier: V) = {
  proc interact() : unit
}.

module Protocol (Gen : G, Prover : P, Verifier : V, Interaction : I) = {
  module Interaction = Interaction(Prover, Verifier)
  proc run () : bool = {
    var pk, sk, o;
    (sk,pk)<-Gen.generate();
    Prover.setup(sk);
    Verifier.setup(pk);
    Interaction.interact();
    o <- Verifier.output();
    return o;
  } 
}.
end IdentificationProtocol.
