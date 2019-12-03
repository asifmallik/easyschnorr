require import Real.
require import List.
abstract theory IdentificationProtocol.

type sk_t.
type pk_t.
print List.
type packet_t.
type transcript_t = packet_t list. 

op packet : packet_t.

module type G = {
  proc generate () : sk_t * pk_t
}.

module type P = {
  proc setup (secret : sk_t) : unit
  proc next_step (packet : packet_t) : packet_t
}.

module type V = {
  proc setup (image : pk_t) : unit
  proc next_step (packet : packet_t) : bool * packet_t
  proc output () : bool
}.

module Protocol (Gen : G, Prover : P, Verifier : V) = {
  proc run () : transcript_t * bool = {
    var pk, sk, p, o, terminate, transcript;
    (sk,pk)<-Gen.generate();
    Prover.setup(sk);
    Verifier.setup(pk);

    terminate <- false;
    p <- packet;
    transcript <- [];
    while (!terminate) {
      p <- Prover.next_step(p);
      transcript <- p :: transcript;
      (terminate, p) <- Verifier.next_step(p);
      transcript <- p :: transcript;
    }

    o <- Verifier.output();
    return (transcript, o);
  } 
}.

(* Define adversaries in new theory/file? *)

print DiffieHellman.DDH.Adversary.
print DiffieHellman.DDH.DDH0.
  
(* Attack Game 18.1 *)
module type DirectAdversary = {
    proc setup (v_k : pk_t) : unit
    proc next_step (packet : packet_t) : packet_t
}.

module DirectAttack(Gen : G, Adv : DirectAdversary, Verifier : V) = {
  proc run () : transcript_t * bool = {
    var pk, sk, p, o, terminate, transcript;
    (sk,pk)<-Gen.generate();
    Adv.setup(pk); (* Init the adversary with v_k *)
    Verifier.setup(pk);

    terminate <- false;
    transcript <- [];
    p <- packet;
    while (!terminate) {
      p <- Adv.next_step(p);
      transcript <- p :: transcript;
      (terminate, p) <- Verifier.next_step(p);
      transcript <- p :: transcript;
    }

    o <- Verifier.output();
    return (transcript, o);
  } 
}.

end IdentificationProtocol.
