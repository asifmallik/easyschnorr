require import Real.
abstract theory IdentificationProtocol.

type sk_t.
type pk_t.

type packet_t.

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
  proc run () : bool = {
    var pk, sk, p, o, terminate;
    (sk,pk)<-Gen.generate();
    Prover.setup(sk);
    Verifier.setup(pk);

    terminate <- false;
    p <- packet;
    while (!terminate) {
      p <- Prover.next_step(p);
      (terminate, p) <- Verifier.next_step(p);
    }


    o <- Verifier.output();
    return o;
  } 
}.

(* Define adversaries in new theory/file? *)

print DiffieHellman.DDH.Adversary.
print DiffieHellman.DDH.DDH0.
  
(* Definition 18.1 *)
module type DirectAdversary = {
    proc setup (v_k : pk_t) : unit
    proc next_step (packet : packet_t) : packet_t
}.

module DirectAttack(Gen : G, Adv : DirectAdversary, Verifier : V) = {
  proc run () : bool = {
    var pk, sk, p, o, terminate;
    (sk,pk)<-Gen.generate();
    Adv.setup(pk); (* Init the adversary with v_k *)
    Verifier.setup(pk);

    terminate <- false;
    p <- packet;
    while (!terminate) {
      p <- Adv.next_step(p);
      (terminate, p) <- Verifier.next_step(p);
    }

    o <- Verifier.output();
    return o;
  } 
}.

end IdentificationProtocol.
