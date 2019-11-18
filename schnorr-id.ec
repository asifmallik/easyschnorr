(*
 * Schnorr's identification protocol.
 * Boneh & Shoup, Figure 19.1
 *)

require import CyclicGroup.
require import Int.

require IdentificationProtocol.

type g_t. (* Type of a group element?*)

(* Instantiate an identification protocol -> types?
*
*clone import IdentificationProtocol with
*type IdentificationProtocol.sk_t <- g_t.
*type IdentificationProtocol.pk_t <- g_t.
*g: a generator of G.
* Z_q
* C subset of Z_q
*)

module SchnorrGen : IdentificationProtocol.G = {
  proc generate () : sk_t * pk_t  = {
    var alpha, u;
    (*  alpha =$..? take random element from Z_q *)
    u <-  g^alpha;
    return (alpha, u);
    }
  }

module SchnorrProver : IdentificationProtocol.P = {
  var s;
  proc setup (secret: sk_t) : unit = {
    s <- secret;
  }
}

module SchnorrVerifier : IdentificationProtocol.V = {
  var p;
  var u_t;
  var a_z;
  var c;
  
  proc setup (image: pk_t) : unit = {
    p <- image;
    (* Init other variables to something? *)
    return;
  }

  proc output () : bool = {
    return (g^a_z = u_t.u^c);
  }
}

