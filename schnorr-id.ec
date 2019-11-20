(*
 * Schnorr's identification protocol.
 * Boneh & Shoup, Figure 19.1
 *)

require import Int.
require import DiffieHellman.
print DiffieHellman.G.
clone export DiffieHellman.G as Group.
require import IdentificationProtocol.
print Group.

theory SchnorrProtocol.
clone import IdentificationProtocol with
type sk_t <- Group.FD.F.t,
type pk_t <- Group.group.
print Group.FD.FDistr.dt.
print Group.FD.F.
module SchnorrGen : G = {
  proc generate () : Group.FD.F.t * Group.group  = {
  var alpha, u;
    alpha <$ Group.FD.F.FDistr.dt;
    u <-  Group.g^alpha;
    return (alpha, u);
    }
  }.

module SchnorrProver : P = {
  var s : Group.FD.F.t
  proc setup (secret: Group.FD.F.t) : unit = {
    s <- secret;
  }
}.

module SchnorrVerifier : V = {
  var p : Group.group
  var u_t : Group.group
  var a_z : Group.FD.F.t
  var c : Group.FD.F.t
  
  proc setup (image: Group.group) : unit = {
    p <- image;
    (* Init other variables to something? *)
    
  }

  proc output () : bool = {
    return (Group.g^a_z = u_t^c);
  }
}.
print Protocol.
module SchnorrInteraction : I = {
  proc interact = 
}
