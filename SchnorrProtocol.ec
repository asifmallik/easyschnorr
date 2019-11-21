(*
 * Schnorr's identification protocol.
 * Boneh & Shoup, Figure 19.1
 *)

require import Int.
require import DiffieHellman.
print DiffieHellman.G.
clone export DiffieHellman.G as Group.

type t = Group.FD.F.t.
type group = Group.group.
type packet_t = [GroupPacket of group | FieldPacket of t].

require import IdentificationProtocol.

theory SchnorrProtocol.
clone import IdentificationProtocol with
type sk_t <- t,
type pk_t <- group,
type packet_t <- packet_t.

op get_field_packet (p) : t =
with p = FieldPacket t => t with p = GroupPacket t => witness.  

op get_group_packet (p) : group =
with p = GroupPacket t => t with p = FieldPacket t => witness.  

module SchnorrGen : G = {
  proc generate () : t * group  = {
  var alpha, u;
    alpha <$ Group.FD.FDistr.dt;
    u <-  Group.g^alpha;
    return (alpha, u);
    }
  }.

module SchnorrProver : P = {
  var a : t
  var a_t : t
  var step : int

  proc setup (secret: Group.FD.F.t) : unit = {
    a <- secret;
    step <- 1;
  }

  proc stepOne() : Group.group = {
      a_t <$ Group.FD.FDistr.dt;
      return Group.g^a_t;
  }

  proc stepThree(c : t) : t = {
      return a_t + a*c;
  } 

  proc next_step (prev_packet : packet_t) : packet_t = {
    var r1, r3, o;
    if (step = 1) {
      r1 <@ stepOne();
      o <- GroupPacket r1;
      step = 3;
    } else {      
      r3 <@ stepThree(get_field_packet prev_packet);
    }
    return o;
  }

}.

module SchnorrVerifier : V = {
  var u : Group.group
  var u_t : Group.group
  var a_z : Group.FD.F.t
  var c : Group.FD.F.t
  var step : int
  proc setup (image: Group.group) : unit = {
    u <- image;
    (* Init other variables to something? *)
    step <- 2;
  }

  proc stepTwo (u_t' : Group.group) : Group.FD.F.t = {
      u_t <- u_t';
      c <$ Group.FD.FDistr.dt; (* TODO: replace with a subset of Z_q, C *)
      return c;
  }

  proc stepFour( a_z' : Group.FD.F.t) = {
    a_z <- a_z';
  }

  proc next_step (prev_packet : packet_t) : bool * packet_t = {
    var r2,r4;
    var o1, o2;
    if (step = 2) {
      r2 <@ stepTwo(get_group_packet prev_packet);
      o2 <- FieldPacket r2;
      step = 4;
      o1 = false;
    } else {
      r4 <@ stepFour(get_field_packet prev_packet);
      o2 <- witness;
      o1 = true;
    }
    return (o1,o2);
  } 
  
  proc output () : bool = {
    return (Group.g^a_z = u_t * u^c);
  }
}.

lemma correctness &m : Pr[Protocol(SchnorrGen, SchnorrProver, SchnorrVerifier).run() @ &m : res] = 1%r. proof. admit. qed. 
