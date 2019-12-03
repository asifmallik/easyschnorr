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

print IdentificationProtocol.

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
      o <- FieldPacket r3;
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

lemma correctness &m : Pr[Protocol(SchnorrGen, SchnorrProver, SchnorrVerifier).run() @ &m : res.`2] = 1%r.
proof.
  byphoare; [ | trivial | trivial].
  proc. inline*. auto. unroll 13. unroll 14.
  seq 14 : (Group.g ^ SchnorrVerifier.a_z =
  SchnorrVerifier.u_t * SchnorrVerifier.u ^ SchnorrVerifier.c /\ terminate).
  auto. rcondt 13. auto. rcondt 14; auto. rcondt 21; auto. rcondt 30; auto.
  rcondf 31; auto. rcondf 37; auto. simplify. rewrite FDistr.dt_ll; simplify.
  rewrite /predT; simplify. smt.
  while (terminate /\ Group.g ^ SchnorrVerifier.a_z = SchnorrVerifier.u_t
  * SchnorrVerifier.u ^ SchnorrVerifier.c ) 0. move=>z.
  auto. exfalso; smt. skip. move => &h [a ->] //=. hoare. rcondt 13; auto.
  rcondt 14; auto. rcondt 21; auto. rcondt 30; auto. rcondf 31; auto.
  rcondf 37; auto. smt. trivial. qed.

  
(* Theorem 19.1 with C = Z_q -> super-poly *)
(* Instead of putting "DL is hard" as an axiom, reduction lemma. *)

module DLAdv(Adv : IdentificationProtocol.DirectAdversary) : DiffieHellman.CDH.Adversary = {
  proc solve (gx: G.group, gy : G.group) : G.group = {
      return G.g; (* Placeholder *)
   }
}.

lemma secure_direct:
    forall (Adv <: IdentificationProtocol.DirectAdversary) &m,
    Pr[IdentificationProtocol.DirectAttack(SchnorrGen, Adv, SchnorrVerifier).run() @ &m : res.`2]
    = Pr[DiffieHellman.CDH.CDH(DLAdv(Adv)).main() @ &m : res].

proof.
  admit.
qed.
