(*
 * Schnorr's identification protocol.
 * Boneh & Shoup, Figure 19.1
 *)

require import Int AllCore.
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

lemma correctness &m :
    Pr[Protocol(SchnorrGen, SchnorrProver, SchnorrVerifier).run() @ &m : res.`2] = 1%r.
    
proof.
  (* Transform in a pRHL statement *)  
  byphoare; [ | trivial | trivial].

  (* Write all the protocol steps *)
  proc. inline*. auto. unroll 13. unroll 14.

  (* Split into two HL goals at step 14 *)
  seq 14 : (Group.g ^ SchnorrVerifier.a_z =
  SchnorrVerifier.u_t * SchnorrVerifier.u ^ SchnorrVerifier.c /\ terminate).

  (* First 14 steps *)
   auto. rcondt 13. auto. rcondt 14; auto. rcondt 21; auto. rcondt 30; auto.
   rcondf 31; auto. rcondf 37; auto. simplify. rewrite FDistr.dt_ll; simplify.
   rewrite /predT; simplify. smt.

  (* Rest of the steps *)
   while (terminate /\ Group.g ^ SchnorrVerifier.a_z = SchnorrVerifier.u_t
   * SchnorrVerifier.u ^ SchnorrVerifier.c ) 0. move=>z.
   auto. exfalso; smt. skip. move => &h [a ->] //=.
   hoare. (* Transform pRHL with bound 0 into HL *) 
   rcondt 13; auto.
   rcondt 14; auto. rcondt 21; auto. rcondt 30; auto. rcondf 31; auto.
   rcondf 37; auto. smt. trivial.
qed.



section DirectSecurity.

  declare module A : IdentificationProtocol.DirectAdversary.

  (* Theorem 19.1 with C = Z_q -> super-poly *)
  (* Instead of putting "DL is hard" as an axiom, reduction lemma. *)

  (* TODO: Discrete Log *)
  local module B : DiffieHellman.CDH.Adversary = {
    proc solve (gx: G.group, gy : G.group) : G.group = {

    (*  CDH.CDH(A0).main.r = G.g ^ (CDH.CDH(A0).main.x * CDH.CDH(A0).main.y) *)
        
      return G.g; (* Placeholder *)
    }
  }.

  (* TODO: Add notations in the lemma *)

  (* A's advantage in the direct attack game *)
  (* op eps = Pr[IdentificationProtocol.DirectAttack(SchnorrGen, Adv, SchnorrVerifier).run() : res.`2]%r. *)
  (* B's advantage in the DL game *)
  (* op eps' = Pr[DiffieHellman.CDH.CDH(B).main() @ &m : res].*)
  (* op N = Group.FD.F.q. (* C = Z_q here *) *)

  print DiffieHellman.

  local lemma secure_direct &m:
    Pr[DiffieHellman.CDH.CDH(B).main() @ &m : res] >=
    Pr[IdentificationProtocol.DirectAttack(SchnorrGen, A, SchnorrVerifier).run() @ &m : res.`2]*(Pr[IdentificationProtocol.DirectAttack(SchnorrGen, A, SchnorrVerifier).run() @ &m : res.`2] - 1%r/(Group.FD.F.q)%r).
  proof.
    admit.
  qed.

end section DirectSecurity.
