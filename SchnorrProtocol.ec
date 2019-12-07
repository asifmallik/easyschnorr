(*
 * Schnorr's identification protocol.
 * Boneh & Shoup, Figure 19.1
 *)

require import Int AllCore.
require import CyclicGroup.
require import DLog.
require import List.
type t = CyclicGroup.FD.F.t.
type group = CyclicGroup.group.
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
    alpha <$ CyclicGroup.FD.FDistr.dt;
    u <-  CyclicGroup.g^alpha;
    return (alpha, u);
    }
  }.

module SchnorrProver : P = {
  var a : t
  var a_t : t
  var step : int

  proc setup (secret: CyclicGroup.FD.F.t) : unit = {
    a <- secret;
    step <- 1;
  }

  proc stepOne() : CyclicGroup.group = {
      a_t <$ CyclicGroup.FD.FDistr.dt;
      return CyclicGroup.g^a_t;
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
  var u : CyclicGroup.group
  var u_t : CyclicGroup.group
  var a_z : CyclicGroup.FD.F.t
  var c : CyclicGroup.FD.F.t
  var step : int
  proc setup (image: CyclicGroup.group) : unit = {
    u <- image;
    step <- 2;
  }

  proc stepTwo (u_t' : CyclicGroup.group) : CyclicGroup.FD.F.t = {
      u_t <- u_t';
      c <$ CyclicGroup.FD.FDistr.dt; (* TODO: replace with a subset of Z_q, C *)
      return c;
  }

  proc stepFour( a_z' : CyclicGroup.FD.F.t) = {
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
    return (CyclicGroup.g^a_z = u_t * u^c);
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
  seq 14 : (CyclicGroup.g ^ SchnorrVerifier.a_z =
  SchnorrVerifier.u_t * SchnorrVerifier.u ^ SchnorrVerifier.c /\ terminate).

  (* First 14 steps *)
   auto. rcondt 13. auto. rcondt 14; auto. rcondt 21; auto. rcondt 30; auto.
   rcondf 31; auto. rcondf 37; auto. simplify. rewrite FDistr.dt_ll; simplify.
   rewrite /predT; simplify. smt.

  (* Rest of the steps *)
   while (terminate /\ CyclicGroup.g ^ SchnorrVerifier.a_z = SchnorrVerifier.u_t
   * SchnorrVerifier.u ^ SchnorrVerifier.c ) 0. move=>z.
   auto. exfalso; smt. skip. move => &h [a ->] //=.
   hoare. (* Transform pRHL with bound 0 into HL *) 
   rcondt 13; auto.
   rcondt 14; auto. rcondt 21; auto. rcondt 30; auto. rcondf 31; auto.
   rcondf 37; auto. smt. trivial.
qed.



section DirectSecurity.

  declare module A : IdentificationProtocol.DirectAdversary {SchnorrVerifier}.
  declare module Ar : IdentificationProtocol.DirectAdversary {SchnorrVerifier}.
  
  (* Theorem 19.1 with C = Z_q -> super-poly *)
  (* Instead of putting "DL is hard" as an axiom, reduction lemma. *)
  
  print DLog.
  print CyclicGroup.
  local module B : DLog.StdAdversary = {
    proc guess (h : CyclicGroup.group) : F.t = {        
      return CyclicGroup.FD.F.one; (* Placeholder *)
    }
  }.

  (* TODO: Add notations in the lemma *)

  (* A's advantage in the direct attack game *)
  (* op eps = Pr[IdentificationProtocol.DirectAttack(SchnorrGen, Adv, SchnorrVerifier).run() : res.`2]%r. *)
  (* B's advantage in the DL game *)
  (* op eps' = Pr[DiffieHellman.CDH.CDH(B).main() @ &m : res].*)
  (* op N = Group.FD.F.q. (* C = Z_q here *) *)
  
  axiom A_setup_ll : islossless A.setup.
  axiom Ar_setup_ll : islossless Ar.setup.
  
  module SimplifiedDirectAttackGame(Adv: IdentificationProtocol.DirectAdversary) = {
    proc run() = {
    var c,u_t,a_z,pk,sk,p,o,transcript;
    sk <$ FDistr.dt;    
    pk <- g ^ sk;         
    Adv.setup(pk);            
    p <- packet;          
    transcript <- [];  
    p <@ Adv.next_step(p);
    transcript <- p :: transcript;
    u_t <- get_group_packet p;
    c <$ FDistr.dt;           
    p <- FieldPacket c;
    transcript <- p :: transcript;    
    p <@ Adv.next_step(p);
    transcript <- p :: transcript;        
    a_z <- get_field_packet p;   
    p <- witness;
    transcript <- p :: transcript;     
    o <- g ^ a_z = u_t * pk ^ c;
    return (transcript, o);
    }
  }.

  module RewindingGame (Adv : IdentificationProtocol.DirectAdversary, AdvRewinded : IdentificationProtocol.DirectAdversary) = {
    proc run() = {
      var c1,c2,pk,sk,p;
      sk <$ FDistr.dt;    
      pk <- g ^ sk;         
      Adv.setup(pk);            
      p <- packet;          
      c1 <@ Adv.next_step(p);
      p <- packet;
      AdvRewinded.setup(pk);
      c2 <@ AdvRewinded.next_step(p);
      return c1 = c2;
    }
  }.

  axiom adversary_rewinding &m : hoare[RewindingGame(A, Ar).run : true ==> res].
  axiom adversary_equivalence &m : equiv[SimplifiedDirectAttackGame(A).run ~ SimplifiedDirectAttackGame(Ar).run : true ==> ={res}].

  local lemma eq_simplified_direct_attack_game &m :
    equiv[IdentificationProtocol.DirectAttack(SchnorrGen, A, SchnorrVerifier).run ~
    SimplifiedDirectAttackGame(A).run : ={glob A} ==> ={res}].
      proof.
        proc. inline *. sim. unroll{1} 11. unroll{1} 12.
        seq 12 18 : (terminate{1} /\ ={transcript} /\
        SchnorrVerifier.a_z{1} = a_z{2} /\
        SchnorrVerifier.c{1} = c{2} /\
        SchnorrVerifier.u_t{1} = u_t{2} /\
        SchnorrVerifier.u{1} = pk{2}).
        auto. rcondt{1} 11. move=> _. auto. call (_: true).
        auto. rcondt{1} 14; auto. call(_:true).
        auto. call(_:true). auto. rcondt{1} 23; auto.
        call(_:true); auto. rcondf{1} 26; auto.
        call(_:true). auto. call(_:true). auto.
        sim. auto. sim.
        while{1} (terminate{1} /\ ={transcript} /\
        SchnorrVerifier.a_z{1} = a_z{2} /\
        SchnorrVerifier.c{1} = c{2} /\
        SchnorrVerifier.u_t{1} = u_t{2} /\
        SchnorrVerifier.u{1} = pk{2} ) 0.
      move=> &c d. exfalso; smt. skip. smt. qed. 

    local lemma secure_direct &m:
    Pr[DLog.DLogStdExperiment(B).main() @ &m : res] >=
    Pr[IdentificationProtocol.DirectAttack(SchnorrGen, A, SchnorrVerifier).run() @ &m : res.`2]*(Pr[IdentificationProtocol.DirectAttack(SchnorrGen, A, SchnorrVerifier).run() @ &m : res.`2] - 1%r/(CyclicGroup.FD.F.q)%r).
  proof.
    admit.
  qed.

end section DirectSecurity.
