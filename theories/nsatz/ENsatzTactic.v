Require Import List.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import Znumtheory.
Require Export Morphisms Setoid Bool.
Require Export Algebra_syntax.
Require Export Ncring.
Require Export Ncring_initial.
Require Export Ncring_tac.
Require Export Integral_domain.
Require Import ZArith.

Declare ML Module "nsatz_core_plugin:coq-core.plugins.nsatz_core".
Declare ML Module "nsatz_plugin:coq-core.plugins.nsatz".

Section nsatz1.

Context {R:Type}`{Rid:Integral_domain R}.

Lemma psos_r1b: forall x y:R, x - y == 0 -> x == y.
intros x y H; setoid_replace x with ((x - y) + y); simpl;
  [setoid_rewrite H | idtac]; simpl.
- cring.
- cring.
Qed.

Lemma psos_r1: forall x y, x == y -> x - y == 0.
intros x y H; simpl; setoid_rewrite H; simpl; cring.
Qed.

Lemma nsatzR_diff: forall x y:R, not (x == y) -> not (x - y == 0).
intros.
intro; apply H.
simpl; setoid_replace x with ((x - y) + y).
- simpl.
  setoid_rewrite H0.
  simpl; cring.
- simpl. simpl; cring.
Qed.

(* adpatation du code de Benjamin aux setoides *)
Export Ring_polynom.
Export InitialRing.

Definition PolZ := Pol Z.
Definition PEZ := PExpr Z.

Definition P0Z : PolZ := P0 (C:=Z) 0%Z.

Definition PolZadd : PolZ -> PolZ -> PolZ :=
  @Padd  Z 0%Z Z.add Zeq_bool.

Definition PolZmul : PolZ -> PolZ -> PolZ :=
  @Pmul  Z 0%Z 1%Z Z.add Z.mul Zeq_bool.

Definition PolZeq := @Peq Z Zeq_bool.

Definition norm :=
  @norm_aux Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zeq_bool.

Fixpoint mult_l (la : list PEZ) (lp: list PolZ) : PolZ :=
 match la, lp with
 | a::la, p::lp => PolZadd (PolZmul (norm a) p) (mult_l la lp)
 | _, _ => P0Z
 end.

Fixpoint compute_list (lla: list (list PEZ)) (lp:list PolZ) :=
 match lla with
 | List.nil => lp
 | la::lla => compute_list lla ((mult_l la lp)::lp)
 end.

Definition check (lpe:list PEZ) (qe:PEZ) (certif: list (list PEZ) * list PEZ) :=
 let (lla, lq) := certif in
 let lp := List.map norm lpe in
 PolZeq (norm qe) (mult_l lq (compute_list lla lp)).

(* Correction *)
Definition PhiR : list R -> PolZ -> R :=
  (Pphi ring0 add mul
    (InitialRing.gen_phiZ ring0 ring1 add mul opp)).

Definition PEevalR : list R -> PEZ -> R :=
   PEeval ring0 ring1 add mul sub opp
    (gen_phiZ ring0 ring1 add mul opp)
         N.to_nat pow.

Lemma P0Z_correct : forall l, PhiR l P0Z = 0.
Proof. trivial. Qed.

Lemma Rext: ring_eq_ext add mul opp _==_.
Proof.
constructor; solve_proper.
Qed.

Lemma Rset : Setoid_Theory R _==_.
apply ring_setoid.
Qed.

Definition Rtheory:ring_theory ring0 ring1 add mul sub opp _==_.
apply mk_rt.
- apply ring_add_0_l.
- apply ring_add_comm.
- apply ring_add_assoc.
- apply ring_mul_1_l.
- apply cring_mul_comm.
- apply ring_mul_assoc.
- apply ring_distr_l.
- apply ring_sub_def.
- apply ring_opp_def.
Defined.

Lemma PolZadd_correct : forall P' P l,
  PhiR l (PolZadd P P') == ((PhiR l P) + (PhiR l P')).
Proof.
unfold PolZadd, PhiR. intros. simpl.
 refine (Padd_ok Rset Rext (Rth_ARth Rset Rext Rtheory)
           (gen_phiZ_morph Rset Rext Rtheory) _ _ _).
Qed.

Lemma PolZmul_correct : forall P P' l,
  PhiR l (PolZmul P P') == ((PhiR l P) * (PhiR l P')).
Proof.
unfold PolZmul, PhiR. intros.
 refine (Pmul_ok Rset Rext (Rth_ARth Rset Rext Rtheory)
           (gen_phiZ_morph Rset Rext Rtheory) _ _ _).
Qed.

Lemma R_power_theory
     : Ring_theory.power_theory ring1 mul _==_ N.to_nat pow.
apply Ring_theory.mkpow_th. unfold pow. intros. rewrite Nnat.N2Nat.id.
reflexivity. Qed.

Lemma norm_correct :
  forall (l : list R) (pe : PEZ), PEevalR l pe == PhiR l (norm pe).
Proof.
 intros;apply (norm_aux_spec Rset Rext (Rth_ARth Rset Rext Rtheory)
           (gen_phiZ_morph Rset Rext Rtheory) R_power_theory).
Qed.

Lemma PolZeq_correct : forall P P' l,
  PolZeq P P' = true ->
  PhiR l P == PhiR l P'.
Proof.
 intros;apply
   (Peq_ok Rset Rext (gen_phiZ_morph Rset Rext Rtheory));trivial.
Qed.

Fixpoint Cond0 (A:Type) (Interp:A->R) (l:list A) : Prop :=
  match l with
  | List.nil => True
  | a::l => Interp a == 0 /\ Cond0 A Interp l
  end.

Fixpoint BFType (A : Type) (l : list A) {struct l} : Type :=
  match l with
  | nil => unit
  |  _ :: l0 =>  (R * BFType A l0)%type
  end.

Fixpoint BCond0 (A : Type) (Interp : A -> R) (l : list A) {struct l} : (BFType A l -> R) :=
  match l return (BFType A l -> R) with
| nil => (fun _ => ring0)
| a :: l0 => (fun n => add (mul (fst n) (Interp a))
                             (BCond0 A Interp l0 (snd n)))
end.

Definition mk_BCond0 (A : Type) (Interp : A -> R) (l : list A) (v : R) :=
  exists n, (v == BCond0 A Interp l n).

Fixpoint ring0_tuple (A :Type) (l: list A) : BFType A l :=
  match l return (BFType A l) with
  | nil => tt
  | a :: q => (ring0, ring0_tuple A q)
  end.

(* The type of the existential *)

Fixpoint FType (A : Type) (l : list (bool * A)) {struct l} : Type :=
  match l with
  | nil => unit
  | (true, _) :: l0 =>  (R * FType A l0)%type
  | (false,_)  :: l0 =>  FType A l0
  end.

(* For the conclusion *)

Fixpoint GCond0 (A : Type) (Interp : A -> R) (l : list (bool * A)) {struct l} : (FType A l -> R) :=
  match l return (FType A l -> R) with
| nil => (fun _ => ring0)
| (true, a) :: l0 => (fun n => add (mul (fst n) (Interp a))
                             (GCond0 A Interp l0 (snd n)))
| (false, a) :: l0 => GCond0 A Interp l0
end.

Definition mk_GCond0 (A : Type) (Interp : A -> R) (l : list (bool * A)) (v : R) :=
  exists n, (v == GCond0 A Interp l n).

(* For the assumptions *)

Fixpoint mk_HCond0 (A : Type) (Interp : A -> R) (l : list (bool * A)) {struct l} : Prop :=
  match l with
  | nil => True
  | (true, a) :: l0 => (mk_HCond0 A Interp l0)
  | (false, a) :: l0 => ((Interp a) == 0) /\ (mk_HCond0 A Interp l0)
  end.

Fixpoint add_coef
  (A : Type)
  (Interp : A -> R)
  (l: list A)  (a : list A)
  (c : R) {struct l} : (BFType A l -> BFType A l) :=
  match l, a return  (BFType A l -> BFType A l) with
  | nil, _ => (fun _ => tt)
  | _, nil => (fun x => x)
  | h :: q , hx :: qx =>
      let coef := c * (Interp hx) in
      fun x => (coef + fst x, add_coef A Interp q qx c (snd x))
  end.

Lemma factories_compute_list :
  forall lla l lpe lq,
  mk_BCond0 PolZ (PhiR l) lpe
    (PhiR l (mult_l lq (compute_list lla lpe))).
Proof.
  unfold mk_BCond0.
  induction lla.
  - induction lpe.
    + destruct lq;simpl;exists tt; reflexivity.
    + intros;simpl.
      destruct lq.
      * simpl.
        simpl in IHlpe.
        specialize (IHlpe nil) as (x,H).
        exists (ring0,x).
        rewrite <- H.
        cring.
      * simpl.
        simpl in IHlpe.
        specialize (IHlpe lq) as (x, H).
        exists (PhiR l (norm p),x).
        rewrite  PolZadd_correct.
        rewrite PolZmul_correct.
        rewrite <- H.
        cring.
   - intros. simpl.
     specialize (IHlla l (mult_l a lpe :: lpe) lq).
     destruct IHlla.
     simpl in H.
     exists (add_coef PolZ (PhiR l) lpe (map norm a) (fst x) (snd x)).
     rewrite H. clear H.
     destruct x.
     simpl.
     generalize dependent lpe.
     induction a.
     + intros; destruct lpe; cring.
     + intros.
       destruct lpe;[ cring |].
       simpl.
       rewrite PolZadd_correct.
       rewrite PolZmul_correct.
       specialize (IHa lpe (snd b)).
       rewrite <- IHa.
       cring.
Qed.

Fixpoint btype_to_ftype
  (A B : Type)
  (norm :  A -> B)
  (l: list (bool*A)) {struct l} : (BFType B (map norm (map snd l)) -> FType A l) :=
  match l return  (BFType B (map norm (map snd l)) -> FType A l) with
  | nil => fun _ => tt
  | (true,a) :: q =>  fun x => (fst x, btype_to_ftype A B norm  q (snd x))
  | (false,a) :: q =>  fun x => (btype_to_ftype A B norm q (snd x))
  end.

Lemma check_correct_exists :
  forall l lpe qe lci lq ,
    check (map snd lpe) qe (lci,lq) = true ->
    mk_HCond0 PEZ (PEevalR l) lpe ->
    mk_GCond0 PEZ (PEevalR l) lpe (PEevalR l qe).
Proof.
  unfold check;intros l lpe qe lla lq H2 H1.
  apply PolZeq_correct with (l:=l) in H2.
  unfold mk_GCond0.
  specialize (factories_compute_list lla l (map norm (map snd lpe)) lq) as H.
  unfold mk_BCond0 in H. destruct H.
  rewrite H in H2.
  clear H.
  exists (btype_to_ftype PEZ PolZ norm lpe x).
  rewrite norm_correct.
  rewrite H2.
  clear H2.
  induction lpe.
  - cring.
  - destruct a.
    destruct b.
    + simpl in H1.
      destruct x.
      specialize (IHlpe b H1).
      simpl.
      rewrite IHlpe.
      rewrite norm_correct.
      reflexivity.
    + destruct H1.
      destruct x.
      specialize (IHlpe b H0).
      simpl.
      rewrite IHlpe.
      rewrite <- norm_correct.
      rewrite H.
      cring.
Qed.

End nsatz1.

Fixpoint get_lpol (g: list (PExpr Z)) :=
  match g with
  | nil => nil
  | (PEc ring0) :: p => get_lpol p
  | p1 :: p2 =>  let l := get_lpol p2 in p1 :: l
  end.

Fixpoint set_false (l: list (PExpr Z)) :=
  match l with
  | nil => nil
  | h :: q => (false, h) :: (set_false q)
  end.

Fixpoint set_true (l: list (PExpr Z)) :=
  match l with
  | nil => nil
  | h :: q => (true, h) :: (set_true q)
  end.

Lemma efactor:
  forall A B P,  (exists x : A * B, P (fst x) (snd x)) -> (exists x : A, exists y: B, P x y).
Proof.
  intros A B P [x H].  eauto.
Qed.

Lemma efactor1:
  forall A B P,  (exists x : A, exists y: B, P (x, y)) -> (exists x : A * B, P x).
Proof.
intros A B P [x [y HP]]; exists (x, y); auto.
Qed.

Lemma emove:
  forall  A P1 P2 P3 a,
  (exists x : A, P1 x = ((P2 x)  + (P3 x) * a)%Z) <->
    (exists x: A,  (P1 x - ((P3 x) * a))%Z = (P2 x)%Z).
Proof.
  intros.
  split.
  + intros [x H].
    exists x.
    rewrite H.
    cring.
  + intros [x H].
    exists x.
    rewrite <- H.
    cring.
Qed.

Fixpoint acc l1 l2:=
  match l1, l2 with
  | nil, _ => 0
  | _, nil => 0
  | h1 :: q1, h2 :: q2 => h2 * h1 + (acc q1 q2)
  end.

Lemma acc_s A P1 P2 P3 a l:
  (exists x : A, P1 x = (acc l (P2 x)  + (P3 x) * a)%Z) <->
    (exists x: A, P1 x =  (acc (a :: l) ((P3 x) :: P2 x))%Z).
Proof.
  split;
    intros [x H];
    exists x;
    rewrite H;
    simpl;
    cring.
Qed.

Lemma acc_id A P1 P2  a:
  (exists x : A, P1 x = ((P2 x) * a)%Z) <->
    (exists x: A, P1 x =  (acc (a :: nil) (( P2 x) :: nil))%Z).
Proof.
  split;
  intros [x H];
  exists x;
  rewrite H;
  simpl;
  cring.
Qed.

Lemma acc_nil a: acc a nil = 0.
Proof. destruct a;auto. Qed.

Lemma acc_concat a0 a b0 b:
  List.length a0 = List.length b0 ->
  acc (a0 ++ a :: nil) (b0 ++ b :: nil) = acc a0 b0 + a * b.
Proof.
generalize dependent b0.
induction a0;intros.
- inversion H.
  destruct b0.
  + simpl.
    cring.
  + inversion H1.
- destruct b0.
  + inversion H.
  + inversion H.
    specialize (IHa0 b0 H1).
    simpl.
    rewrite IHa0.
    cring.
Qed.

Lemma acc_rev a b:
  List.length a = List.length b ->
  acc a b = acc (List.rev a) (List.rev b).
Proof.
  generalize dependent b.
  induction a; intros.
  - reflexivity.
  - destruct b.
    + inversion H.
    + inversion H.
      specialize (IHa b H1).
      simpl.
      rewrite acc_concat.
      rewrite IHa.
      cring.
      repeat rewrite length_rev.
      assumption.
Qed.

Lemma modulo1 a b c: a mod b = c -> exists k:Z, (a - c)%Z = k*b.
Proof.
  intros.
  destruct (Z.eq_dec b 0) as [H1 | H1].
    - subst.
      exists 0%Z.
      rewrite Zmod_0_r.
      rewrite Z.sub_diag.
      rewrite Z.mul_0_l.
      trivial.
    - specialize (Zmod_divides (a -c)%Z b H1).
      rewrite Zminus_mod.
      rewrite H.
      rewrite Zminus_mod_idemp_r.
      rewrite Z.sub_diag.
      rewrite Zmod_0_l.
      intros [H2 _].
      destruct (H2 eq_refl).
      exists x.
      rewrite Z.mul_comm.
      trivial.
Qed.

Lemma modulo2 a b c:  (exists k:Z, (a - c)%Z = k*b) -> a mod b = c mod b.
Proof.
  intros. destruct H.
  rewrite Z.sub_move_r in H.
  subst.
  rewrite Z.add_comm.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

Lemma div1 a b : (a | b)%Z  -> (exists k:Z, b = k*a).
Proof.
  intros.
  destruct (Z.eq_dec a 0) as [H1 | H1].
    - subst.
      exists 0%Z.
      apply Z.divide_0_l in H.
      subst. reflexivity.
    - apply Zdivide_mod in H.
      apply (Zmod_divides _ _ H1 ) in H.
      destruct H.
      rewrite Z.mul_comm in H.
      exists x. trivial.
Qed.

Lemma div2 a b : (exists k:Z, b = k*a) -> (a | b)%Z.
Proof.
 intros.
 destruct (Z.eq_dec a 0) as [H1 | H1].
    - subst.
      destruct H.
      rewrite Z.mul_0_r in H.
      subst.
      apply Z.divide_0_r.
    - assert (H': exists k:Z, b = a * k).
      destruct H. exists x. rewrite Z.mul_comm. trivial.
      apply (Zmod_divides _ _ H1) in H'.
      apply (Zmod_divide _ _ H1 H').
Qed.

(* coprime: idendité de bezout *)

Ltac equality_to_goal H x y:=
  (* eliminate trivial  hypotheses, but it takes time!:
  let h := fresh "nH" in
    (assert (h:equality x y);
    [solve [cring] | clear H; clear h])
  || *) try (generalize (@psos_r1 _ _ _ _ _ _ _ _ _ _ _ x y H); clear H)
.

Ltac div_to_equality H x y :=
  try (apply (div1 x y) in H)
.

Ltac mod_to_equality H x y z:=
  try (apply (modulo1 x y z) in H)
.

Ltac divs_to_equalities :=
  lazymatch goal with
  |  H: (?x | ?y) |- _ => div_to_equality H x y
   end.

Ltac mods_to_equalities :=
  lazymatch goal with
  |  H: (?z = ?x mod ?y) |- _ => apply symmetry in H
  |  H: (?x mod ?y = ?z) |- _ => mod_to_equality H x y z
  end.

Ltac exists_to_equalities :=
  lazymatch goal with
  | H: (exists e: ?A, ?b1) |- _ => destruct H
  end.

Ltac equalities_to_goal :=
  lazymatch goal with
  |  H: (_ ?x ?y) |- _ => equality_to_goal H x y
  |  H: (_ _ ?x ?y) |- _ => equality_to_goal H x y
  |  H: (_ _ _ ?x ?y) |- _ => equality_to_goal H x y
  |  H: (_ _ _ _ ?x ?y) |- _ => equality_to_goal H x y
  (* extension possible :-) *)
  |  H: (?x == ?y) |- _ => equality_to_goal H x y
   end.

Ltac parametres_en_tete fv lp :=
    match fv with
     | (@nil _)          => lp
     | (@cons _ ?x ?fv1) =>
       let res := AddFvTail x lp in
         parametres_en_tete fv1 res
    end.

Ltac append1 a l :=
 match l with
 | (@nil _)     => constr:(cons a l)
 | (cons ?x ?l) => let l' := append1 a l in constr:(cons x l')
 end.

Ltac rev l :=
  match l with
   |(@nil _)      => l
   | (cons ?x ?l) => let l' := rev l in append1 x l'
  end.

Ltac lterm g :=
  match g with
  | (exists e: ?A, ?b1%Z = acc ?l1 ?l2) => constr:((l1))
  | ?b1 == ?b2 -> ?g => let l := lterm g in
                        constr:((b1 :: b2 :: l))
  end.

Ltac nsatz_call_n info nparam p rr lp kont :=
(*  idtac "Trying power: " rr;*)
  let ll := constr:(PEc info :: PEc nparam :: PEpow p rr :: lp) in
(*  idtac "calcul...";*)
  nsatz_compute ll;
(*  idtac "done";*)
  match goal with
  | |- (?c::PEpow _ ?r::?lq0)::?lci0 = _ -> _ =>
    intros _;
    let lci := fresh "lci" in
    set (lci:=lci0);
    let lq := fresh "lq" in
    set (lq:=lq0);
    kont c rr lq lci
  end.

Ltac nsatz_call radicalmax info nparam p lp kont :=
  let rec try_n n :=
    lazymatch n with
    | 0%N => fail
    | _ =>
        (let r := eval compute in (N.sub radicalmax (N.pred n)) in
         nsatz_call_n info nparam p r lp kont) ||
         let n' := eval compute in (N.pred n) in try_n n'
    end in
  try_n radicalmax.

Ltac ensatz :=
  intros;
  match goal with
  | |- ?x mod ?n = ?y mod ?n => apply modulo2
  | |- (?x | ?y) => apply div2
  | |- ?g => idtac
  end;
  repeat mods_to_equalities;
  repeat divs_to_equalities;
  repeat exists_to_equalities;
  repeat apply efactor;
  repeat rewrite emove;
  repeat rewrite acc_id;
  repeat (rewrite <- emove; rewrite acc_s);
  repeat equalities_to_goal;
  match goal with
    |- ?g =>
      let lb := lterm g in
      intros;
      match goal with
      | |- (exists e: ?A, ?b1%Z = acc ?l1 ?l2) =>
          let lb := constr: ((b1 :: lb)) in
          match (list_reifyl0 lb) with
          |(?fv, ?le) =>
             let lv := fresh "lv" in
             set(lv := fv);
             let lpol := eval compute in  (get_lpol le) in
             let SplitPolyList kont :=
               match lpol with
               | ?p2::?lp2 =>
                 let lp2 := eval compute in (List.rev lp2) in
                 kont p2 lp2
          | _ => idtac "polynomial not in the ideal"
          end
            in
            SplitPolyList
              ltac:(fun p lp =>
                      let p21 := fresh "p21" in
                      let lp21 := fresh "lp21" in
                      set (p21:=p) ;
                      set (lp21:=lp);
                      nsatz_call
                        6%N 1%Z 0%Z p lp
                        ltac:(fun c r lq lci =>
                                let Hg := fresh "Hg" in
                                assert (Hg:check lp p (lci,lq) = true);
                                [vm_compute ;reflexivity |
                                  match goal with
                                  | |- (exists e: ?A, ?b1%Z = acc ?l1 ?l2) =>
                                      let nte := eval compute in (List.length l1) in
                                        let hd := eval compute in (firstn nte lp21) in
                                          let hdt := eval compute in (set_true hd) in
                                            let tl := eval compute in (skipn nte lp21) in
                                              let tlf:= eval compute in (set_false tl) in
                                                let pl := eval compute in (hdt ++ tlf) in
                                                  assert (Hg2: mk_HCond0 PEZ (PEevalR lv) pl);
                                                  [repeat (split;[assumption|idtac]); exact I|];
                                                                          generalize (@check_correct_exists _ _ _ _ _ _ _ _ _ _ _ lv  pl  p21 lci lq Hg Hg2)
                                  end;
                                  unfold mk_GCond0;
                                  intros H1;
                                  repeat apply efactor1;
                                  simpl in H1;
                                  destruct H1;
                                  repeat (match goal with x0 : (_ * _)%type |- _ => destruct x0 end);
                                  simpl in H1;
                                  erewrite H1;
                                  repeat eexists;
                                  erewrite acc_rev;
                                  repeat reflexivity
                                ]
                             )
                   )
      end
  end
end.

Example test a n x y d u v:
  (a * y - a* x = n * d -> a * u + n * v = 1 -> exists e, y - x = e * n)%Z.
Proof.
  ensatz.
Qed.

Example test2 a n x y d u v m r:
  (a * y - a* x = n * d -> a * u + n * v = 1 ->
  exists e1, exists e2, exists e3, y - x = e3 * n  + e2 * r + e1 * m )%Z.
Proof.
 ensatz.
Qed.

Example test3 a n x y d u v m r t:
  (a * y - a* x = n * d -> a * u + n * v = 1 ->
  exists e3, exists e1, exists e4, exists e2, y - x = e3 * n  + e2 * r + e1 * m + e4 * t)%Z.
Proof.
  ensatz.
Qed.

Example test4 a n x y:
  (a * x = (a * y) mod n -> (exists e1 e2, a * e1 + n * e2 = 1) -> y mod n = x mod n)%Z.
Proof.
  ensatz.
Qed.
