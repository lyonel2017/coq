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
  | (PEc 0%Z) :: p => get_lpol p
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

Ltac equality_to_goal H x y:=
  (* eliminate trivial  hypotheses, but it takes time!:
  let h := fresh "nH" in
    (assert (h:equality x y);
    [solve [cring] | clear H; clear h])
  || *) try (generalize (@psos_r1 _ _ _ _ _ _ _ _ _ _ _ x y H); clear H)
.

Ltac equalities_to_goal :=
  lazymatch goal with
  |  H: (_ ?x ?y) |- _ => equality_to_goal H x y
  |  H: (_ _ ?x ?y) |- _ => equality_to_goal H x y
  |  H: (_ _ _ ?x ?y) |- _ => equality_to_goal H x y
  |  H: (_ _ _ _ ?x ?y) |- _ => equality_to_goal H x y
  (* extension possible :-) *)
  |  H: (?x == ?y) |- _ => equality_to_goal H x y
   end.

Ltac hterm g :=
  match g with
  | (exists _: _, _ ) => constr:((@nil Z))
  | ?b1 == ?b2 -> ?g => let l := hterm g in
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

Inductive Var {A: Type}: Type :=
| mRef: A -> Var
| fstVar :forall B,  @Var (A*B) -> @Var A
| sndVar : forall B, @Var (B*A) -> @Var A.

Ltac reify_evar_aux term :=
  match term with
  | (fun e => fst (@?P e)) =>
       let term' := reify_evar_aux P in
       constr:(fun x => @fstVar _ _ (term' x))
  | (fun e => snd (@?P e)) =>
      let term' := reify_evar_aux P in
      constr:(fun x => @sndVar _ _ (term' x))
  | (fun e:?T => e) => constr:(fun e :T => mRef e)
  end.

Inductive MPoly {var: Type}: Type:=
| Poly : MPoly -> Z -> @Var Z -> MPoly
| Pc : Z -> MPoly.

Ltac reify_evar term :=
  match term with
  | (fun e => fst _) =>
      let term' := reify_evar_aux term in
      constr:(fun e' => @Poly Z (@Pc Z 0%Z) (1%Z) (term' e'))
  | (fun e => snd _) =>
      let term' := reify_evar_aux term in
      constr:(fun e' => @Poly Z (@Pc Z 0%Z) (1%Z) (term' e'))
  | (fun e:?T => e) =>  constr:(fun e':T => @Poly T (@Pc Z 0%Z) (1%Z) (mRef e'))
  end.

Fixpoint mult_mpoly {A: Type} (c : Z) (p : @MPoly A) : @MPoly A :=
  match p with
  | Pc e => Pc (e * c)
  | Poly p e v => Poly (mult_mpoly c p) (e * c) v
  end.

Fixpoint equal {A1 A2: Type} (v1 : @Var A1) (v2 : @Var A2): comparison :=
    match v1, v2 with
    | mRef _, mRef _ => Eq
    | fstVar _ v1, fstVar _ v2 => equal v1 v2
    | sndVar _ v1, sndVar _ v2 => equal v1 v2
    | fstVar _ _, sndVar _ _ => Gt
    | sndVar _ _, fstVar _ _ => Lt
    | _, mRef _ => Gt
    | mRef _, _ => Lt
    end.

Inductive Monom {var: Type}: Type:=
| Mon : Z -> @Var Z -> Monom
| Monc : Z -> Monom.

Fixpoint add_monom_poly {A: Type} (p: @MPoly A) (m: @Monom A) :=
  match p with
  | Pc e1 =>
      match m with
      | Monc e2 => Pc (e1 + e2)
      | Mon e2 v => Poly p e2 v
      end
  | Poly p' e1 v1 =>
      match m with
      | Monc e2 => Poly (add_monom_poly p' m) e1 v1
      | Mon e2 v2 =>
          match equal v1 v2 with
          | Eq => Poly p' (e1 + e2) v1
          | Gt => Poly (add_monom_poly p' m) e1 v1
          | Lt => Poly p e2 v2
          end
      end
  end.

Fixpoint add_mpoly {A: Type} (p1 p2 : @MPoly A) : @MPoly A :=
  match p1 with
  | Pc e1 => add_monom_poly p2 (Monc e1)
  | Poly p1' e1 v1 => add_mpoly p1' (add_monom_poly p2 (Mon e1 v1))
  end.

Fixpoint opp_mpoly {A: Type} (p: @MPoly A) : @MPoly A :=
  match p with
  | Pc e => Pc (Z.opp e)
  | Poly p e v => Poly (opp_mpoly p) e v
  end.

Ltac reify_term term :=
  match term with
  | (fun e1 => (@?E1 e1 + @?E2 e1)%Z) =>
      let E1' := reify_term E1 in
      let E2' := reify_term E2 in
      constr:(fun x => add_mpoly (E1' x) (E2' x))
  | (fun e1 => (@?E1 e1 - @?E2 e1)%Z) =>
      let E1' := reify_term E1 in
      let E2' := reify_term E2 in
      constr:(fun x => add_mpoly (E1' x) (opp_mpoly (E2' x)))
  | (fun e1 => (?E * @?E1 e1)%Z) =>
      let E1' := reify_term E1 in
      constr:(fun x => mult_mpoly E (E1' x))
  | (fun e1 => (@?E1 e1 * ?E)%Z) =>
      let E1' := reify_term E1 in
      constr:(fun x => mult_mpoly E (E1' x))
  | (fun e => @?E e) => reify_evar E
  | (fun _:?T => ?E) => constr:(fun _:T => @Pc Z E)
  end.

Fixpoint get_coef {A:Type} (p: @MPoly A) :=
  match p with
  | Pc e => e :: nil
  | Poly p e v => e :: get_coef p
  end.

Definition coef {A:Type} (p: A -> @MPoly Z) :=
  fun x => get_coef (p x).

Definition merge {A:Type} (p1 p2: A -> @MPoly Z) :=
  fun x => add_mpoly (p1 x) (opp_mpoly (p2 x)).

Ltac mk_tuple l :=
  match l with
  | (?a :: ?h) =>
      let t := mk_tuple h in
      constr:((t,a))
  | (?a1 :: ?a2 :: @nil Z) => constr:((a2,a1))
  end.

Ltac destr_tuple l :=
      match goal with
      | x : (Z * ?A)%type |- _ =>
          let z := fresh "z" in
          destruct x as [z x];
          let l := constr:(z :: l) in
          destr_tuple l
      | x : (unit)%type |- _ =>
          let l := eval compute in (List.rev l) in
          let t := mk_tuple l in
          exists t
      end.

Ltac ensatz :=
  intros;
  repeat apply efactor;
  repeat equalities_to_goal;
  match goal with
    |- ?g =>
      let lb := hterm g in
      intros;
      match goal with
      | |- @ex _ (fun e1 : _ => @?P1 e1 = @?P2 e1) =>
          let xr := reify_term P2 in
          let xl := reify_term P1 in
          let x := eval cbv delta
                     [merge coef
                        get_coef
                        add_mpoly
                        mult_mpoly
                        add_monom_poly
                        equal
                        opp_mpoly]
                     beta iota in
          (coef (merge xr xl)) in
          match x with
          | (fun _: _ => ?x) =>
              let b := eval simpl in (List.last x 0%Z) in
              let b := constr: (Z.opp b) in
              let l := constr: (List.removelast x) in
              let n := eval simpl in (List.length l) in
              let l := constr: (List.rev_append lb l) in
              let lb := constr: (b :: l) in
              let lb := eval cbv delta [removelast rev_append] beta iota  in lb in
              match (list_reifyl0 lb) with
              |(?fv, ?le) =>
                 let lv := fresh "lv" in
                 set(lv := fv);
                 let lpol := eval compute in (get_lpol le) in
                 let SplitPolyList kont :=
                   match lpol with
                   | ?p2::?lp2 =>
                       let lp2 := eval compute in (List.rev lp2) in
                       kont p2 lp2 n
                   | ?g => idtac "polynomial not in the ideal"
                  end
            in
            SplitPolyList
              ltac:(fun p lp n =>
                      let p21 := fresh "p21" in
                      let lp21 := fresh "lp21" in
                      let n21 := fresh "n21" in
                      set (p21:=p) ;
                      set (lp21:=lp);
                      set (n21:= n);
                      nsatz_call
                        6%N 1%Z 0%Z p lp
                        ltac:(fun c r lq lci =>
                                let Hg := fresh "Hg" in
                                assert (Hg:check lp p (lci,lq) = true);
                                [vm_compute; reflexivity |
                                  match goal with
                                  | |- (exists e: ?A, ?x) =>
                                      let hd := eval compute in (firstn n lp21) in
                                        let hdt := eval compute in (set_true hd) in
                                          let tl := eval compute in (skipn n lp21) in
                                      let tlf:= eval compute in (set_false tl) in
                                        let pl := eval compute in (hdt ++ tlf) in
                                      assert (Hg2: mk_HCond0 PEZ (PEevalR lv) pl);
                                      [repeat (split;[assumption|idtac]); exact I|];
                                      generalize (@check_correct_exists _ _ _ _ _ _ _ _ _ _ _ lv  pl  p21 lci lq Hg Hg2)
                                  end;
                                  unfold mk_GCond0;
                                  let H := fresh "H" in
                                  intros H;
                                  let x := fresh "x" in
                                  let H1 := fresh "H" in
                                  destruct H as [x H1];
                                  simpl in x;
                                  match goal with
                                  | x : (Z * unit)%type |- _ =>
                                      let z := fresh "z" in
                                      destruct x as [z x];
                                      exists z
                                  | x : (Z * ?A)%type |- _ => destr_tuple constr:(@nil Z)
                                  end;
                                  cbv delta [PEevalR
                                               GCond0
                                               Ring_polynom.PEeval
                                               gen_phiZ
                                               gen_phiPOS
                                               BinList.nth
                                               jump hd
                                               tl
                                               nth
                                               lv
                                               p21
                                               fst
                                               snd] iota beta match in H1;
                                simpl;
                                apply Zminus_eq;
                                apply psos_r1 in H1;
                                rewrite <- H1;
                                cring
                                ]
                             )
                   )
               end
          end
      end
end.

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

Lemma modulo2 a b c:  (exists k:Z, (a - c)%Z = (k*b)%Z) -> a mod b = c mod b.
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

Ltac div_to_equality H x y := try (apply (div1 x y) in H).

Ltac divs_to_equalities :=
  lazymatch goal with
  |  H: (?x | ?y) |- _ => div_to_equality H x y
   end.

Ltac mod_to_equality H x y z:= try (apply (modulo1 x y z) in H).

Ltac mods_to_equalities :=
  lazymatch goal with
  |  H: (?z = ?x mod ?y) |- _ => apply symmetry in H
  |  H: (?x mod ?y = ?z) |- _ => mod_to_equality H x y z
  end.

Ltac exists_to_equalities :=
  lazymatch goal with
  | H: (exists e: ?A, ?b1) |- _ => destruct H
  end.

Example cancellation_congruence a n x y:
  (a * x = (a * y) mod n -> (exists e1 e2, a * e1 + n * e2 = 1) -> y mod n = x mod n)%Z.
Proof.
  intros;
  match goal with
  | |- ?x mod ?n = ?y mod ?n => apply modulo2
  | |- (?x | ?y) => apply div2
  | |- ?g => idtac
  end;
  repeat mods_to_equalities;
  repeat divs_to_equalities;
  repeat exists_to_equalities.
  ensatz.
Qed.

Example cancellation_congruence2 a n x y d u v m r:
  (a * y - a* x = n * d -> a * u + n * v = 1 ->
  exists e1, exists e2, exists e3, exists e4, y - x = e1 * n  + r * e2 + m * e3 + e4)%Z.
Proof.
  ensatz.
Qed.

Example cancellation_congruence3 a n x y d u v m r:
  (a * y - a* x = n * d -> a * u + n * v = 1 ->
  exists e1, exists e2, exists e3, y - x = e3 * n  + r * e2 + m * e1 )%Z.
Proof.
  ensatz.
Qed.

Example cancellation_congruence4 a n x y d u v m r t:
  (a * y - a* x = n * d -> a * u + n * v = 1 ->
  exists e3, exists e1, exists e4, exists e2, y - x = e3 * n  + e2 * r + e1 * m + e4 * t)%Z.
Proof.
ensatz.
Qed.
