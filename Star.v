(**********************************************************************)
(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)
(**********************************************************************)

(**********************************************************************)
(*                        SF-Calculus                                 *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                       Star.v                                       *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import List.
Require Import Test.
Require Import General. 
Require Import Max. 
Require Import SF_Terms.
Require Import SF_Tactics.
Require Import Substitution_term.
Require Import SF_reduction.
Require Import SF_Normal.
Require Import SF_Closed.
Require Import SF_Eval.


Lemma map_lift0 : forall Ms, map (lift 0) Ms = Ms. 
Proof. induction Ms; split_all.   rewrite IHMs. unfold lift; rewrite lift_rec_null. auto. Qed.

Lemma append_nil: forall A (Ms: list A), Ms ++ nil = Ms. 
Proof. induction Ms; split_all. Qed.


Lemma max_choice: forall m n, max m n = m \/ max m n = n.
Proof.
induction m; split_all.   case n; split_all. 
assert(max m n0 = m \/ max m n0 = n0) by eapply2 IHm. 
inversion H; rewrite H0; auto. 
Qed.

Lemma maxvar_app : forall M N, maxvar (App M N) = max (maxvar M) (maxvar N).
Proof. split_all. Qed.


Lemma lift_preserves_maxvar2:
  forall M, forall k, maxvar (lift k M) - k = maxvar M.
Proof.
  induction M; split_all. relocate_lt. induction k; split_all.
  rewrite max_minus. unfold lift in *; rewrite IHM1; rewrite IHM2; auto.
Qed.
  
Fixpoint star M := 
match M with 
  | Ref 0 => App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))
| Ref (S n) => App  (App (Op Fop) (Op Fop))  (Ref n)
| Op o => App  (App (Op Fop) (Op Fop)) (Op o)
| App M1 M2 => App (App (Op Sop) (star M1)) (star M2)
end
.

Proposition star_beta: forall M N, sf_red (App (star M) N) (subst M N).
Proof.
induction M; split_all. 
(* 3 *) 
unfold subst; case n; split_all; unfold_op;  eapply2 succ_red.
insert_Ref_out. rewrite lift_rec_null_term. 
eapply succ_red. eapply2 s_red. one_step.
(* 2 *) 
unfold_op;  eapply2 succ_red. 
(* 1 *)
unfold subst; simpl. 
eapply succ_red. eapply2 s_red.
eapply2 preserves_app_sf_red. 
Qed.

Lemma star_beta2:
  forall M N1 N2, sf_red (App (App (star (star M)) N1) N2) (subst (subst M (lift 1 N2)) N1).
Proof.
induction M; split_all. 
(* 3 *) 
unfold subst; case n; split_all; unfold_op;  eapply2 succ_red.
insert_Ref_out. rewrite lift_rec_null_term. 
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term.
repeat eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0.
case n0; split_all; insert_Ref_out. rewrite lift_rec_null_term. 
repeat eval_SF0.
repeat eval_SF0.
(* 2 *)
unfold subst; simpl. repeat eval_SF0.
(* 1 *)
eval_SF0. eval_SF0. eval_SF0.
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 IHM1.
eapply2 IHM2.
eapply2 preserves_app_sf_red. 
Qed.

Lemma star_beta3:
  forall M N1 N2 N3, sf_red (App (App (App (star (star (star M))) N1) N2) N3)
                           (subst (subst (subst M (lift 2 N3)) (lift 1 N2)) N1).
Proof.
induction M; split_all. 
(* 3 *) 
unfold subst; case n; split_all; unfold_op;  eapply2 succ_red.
insert_Ref_out. rewrite lift_rec_null_term. 
repeat rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term.
repeat eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0.
case n0; split_all; insert_Ref_out. rewrite lift_rec_null_term. 
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null_term. repeat eval_SF0.
case n1; split_all. insert_Ref_out. rewrite lift_rec_null_term.
repeat eval_SF0.
 insert_Ref_out.  repeat eval_SF0.
 (* 2 *)
unfold subst; simpl. repeat eval_SF0.
(* 1 *)
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. 
eapply2 preserves_app_sf_red. 
Qed.

Lemma star_lift: forall M N k, sf_red (App (star (lift (S k) M)) N) (lift k M). 
Proof.
  induction M; split_all.
  (* 3 *)
  relocate_lt.
  replace (S k + n) with (S(k+n)) by omega.
  eval_SF0. unfold lift; simpl; relocate_lt;  auto. 
(* 2 *) 
  eval_SF0. 
  (* 1 *)
  eval_SF0. unfold lift in *;unfold_op. unfold lift_rec; fold lift_rec. 
  eapply2 preserves_app_sf_red. 
Qed.

Lemma lift_rec_preserves_star: 
forall M n k, lift_rec (star M) n k = star (lift_rec M (S n) k). 
Proof. induction M; split_all. case n; split_all. rewrite relocate_succ. auto. Qed. 

Lemma maxvar_star: forall M, maxvar (star M) = pred (maxvar M). 
Proof. 
induction M; split_all. 
case n; split_all. 
rewrite max_pred. auto.
Qed. 


Lemma star_normal: forall M, normal (star M). 
Proof. induction M; split_all. case n; split_all. Qed. 

Hint Resolve star_normal. 

(* fixpoints in normal form *) 

Definition app_comb M N := 
App (App s_op (App (App s_op (App k_op M)) (App k_op N))) i_op. 

Lemma app_comb_red : forall M N P, sf_red (App (app_comb M N) P) (App (App M N) P).
Proof.
unfold app_comb; unfold_op; split_all. 
eapply succ_red. eapply2 s_red. 
eapply succ_red. eapply app_sf_red. eapply2 s_red.  eapply2 s_red. 
eapply succ_red. eapply app_sf_red. eapply app_sf_red. eapply2 f_op_red.  eapply2 f_op_red.  
eapply2 f_op_red.  
auto. 
Qed. 


Lemma lift_rec_preserves_app_comb: 
forall M1 M2 n k, lift_rec (app_comb M1 M2) n k = app_comb (lift_rec M1 n k) (lift_rec M2 n k).
Proof. intros; unfold app_comb; unfold_op; split_all. Qed. 

Lemma subst_rec_preserves_app_comb: 
forall i M N k, subst_rec (app_comb i M) N k = app_comb (subst_rec i N k) (subst_rec M N k). 
Proof. intros; unfold app_comb; unfold_op; split_all.  Qed. 

Lemma app_comb_normal: forall i M, normal i -> normal M -> normal (app_comb i M). 
Proof. intros; unfold app_comb; unfold_op. repeat eapply2 nf_compound. Qed. 

Lemma maxvar_app_comb : forall M N,  maxvar (app_comb M N) = maxvar (App M N). 
Proof. intros; unfold app_comb. unfold_op; split_all. rewrite max_zero. auto. Qed.


Lemma rank_app_comb: forall M N, rank (app_comb M N) > rank (App M N).
Proof. intros; unfold app_comb; split_all. omega. Qed.

Definition omega := star(star (App (Ref 0) (app_comb (app_comb (Ref 1) (Ref 1)) (Ref 0)))).

Lemma program_app_comb2 : forall M N, program (app_comb M N) -> program M /\ program N.
Proof.
  unfold app_comb; unfold_op; intros. inversion H. simpl in H1. max_out. max_out.
  inversion H0; inversion H6; inversion H12; inversion H16; inversion H22; inversion H17; split_all. 
Qed.

Lemma omega_normal: normal omega.
Proof. unfold omega; auto. Qed.

Hint Resolve omega_normal. 

Definition fix_comb M := app_comb (app_comb omega omega) M. 

Lemma maxvar_fix_comb : forall M,  maxvar (fix_comb M) = maxvar M.
Proof. intros; unfold fix_comb. rewrite maxvar_app_comb. simpl. auto. Qed.

Lemma omega_omega : forall M, sf_red (App (App omega omega) M) (App M (fix_comb M)).
Proof.
unfold omega at 1. intros. 
eapply transitive_red. eapply2 star_beta2. 
unfold subst, subst_rec; fold subst_rec. 
insert_Ref_out. rewrite lift_rec_null.  rewrite subst_rec_lift_rec; try omega.  
rewrite lift_rec_null. eapply2 preserves_app_sf_red. 
repeat rewrite subst_rec_preserves_app_comb. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null.  
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. rewrite lift_rec_null.  
rewrite subst_rec_lift_rec; try omega.  rewrite lift_rec_null. auto. 
Qed. 

Lemma fix_comb_fix: forall M N, 
sf_red (App (fix_comb M) N) (App (App M (fix_comb M)) N).
Proof.
unfold fix_comb at 1. split_all. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. auto. 
eapply2 preserves_app_sf_red.
eapply2 omega_omega. 
Qed. 


Lemma lift_rec_preserves_fix_comb: 
forall M n k, lift_rec (fix_comb M) n k = fix_comb (lift_rec M n k).
Proof. unfold fix_comb; split_all. Qed.


Lemma subst_preserves_fix_comb: forall M N, subst (fix_comb M) N = fix_comb (subst M N). 
Proof. unfold fix_comb; split_all. Qed.


Lemma fix_comb_normal: forall M, normal M -> normal (fix_comb M). 
Proof. 
intros; unfold fix_comb; unfold_op.  
repeat eapply2 app_comb_normal; unfold omega; unfold_op; repeat eapply2 nf_compound. 
Qed. 


Definition vee_fn := star(star(star(star(app_comb (app_comb (Ref 3) (Ref 2))
                                                  (App (App s_op (Ref 1)) (Ref 0))))))
.

Definition vee := fix_comb vee_fn.

Lemma vee_normal: normal vee. 
Proof. intros; unfold vee; eapply2 fix_comb_normal. unfold vee_fn; unfold_op. 
       eapply2 star_normal.
Qed. 

Definition var i M := app_comb (app_comb vee i) M . 

Lemma var_normal: forall i M, normal i -> normal M -> normal (var i M). 
Proof. 
intros; unfold var; unfold_op. eapply app_comb_normal. eapply app_comb_normal. 
eapply vee_normal. auto. auto. 
Qed. 

Lemma maxvar_var : forall M N,  maxvar (var M N) = maxvar (App M N). 
Proof. intros; unfold var. repeat rewrite maxvar_app_comb. rewrite maxvar_app.
       repeat rewrite maxvar_app_comb. rewrite maxvar_app.
       replace (maxvar vee) with 0. split_all. unfold vee.
       rewrite maxvar_fix_comb. unfold vee_fn. repeat rewrite maxvar_star.
       rewrite maxvar_app_comb. simpl. auto.
Qed.

Lemma subst_rec_preserves_var:
  forall M1 M2 N k, subst_rec(var M1 M2) N k = var (subst_rec M1 N k) (subst_rec M2 N k).
Proof.
  intros. unfold var. repeat rewrite subst_rec_preserves_app_comb.
  rewrite subst_rec_closed. auto. unfold vee. rewrite maxvar_fix_comb.
  unfold vee_fn; split_all. omega. 
Qed.


Lemma rank_var: forall M N, rank (var M N) > rank (App M N).
Proof.
  intros; unfold var.
  assert(rank(app_comb (app_comb vee M) N) > rank(App (app_comb vee M) N)) by eapply2 rank_app_comb. 
  assert(rank (app_comb vee M) > rank (App vee M)) by eapply2 rank_app_comb.
  unfold rank in *; fold rank in *. omega.
Qed.


Lemma program_var2 : forall M N, program (var M N) -> program M /\ program N.
Proof.
  unfold var; unfold_op; intros.
  assert(program (app_comb vee M) /\ program N) by eapply2 program_app_comb2. inversion H0.
  assert(program M) by eapply2 program_app_comb2.   split; auto.
  Qed.

Proposition var_check : forall i M N, sf_red (App (var i M) N) (var  i (App (App s_op M) N)).
Proof.
 unfold var; split_all.  
 eapply transitive_red. eapply2 app_comb_red.
 eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto. 
unfold vee. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
 apply transitive_red with (App (App vee_fn (fix_comb vee_fn)) i).
eapply2 fix_comb_fix.
unfold vee_fn at 1; unfold_op.
eapply2 star_beta2. 
auto. auto.
unfold subst.
 rewrite fold_subst. rewrite fold_subst.
unfold subst. rewrite fold_subst. rewrite fold_subst.
replace (multi_step sf_red1) with sf_red by auto.
eapply transitive_red. eapply subst_preserves_sf_red. eapply subst_preserves_sf_red.
eapply2 star_beta2. auto. auto.
unfold subst, app_comb; unfold_op; split_all.
insert_Ref_out. repeat rewrite lift_rec_null.
repeat (rewrite subst_rec_lift_rec; try omega; auto). repeat rewrite lift_rec_null.
repeat (rewrite subst_rec_lift_rec; try omega; auto). repeat rewrite lift_rec_null.
repeat (rewrite subst_rec_lift_rec; try omega; auto). repeat rewrite lift_rec_null.
auto.
Qed.


Hint Resolve app_comb_normal fix_comb_normal star_normal. 

Lemma lift_rec_preserves_var: 
forall i M n k, lift_rec (var i M) n k = var (lift_rec i n k) (lift_rec M n k).
Proof. intros; unfold var; unfold_op; split_all. Qed. 

Lemma subst_preserves_var: forall i M N, subst (var i M) N = var (subst i N) (subst M N).
Proof.  unfold var; split_all. Qed. 




Definition fold_app_fn :=
  star(star(star (App (App (App (Op Fop) (Ref 0)) (Ref 1))
                      (star (star(App (App (App (Op Fop) (Ref 1)) (Op Sop))
                                      (App k_op (star(App (App (App (Ref 5) (Ref 4)) (Ref 0))
                                                          (Ref 1))))))))))
.

Definition fold_app := fix_comb fold_app_fn.

Lemma fold_app_nil: forall M o, sf_red (App (App fold_app M) (Op o)) M.
Proof.
  intros. eapply transitive_red. eapply preserves_app_sf_red.  
  unfold fold_app.
  eapply2 fix_comb_fix. auto. 
  unfold fold_app_fn at 1.
  eapply transitive_red. eapply preserves_app_sf_red.  
  eapply2 star_beta2. auto. 
  unfold subst. repeat  rewrite fold_subst. 
  eapply transitive_red. repeat (eapply subst_preserves_sf_red).
  eapply2 star_beta. auto. auto. 
  (* 1 *)
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
  rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null.
  eval_SF0.
Qed.


Lemma fold_app_snoc: forall M Ns N, sf_red (App (App fold_app M) (App (App (Op Sop) Ns) N))
                                           (App (App (App fold_app M) Ns) N).
Proof.
  intros. eapply transitive_red. eapply preserves_app_sf_red.  
  unfold fold_app.
  eapply2 fix_comb_fix. auto. 
  unfold fold_app_fn at 1.
  eapply transitive_red. eapply preserves_app_sf_red.  
  eapply2 star_beta2. auto. 
  unfold subst. repeat  rewrite fold_subst. 
  eapply transitive_red. repeat (eapply subst_preserves_sf_red).
  eapply2 star_beta. auto. auto. 
  (* 1 *)
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
  rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega.
  rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega.
  repeat rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega.
  rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega.
  rewrite lift_rec_null.
  eapply succ_red. eapply2 f_compound_red.
  repeat  rewrite fold_subst.
  unfold subst. repeat  rewrite fold_subst.
  eapply transitive_red. repeat eapply subst_preserves_sf_red.  
  eapply2 star_beta2. auto. auto. auto. 
  unfold_op; unfold left_component, right_component, subst, subst_rec; fold subst_rec. 
  insert_Ref_out. 
  unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
  unfold subst, subst_rec; fold subst_rec.
  rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega.
  rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega.
  repeat rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega.
  rewrite lift_rec_null.
  eapply succ_red. eapply2 f_compound_red. unfold left_component, right_component.
  eval_SF0. eval_SF0. eval_SF0. insert_Ref_out. repeat rewrite lift_rec_null.
   rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null.
   eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
   eapply preserves_app_sf_red.  eapply succ_red. eapply2 f_op_red. auto. 
   eapply succ_red. eapply2 f_op_red. auto. eval_SF0. 
   eapply succ_red. eapply2 f_op_red.
   rewrite subst_rec_lift_rec; try omega.  rewrite lift_rec_null.
   rewrite subst_rec_lift_rec; try omega.  rewrite lift_rec_null.
   rewrite subst_rec_lift_rec; try omega.  rewrite lift_rec_null.
   rewrite subst_rec_lift_rec; try omega.  rewrite lift_rec_null. auto. 
   eapply2 preserves_app_sf_red.   eapply2 preserves_app_sf_red. eval_SF0.
Qed.

Lemma maxvar_fold_app: maxvar fold_app = 0.
Proof. unfold fold_app; split_all. Qed. 


