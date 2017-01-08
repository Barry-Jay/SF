(* This Program is free software; you can redistribute it and/or      *)
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
(*                        SF-Calculus                                 *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                      Equal.v                                       *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import ArithRing.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import SF_Terms.
Require Import SF_Tactics.
Require Import Substitution_term.
Require Import SF_reduction.
Require Import SF_Normal.
Require Import SF_Closed.
Require Import SF_Eval.
Require Import Star.



(* General equality *) 

Definition is_atom M := 
  App (App (App (Op Fop) M) k_op) (App k_op (App k_op (App k_op i_op))).

Definition S_not_F M := App (App (App (App M (Op Fop)) k_op) k_op) i_op.

Lemma S_not_F_S : sf_red (S_not_F (Op Sop)) k_op. 
Proof. unfold i_op, k_op, S_not_F; repeat  eval_SF0; auto. Qed. 

Lemma S_not_F_F : sf_red (S_not_F (Op Fop)) (App k_op i_op). 
Proof. unfold i_op, k_op, S_not_F; repeat  eval_SF0; auto. Qed. 

Definition eq_op M N := iff (S_not_F M) (S_not_F N).

Definition equal_body :=  
(* Ref 2 is the recursion ref; 
   Ref 1 is the first argument, x
   Ref 0 is the second argument, y
*) 
  App
     (App (App (Op Fop) (Ref 1))
        (App (App (App (Op Fop) (Ref 0)) (eq_op (Ref 1) (Ref 0)))
           (App k_op (App k_op (App k_op i_op)))))
     (App
        (App s_op
           (App k_op
              (App (Op Sop)
                 (App (App (Op Fop) (Op Fop))
                    (App (App (Op Fop) (Ref 0))
                       (App (App (Op Fop) (Op Fop))
                          (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                             (App (Op Fop) (Op Fop)))))))))
        (App
           (App (Op Sop)
              (App (App (Op Sop) (App k_op (Op Sop)))
                 (App
                    (App (Op Sop)
                       (App (App f_op f_op)
                          (App (Op Sop)
                             (App (App (Op Fop) (Op Fop)) (Op Sop)))))
                    (App
                       (App (Op Sop)
                          (App (App f_op f_op)
                             (App (Op Sop)
                                (App (App (Op Fop) (Op Fop))
                                   (App (Op Sop)
                                      (App (App (Op Fop) (Op Fop)) (Op Sop)))))))
                       (App
                          (App (Op Sop)
                             (App (App (Op Sop) (App k_op (Op Sop)))
                                (App
                                   (App (Op Sop)
                                      (App (App f_op f_op)
                                         (App (Op Fop) (Op Fop))))
                                   (App
                                      (App (Op Sop)
                                         (App (App f_op f_op) (Op Sop)))
                                      (App
                                         (App (Op Sop)
                                            (App (App f_op f_op)
                                               (App 
                                                  (Op Sop)
                                                  (App
                                                  (App (Op Fop) (Op Fop))
                                                  (Op Sop)))))
                                         (App
                                            (App (Op Sop)
                                               (App 
                                                  (App f_op f_op)
                                                  (App 
                                                  (Op Sop)
                                                  (App
                                                  (App (Op Fop) (Op Fop))
                                                  (App (Op Fop) (Op Fop))))))
                                            (Ref 2)))))))
                          (App k_op
                             (App
                                (App (Op Sop)
                                   (App (App (Op Fop) (Op Fop))
                                      (App (Op Fop) (Op Fop)))) 
                                (Ref 2))))))))
           (App k_op
              (App (App (Op Fop) (Op Fop))
                 (App (App (Op Fop) (Op Fop))
                    (App (App (Op Fop) (Op Fop))
                       (App (App (Op Fop) (Op Fop))
                          (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                             (App (Op Fop) (Op Fop)))))))))).


  

Definition equal_fn := star (star (star equal_body)). 
Definition equal_comb :=  fix_comb equal_fn.

Lemma equal_fn_closed: maxvar equal_fn = 0.
Proof. unfold equal_fn; split_all.  Qed. 
Lemma equal_comb_closed : maxvar equal_comb = 0.
Proof. split_all; omega. Qed. 

Ltac unfold_equal M N := 
unfold equal_comb at 1; eval_SF0; 
unfold equal_fn at 1; unfold equal_body;  unfold iff; unfold not.

Ltac eq_out := 
match goal with 
| |- _ >= maxvar equal_comb => unfold equal_comb; eq_out
| |- _ >= maxvar (fix_comb equal_fn) => 
    rewrite equal_comb_closed; omega; eq_out 
| |- _ >= maxvar equal_fn => rewrite equal_fn_closed; omega; eq_out 
| _ => try omega; auto
end.

Ltac eval_SF := eval_SF0;  relocate_lt; unfold insert_Ref; split_all.

Lemma equal_comb_op : forall o, sf_red (App (App equal_comb (Op o)) (Op o)) k_op.
Proof. 
split_all. 
unfold equal_comb at 1.  
apply transitive_red with 
(App (App (App equal_fn (fix_comb equal_fn)) (Op o)) (Op o)). 
eapply2 preserves_app_sf_red. 
eapply2 fix_comb_fix.
unfold equal_fn at 1; unfold equal_body, iff, not.
eapply transitive_red.
eapply2 star_beta3.
unfold subst; unfold subst_rec; fold subst_rec.
unfold lift, lift_rec; fold lift_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec.
eval_SF0. eval_SF0.
case o; repeat eval_SF0.
Qed.


Lemma unequal_op_compound : 
forall M o, compound M -> 
              sf_red (App (App equal_comb (Op o)) M) (App k_op i_op). 
Proof. 
split_all.
apply transitive_red with 
(App (App (App equal_fn (fix_comb equal_fn)) (Op o)) M). 
eapply2 preserves_app_sf_red. 
unfold equal_comb. eapply2 fix_comb_fix. 
unfold equal_fn at 1; unfold equal_body.
eapply transitive_red.
eapply2 star_beta3.
unfold subst; unfold subst_rec; fold subst_rec.
unfold lift, lift_rec; fold lift_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec.
eval_SF0.
rewrite lift_rec_null_term.
rewrite subst_rec_lift_rec; try omega. rewrite subst_rec_lift_rec; try omega.
rewrite lift_rec_null_term.
(* 1 *) 
match goal with 
| |- multi_step sf_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 

apply succ_red with (App (App N (left_component M)) (right_component M))
end.
eapply2 f_compound_red.
eval_SF0.
Qed. 


Lemma unequal_op : 
forall M o, normal M -> maxvar M = 0 -> M <> (Op o) -> 
              sf_red (App (App equal_comb (Op o)) M) (App k_op i_op). 
Proof. 
split_all.
assert((exists o, M = (Op o)) \/ compound M) .
eapply2 programs_are_factorable. unfold program; split_all. 
inversion H2; split_all.
2: eapply2 unequal_op_compound. 
subst. 
apply transitive_red with 
(App (App (App equal_fn (fix_comb equal_fn)) (Op o)) (Op x)). 
eapply2 preserves_app_sf_red. 
eapply2 fix_comb_fix. 
unfold equal_fn at 1; unfold equal_body.
eapply transitive_red.
eapply2 star_beta3.
unfold subst; unfold subst_rec; fold subst_rec.
unfold lift, lift_rec; fold lift_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec.
eval_SF0. eval_SF0.
gen_case H1 o; gen_case H1 x; try discriminate; repeat eval_SF0.  
Qed. 



Lemma unequal_compound_op : 
forall M o, compound M -> 
              sf_red (App (App equal_comb M) (Op o))(App k_op i_op).
Proof. 
split_all.
apply transitive_red with 
(App (App (App equal_fn (fix_comb equal_fn)) M) (Op o)) .
eapply2 preserves_app_sf_red. 
eapply2 fix_comb_fix. 
unfold equal_fn at 1; unfold equal_body.
eapply transitive_red.
eapply2 star_beta3.
unfold subst; unfold subst_rec; fold subst_rec.
unfold lift, lift_rec; fold lift_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite lift_rec_null.
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. 
match goal with 
| |- multi_step sf_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 

apply succ_red with (App (App N (left_component M)) (right_component M))
end.
eapply2 f_compound_red.
simpl. repeat eval_SF0.
Qed. 

Lemma unequal_op2 : 
forall M o, normal M -> maxvar M = 0 -> M <> (Op o) -> 
              sf_red (App (App equal_comb M) (Op o))(App k_op i_op).
Proof. 
split_all.
assert((exists o, M = (Op o)) \/ compound M) .
eapply2 programs_are_factorable. 
unfold program; auto.
inversion H2. 
2: eapply2 unequal_compound_op. 
split_all. subst. 
eapply2 unequal_op.  
Qed. 


Lemma equal_compounds : 
forall M N, compound M -> compound N -> 
sf_red (App (App equal_comb M) N) 
        (App (App 
                (App (App equal_comb (left_component M)) 
                     (left_component N))
                (App (App equal_comb (right_component M)) 
                     (right_component N)))
             (App k_op i_op))
.
Proof. 
split_all.
apply transitive_red with 
(App (App (App equal_fn (fix_comb equal_fn)) M) N). 
eapply2 preserves_app_sf_red. unfold equal_comb. eapply2 fix_comb_fix. 
unfold equal_fn at 1; unfold equal_body.
eapply transitive_red.
eapply2 star_beta3.
unfold subst; unfold subst_rec; fold subst_rec.
unfold lift, lift_rec; fold lift_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
rewrite lift_rec_null.
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. 
match goal with 
| |- multi_step sf_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 

apply succ_red with (App (App N (left_component M)) (right_component M))
end.
eapply2 f_compound_red.
(* 1 *)
unfold_op; simpl. 
insert_Ref_out.  rewrite lift_rec_null_term.
repeat (rewrite subst_rec_lift_rec; try omega). 
repeat (rewrite lift_rec_null). 
eval_SF0. eval_SF0.
eapply transitive_red.
eapply preserves_app_sf_red. 
eval_SF0. eval_SF0. 
match goal with 
| |- multi_step sf_red1 (App (App (App (Op Fop) ?M) _) ?N) _ => 

apply succ_red with (App (App N (left_component M)) (right_component M)); split_all
end. 
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eval_SF0. eval_SF0. eval_SF0. eval_SF0.
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red;  auto. 
repeat eval_SF0. repeat eval_SF0.
Qed.


Theorem equal_programs : forall M, program M -> sf_red (App (App equal_comb M) M) k_op.
Proof. 
cut(forall p M, p >= rank M -> program M -> 
sf_red (App (App equal_comb M) M) k_op)
.
unfold program; split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *)
assert(factorable M) . eapply2 programs_are_factorable.  
inversion H1; split_all; subst. 
eapply2 equal_comb_op.
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component M))
          (App (App equal_comb (right_component M)) (right_component M))) 
     (App k_op i_op))
.
eapply2 equal_compounds. 

apply transitive_red with (App (App k_op k_op) (App k_op i_op)).
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
(* left *) 
eapply2 IHp.  
assert(rank (left_component M) < rank M) by eapply2 rank_compound_l. 
omega. 
unfold program in *; split_all.
inversion H2; subst; split_all; eapply2 nf_compound. inversion H3; auto; inversion H6; auto.
assert(maxvar (left_component M) <= maxvar M) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
(* right *) 
eapply2 IHp.  
assert(rank (right_component M) < rank M) .  eapply2 rank_compound_r. 
omega. 
unfold program in *; split_all. 
inversion H2; subst; split_all; inversion H3; auto; inversion H6; auto. 
assert(maxvar (right_component M) <= maxvar M) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
(* 1*)
repeat eval_SF0; auto. 
Qed. 



Theorem unequal_programs : forall M N, program M -> program N -> M<>N ->
                                       sf_red (App (App equal_comb M) N) (App k_op i_op).

Proof. 
cut(forall p  M N, p >= rank M -> program M -> program N -> M<>N ->  
sf_red (App (App equal_comb M) N) (App k_op i_op)
). 
split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *)
assert(factorable M) by eapply2 programs_are_factorable.  
assert(factorable N) by eapply2 programs_are_factorable.  
unfold program in *. 
inversion H3; inversion H4; split_all; subst.  
eapply2 unequal_op.
eapply2 unequal_op.
eapply2 unequal_op2.
(* both compounds *) 
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component N))
          (App (App equal_comb (right_component M)) (right_component N)))
     (App k_op i_op))
.
eapply2 equal_compounds. 

assert(left_component M = left_component N \/ left_component M <> left_component N) by eapply2 decidable_term_equality. 
assert(right_component M = right_component N \/ right_component M <> right_component N) by eapply2 decidable_term_equality. 
inversion H0.
inversion H10. 
(* 3 *) 
assert False. eapply2 H2. 
eapply2 components_monotonic; split_all. noway. 
(* 2 *) 
apply transitive_red with (App (App k_op (App k_op i_op)) (App k_op i_op)).
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
rewrite H11. eapply2 equal_programs.
split_all. 
inversion H6; subst; split_all; eapply2 nf_compound. inversion H7; auto; inversion H15; auto.
assert(maxvar (left_component N) <= maxvar N) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
eapply2 IHp.  
assert(rank (right_component M) < rank M) by eapply2 rank_compound_r. 
omega. 
split_all. 
inversion H5; subst; split_all; inversion H1; auto; inversion H15; auto.
assert(maxvar (right_component M) <= maxvar M) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
split_all. 
inversion H6; subst; split_all; inversion H7; auto; inversion H15; auto.
assert(maxvar (right_component N) <= maxvar N) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
repeat eval_SF0; auto. 
(* 1 *) 
apply transitive_red with (App (App (App k_op i_op) (App (App equal_comb (right_component M)) (right_component N))) (App k_op i_op)).
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 IHp.  
assert(rank (left_component M) < rank M) by eapply2 rank_compound_l. 
omega. 
split_all. 
inversion H5; subst; split_all; inversion H1; auto; inversion H15; auto.
assert(maxvar (left_component M) <= maxvar M) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
split_all. 
inversion H6; subst; split_all; inversion H7; auto; inversion H15; auto.
assert(maxvar (left_component N) <= maxvar N) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
unfold_op. 
eval_SF0.  eval_SF0. 
Qed. 


Lemma maxvar_equal_comb: maxvar equal_comb = 0. 
Proof. unfold equal_comb; split_all. Qed. 
