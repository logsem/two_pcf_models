From stdpp Require Export base tactics.
From iris.prelude Require Export options prelude.
From iris.algebra Require Export ofe.
From iris.si_logic Require Import bi siprop.

Program Definition idfun {A : ofe} : A -n> A := λne x, x.
Program Definition NextO {A} : A -n> laterO A := λne x, Next x.

Program Definition sumO_rec {A B C : ofe} (f : A -n> C) (g : B -n> C) : sumO A B -n> C :=
  λne x, match x with
         | inl a => f a
         | inr b => g b
         end.
Next Obligation.
  intros. intros x y Hxy. simpl.
  destruct x as [a1|b1], y as [a2|b2]; try by inversion Hxy.
  - apply inl_ne_inj in Hxy. by f_equiv.
  - apply inr_ne_inj in Hxy. by f_equiv.
Qed.

#[export] Instance sumO_rec_ne n A B C : Proper (dist n ==> dist n ==> dist n) (@sumO_rec A B C).
Proof.
  intros f1 f2 Hf g1 g2 Hg. intros [x|y]; simpl; eauto.
Qed.

#[export] Instance sumO_rec_proper A B C : Proper ((≡) ==> (≡) ==> (≡)) (@sumO_rec A B C).
Proof.
  intros f1 f2 Hf g1 g2 Hg. intros [x|y]; simpl; eauto.
Qed.

Program Definition constO {A B : ofe} : A -n> B -n> A := λne x _, x.
Next Obligation. solve_proper. Qed.
Next Obligation. solve_proper. Qed.

#[export] Instance optionO_map_proper (A B : ofe) :
  Proper ((≡) ==> (≡)) (@optionO_map A B).
Proof. solve_proper. Qed.

Program Definition flipO {A B C : ofe} : (A -n> B -n> C) -n> B -n> A -n> C
  := λne f x y, f y x.
Next Obligation. solve_proper. Qed.
Next Obligation. solve_proper. Qed.
Next Obligation. solve_proper. Qed.

Program Definition later_ap {A B} (f : later (A -n> B)) : laterO A -n> laterO B :=
  λne x, Next $ (later_car f) (later_car x).
#[export] Instance later_ap_ne {A B} : NonExpansive (@later_ap A B).
Proof.
  intros n f g Hfg. intros x. simpl.
  eapply Next_contractive. destruct n; eauto using dist_later_0, dist_later_S.
  apply dist_later_S. f_equiv. eapply later_car_anti_contractive; eauto.
Qed.

Definition laterO_ap {A B} := OfeMor (@later_ap A B).

Lemma laterO_map_compose {A B C} (f : A -n> B) (g : B -n> C) x :
  laterO_map (g ◎ f) x ≡ laterO_map g (laterO_map f x).
Proof. by destruct x. Qed.
Lemma laterO_map_id {A} (x : laterO A) : laterO_map idfun x ≡ x.
Proof. by destruct x. Qed.
Lemma laterO_map_Next {A B} (f : A -n> B) (x : A) : laterO_map f (Next x) ≡ Next (f x).
Proof. reflexivity. Qed.

Program Definition inlO {A B : ofe} : A -n> sumO A B := λne x, inl x.
Program Definition inrO {A B : ofe} : B -n> sumO A B := λne x, inr x.
Program Definition fstO {A B : ofe} : prodO A B -n> A := λne x, fst x.
Program Definition sndO {A B : ofe} : prodO A B -n> B := λne x, snd x.
Program Definition prod_in {A B C : ofe} : (C -n> A) -n> (C -n> B) -n> C -n> prodO A B
    := λne f g x, (f x, g x).
Solve Obligations with solve_proper.

Definition mmuu `{!Cofe A, !Inhabited A} (f : laterO A -n> A) : A.
Proof.
  refine (fixpoint (f ◎ NextO)).
  solve_contractive.
Defined.

Lemma mmuu_unfold {A} `{!Cofe A, Inhabited A} (f : laterO A -n> A) :
  mmuu f ≡ f (Next $ mmuu f).
Proof.
  rewrite /mmuu.
  etrans.
  { eapply (fixpoint_unfold (A:=A)). }
  simpl. f_equiv.
Qed.

Global Instance mmuu_ne {A} `{!Cofe A, Inhabited A} :
  NonExpansive (@mmuu A _ _).
Proof.
  repeat intro. unfold mmuu.
  apply fixpoint_ne. intros z.
  solve_proper.
Qed.

Section siProp.
Import siprop.
Import siProp_primitive.
Ltac unseal := (* Coq unfold is used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_pure, bi_entails, bi_later,
    bi_and, bi_or, bi_impl, bi_forall, bi_exist,
    bi_sep, bi_wand, bi_persistently, bi_later; simpl;
  unfold internal_eq, bi_internal_eq_internal_eq,
    plainly, bi_plainly_plainly; simpl;
  siProp_primitive.unseal.
Lemma internal_eq_pointwise {A B : ofe} (f g : A -n> B) :
  ⊢@{bi.siPropI} (∀ x, f x ≡ g x) → f ≡ g.
Proof.
  unseal. split. intros n _ m Hnm H x. apply H.
Qed.
Lemma laterN_soundness (P : siProp) (n : nat) : (⊢ ▷^n P) → ⊢ P.
Proof.
  induction n; simpl; eauto.
  intros H%siProp.later_soundness. by eapply IHn.
Qed.
End siProp.

