Inductive form :=
  Tr
| Fa
| And  (_ _ :form)
| Or   (_ _:form)
| Impl (_ _:form)
| All  {A:Type} (_:A-> form)
| Ex   {A:Type} (_:A-> form)
| Atom (_:Prop).


(** Some definitions about the context **)

Definition Included (Gamma Delta:form -> Prop ) : Prop :=
  forall x:form , Gamma x -> Delta x.

Inductive Singleton (x:form) : form -> Prop :=
  In_singleton : (Singleton x) x.

Inductive Union (B C:form -> Prop) : form -> Prop :=
| Union_introl : forall x:form, B x -> (Union B C) x
| Union_intror : forall x:form, C x -> (Union B C) x.

Definition Add (G:form -> Prop) (x:form) : form -> Prop :=
  Union G (Singleton x).

Hint Unfold Included Add: ctx.

Hint Resolve Union_introl Union_intror In_singleton: ctx.

(** Some Properties on Contextes **)

Lemma union_assoc_lr (A B C: form -> Prop) :
  forall x :form, Union (Union A C) B x -> Union A (Union C B) x.
Proof.
  intros.
  induction H.
  inversion H.
  apply Union_introl.
  firstorder.
  apply Union_intror.
  apply Union_introl.
  auto.
  apply Union_intror.
  apply Union_intror.
  auto.
Qed.

Lemma union_assoc_rl (A B C: form -> Prop) :
  forall x :form, Union A (Union C B) x -> Union (Union A C) B x .
Proof.
  intros.
  induction H.
  apply Union_introl.
  firstorder.
  inversion H.
  firstorder.
  apply Union_intror.
  auto.
Qed.
Lemma union_assoc (A B C: form -> Prop) :
  forall x :form, Union (Union A C) B x <-> Union A (Union C B) x.
Proof.
  split.
  apply union_assoc_lr.
  apply union_assoc_rl.
Qed.
Lemma union_comm (A B: form -> Prop) :
  forall x :form, Union A B x <-> Union B A x.
Proof.
  split.
  intros. induction H.
  apply Union_intror. assumption.
  apply Union_introl. assumption.
  intros. induction H.
  apply Union_intror. assumption.
  apply Union_introl. assumption.
Qed.
Lemma union_assoc_swith_A_C (A B C: form -> Prop) :
  forall x :form, Union (Union A C) B x -> Union C (Union A B) x.
Proof.
  *intros.  
   induction H. inversion H.
  +apply Union_intror. apply Union_introl. assumption.
  + apply Union_introl. assumption.
  +apply Union_intror. apply Union_intror. assumption.
Qed.
Lemma union_assoc_swith_C_A (A B C: form -> Prop) :
  forall x :form, Union C (Union A B) x -> Union (Union A C) B x.
Proof.
  intros. induction H. 
  +apply Union_introl. apply Union_intror. assumption.
  +inversion H. apply Union_introl. apply Union_introl. assumption.
   apply Union_intror. assumption.
Qed.

(** Question 1.1 **)
Inductive deriv  (Gamma:form-> Prop) : form -> Prop :=
| ATr : deriv Gamma Tr
| Ax :
    forall (F:form),
      (Gamma F) -> deriv Gamma F
(***

      --------------------
          Γ , A  |- A  

 ***)                     
| IImpl :

    (***
           Γ , A |- B 
      --------------------
            Γ |- A -> B 
     **)
    forall A B: form,
      Included Gamma (Add Gamma A) -> 
      deriv (Add Gamma A) B ->
      deriv Gamma (Impl A B)
   
| EImpl :
    
    (***
        Γ  |- A    Γ  |- A -> B 
      --------------------------
              Γ |- B 
     ***)
    forall A B:form,
      deriv Gamma A ->
      deriv Gamma (Impl A B) ->
      deriv Gamma B
| IAnd :

    (***
        Γ  |- A    Γ  |- B 
      --------------------
           Γ |- A /\ B 
     ***)
    forall A B:form,
      deriv Gamma A -> deriv Gamma B ->
      deriv Gamma (And A B)
| EAnd_1 :
    
    (***
        Γ  |- A /\ B 
      --------------------
         Γ |- A 
     ***)
    forall A B:form,
      deriv Gamma (And A B) -> 
      deriv Gamma A
| EAnd_2 :
    
    (***
        Γ  |- A /\ B 
      --------------------
         Γ |- B 
     ***)
    forall A B:form,
      deriv Gamma (And A B) -> 
      deriv Gamma B
| IOr_1 :
    (***
           Γ  |- A 
      --------------------
         Γ |- A \/ B 
     ***)
    forall A B:form,
      deriv Gamma A -> 
      deriv Gamma (Or A B)
| IOr_2 :
    (***
           Γ  |- B 
      --------------------
         Γ |- A \/ B 
     ***)
    
    forall A B:form,
      deriv Gamma B -> 
      deriv Gamma (Or A B)
| EOr :    
    (***
       Γ |- A \/ B   Γ , A |- C  Γ , B |- C 
      ---------------------------------------
                    Γ |- C
     ***)
    
    forall A B C:form,
      
      deriv Gamma (Or A B) ->
      Included Gamma (Add Gamma A) ->
      deriv (Add Gamma A) C ->
      Included Gamma (Add Gamma B) ->
      deriv (Add Gamma B) C -> 
      deriv Gamma C 
            
| INot : 
    (***
          Γ , A |- Fa 
     -----------------------
            Γ |- ¬A 

     ***)
    
    forall A:form,
      Included Gamma (Add Gamma A) ->
      deriv (Add Gamma A) Fa ->
      deriv Gamma (Impl A Fa)
            
| ENot_1 :            
    (***
       Γ |- A    Γ |- ¬ A 
      --------------------
            Γ |- Fa 
     ***)
    
    forall A:form,
      deriv Gamma A ->
      deriv Gamma (Impl A Fa) ->
      deriv Gamma Fa

            
| ENot_2 :          
    (* 
        exfalso
       Γ |- Fa
     ------------- 
        Γ |- A      
     *)
    forall (A:form),
      deriv Gamma Fa ->
      deriv Gamma A
            
            
| IAll :
    (***
       Γ |- P(x) (x not in FV(Γ))
     -------------------------
       Γ |- ∀ P(x)
     ***)
    forall (X:Type) (P:X -> form),
      (forall x, deriv Gamma (P x)) ->
      deriv Gamma (All P)
            
| EAll :
    (***
       Γ |-    ∀ P(x) 
     -------------------------
       Γ |-  P(x) { x \ t } 
     ***)

    forall X:Type, forall a:X, forall P:X -> form,
          deriv Gamma (All P) ->
          deriv Gamma (P a)
| IEx :
    (***
       Γ |-   P(x) { x \ t } 
     -------------------------
       Γ |-  ∃x P(x) 
     ***)
    
    forall (X:Type) (a:X) (P:X -> form),
      deriv Gamma (P a) ->
      deriv Gamma (Ex P)
| EEx :
    (***
       Γ |- ∃x P(x)   Γ , P |- B 
     ----------------------------
              Γ |-  B
     ***)  
    forall  (B:form),
    forall  (X:Type) (P:X -> form),    
      (forall x, Included Gamma (Add Gamma (P x)) ->
            deriv (Add Gamma (P x)) B) ->
      deriv Gamma (Ex P) ->    
      deriv Gamma B.

   
Hint Resolve  Ax IImpl EImpl IAnd EAnd_1 EAnd_2 IOr_1 IOr_2 EOr INot ENot_1
     ENot_2 IAll EAll IEx EEx : derv.


(** Somme Properties about First order Logics **)

Lemma de_morgan'_1 :
  forall (G:form -> Prop) (A B:form), 
    deriv (Add G (Impl (Or A B) Fa) )  (And (Impl A Fa) (Impl B Fa)).
Proof.
  intros.
  apply (IAnd ).
  apply INot;auto with ctx.
  apply (ENot_1 (Add (Add G (Impl (Or A B) Fa)) A) (Or A B)).
  apply (IOr_1). apply Ax. auto with ctx.
  apply Ax.
  auto with ctx.

  apply INot;auto with ctx.
  apply (ENot_1 (Add (Add G (Impl (Or A B) Fa)) B) (Or A B)).
  apply (IOr_2). apply Ax. auto with ctx.
  apply Ax.  auto with ctx.
Qed.

Lemma de_morg_1 :
  forall (L : form -> Prop) (A1 A2:form),
    deriv L (Impl (Or A1 A2) Fa) ->
    deriv L (And (Impl A1 Fa) (Impl A2 Fa)).
Proof.
  intros.
  apply (EImpl L (Impl (Or A1 A2) Fa)
               (And (Impl A1 Fa) (Impl A2 Fa))).
  auto .
  apply IImpl. auto with ctx.
  apply (de_morgan'_1 L A1 A2 ).
Qed.

Hint Resolve de_morg_1 de_morgan'_1:derv.

Lemma de_morgan'_and_l :
  forall (G:form -> Prop) (A B:form), 
    deriv (Add G (Impl (Impl (And A B) Fa) Fa) )
          (And (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa)).
Proof.
  intros.
  apply IAnd.
  (* coté gauche not not A  *)
  apply INot;auto with ctx.
  apply (ENot_1 (Add (Add G (Impl (Impl (And A B) Fa) Fa)) (Impl A Fa))
                (Impl (And A B) Fa) ).
  apply INot;auto with ctx.
  apply (ENot_1
           (Add (Add (Add G (Impl (Impl (And A B) Fa) Fa)) (Impl A Fa)) (And A B))
           A).
  apply (EAnd_1
           (Add (Add (Add G (Impl (Impl (And A B) Fa) Fa)) (Impl A Fa)) (And A B))
           A B).
  apply Ax. auto with ctx. 
  apply Ax; auto with derv ctx. 
  apply Ax; auto with derv ctx. 

  (* coté droit not not B  *)
  apply INot;auto with ctx.
  apply (ENot_1 (Add (Add G (Impl (Impl (And A B) Fa) Fa)) (Impl B Fa))
                (Impl (And A B) Fa)).
  apply INot;auto with ctx.
  apply (ENot_1
           (Add (Add (Add G (Impl (Impl (And A B) Fa) Fa)) (Impl B Fa)) (And A B))
           B).
  apply (EAnd_2
           (Add (Add (Add G (Impl (Impl (And A B) Fa) Fa)) (Impl B Fa)) (And A B))
           A B).
  apply Ax. auto with ctx. 
  apply Ax; auto with derv ctx. 
  apply Ax; auto with derv ctx. 
Qed.


(* not not A /\ B => not not A /\ not not B*)

Lemma de_morgan_and_l :
  forall (G:form -> Prop) (A B:form), 
    deriv G           
          (Impl (Impl (Impl (And A B) Fa) Fa) 
                (And (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa))).
Proof.
  intros.
  apply IImpl. auto with ctx.
  apply de_morgan'_and_l.
Qed.

Hint Resolve de_morgan'_and_l de_morgan_and_l:derv.

Lemma de_morg_and :
  forall (L : form -> Prop) (A1 A2:form),
    deriv L (Impl (Impl (And A1 A2) Fa) Fa) ->
    deriv L (And (Impl (Impl A1 Fa) Fa) (Impl (Impl A2 Fa) Fa)).
Proof.
  intros.
  apply (EImpl L (Impl (Impl (And A1 A2) Fa) Fa)
               (And (Impl (Impl A1 Fa) Fa) (Impl (Impl A2 Fa) Fa))).
  auto .
  apply IImpl. auto with ctx.
  apply (de_morgan'_and_l L A1 A2 ).
Qed.
Hint Resolve de_morg_and :derv.

Lemma quad_to_double' :
  forall (L :form -> Prop) (A1 A2:form),
    deriv (Add L (Impl (Impl (Impl (Impl (Or  A1  A2) Fa) Fa) Fa) Fa))
          (Impl (Impl (Or A1 A2) Fa) Fa).
Proof.
  intros.
  apply (INot); auto with ctx derv. 
  apply (ENot_1
           (Add
              (Add L
                   (Impl (Impl (Impl
                                  (Impl (Or  A1  A2) Fa) Fa) Fa) Fa))
              (Impl (Or  A1  A2) Fa))
           (Impl (Impl (Impl (Or A1  A2) Fa) Fa) Fa)
        ).
  apply (INot); auto with ctx derv. 
  apply (ENot_1
           (Add
              (Add
                 (Add L (Impl
                           (Impl
                              (Impl
                                 (Impl (Or A1  A2) Fa) Fa) Fa) Fa))
                 (Impl (Or A1 A2) Fa))
              (Impl (Impl (Or  A1  A2) Fa) Fa))
           (Impl (Or A1 A2) Fa) ).
  apply Ax;auto with ctx derv.
  apply Ax;auto with ctx derv.
  apply Ax;auto with ctx derv. 
Qed.

Lemma quad_to_double :
  forall (L :form -> Prop) (A1 A2:form),
    deriv L (Impl (Impl (Impl (Impl (Or  A1 A2) Fa) Fa) Fa) Fa) ->
    deriv L (Impl (Impl (Or A1 A2) Fa) Fa).
Proof.
  intros.
  apply (EImpl L
               (Impl (Impl (Impl (Impl (Or  A1  A2) Fa) Fa) Fa) Fa)
               (Impl (Impl (Or A1 A2) Fa) Fa)
        ).
  auto .
  apply IImpl. auto with ctx.
  apply (quad_to_double' L A1 A2 ).
Qed.
Hint Resolve quad_to_double quad_to_double':derv.

Lemma dist_neg_impl' :
  forall (L:form -> Prop) (A1 A2 : form),
    deriv (Add L (Impl (Impl (Impl A1 A2) Fa) Fa))
          (Impl (Impl (Impl A1 Fa) Fa)  (Impl (Impl A2 Fa) Fa)).
Proof.
  intros.
  apply IImpl;auto with ctx.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add
              (Add
                 (Add L
                      (Impl (Impl (Impl A1 A2) Fa) Fa))
                 (Impl (Impl A1 Fa) Fa)) (Impl A2 Fa)
           )
           (Impl A1 Fa)
        );auto with ctx.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add
              (Add
                 (Add
                    (Add L
                         (Impl (Impl (Impl A1 A2) Fa) Fa)) (Impl (Impl A1 Fa) Fa))
                 (Impl A2 Fa)) A1)
           (Impl (Impl A1 A2) Fa)
        ).
  apply IImpl;auto with ctx.
  apply (EImpl
           (Add
              (Add
                 (Add
                    (Add (Add L (Impl (Impl (Impl A1 A2) Fa) Fa))
                         (Impl (Impl A1 Fa) Fa)) (Impl A2 Fa)) A1) 
              (Impl A1 A2))
           A2
        ).
  apply (EImpl
           (Add
              (Add
                 (Add
                    (Add (Add L (Impl (Impl (Impl A1 A2) Fa) Fa))
                         (Impl (Impl A1 Fa) Fa)) (Impl A2 Fa)) A1) 
              (Impl A1 A2))
           A1
        ).
  apply Ax; auto with ctx.
  apply Ax; auto with ctx. 
  apply Ax;auto with ctx.
  apply Ax;auto with ctx.
  (** On pouss dans le contexte pour récupérer not (not (A1 => A2)) *)
  red. apply Union_introl. auto with ctx.
  apply Ax;auto with ctx.
Qed.

Lemma dist_neg_impl:
  forall (L :form -> Prop) (A1 A2:form),
    deriv L (Impl (Impl (Impl A1 A2) Fa) Fa) -> 
    deriv L (Impl (Impl (Impl A1 Fa) Fa)  (Impl (Impl A2 Fa) Fa)).
Proof.
  intros.
  apply (EImpl L
               (Impl (Impl (Impl A1 A2) Fa) Fa)
               (Impl (Impl (Impl A1 Fa) Fa) (Impl (Impl A2 Fa) Fa))
        ).
  auto .
  apply IImpl. auto with ctx.
  apply (dist_neg_impl' L A1 A2 ).
Qed.
Hint Resolve dist_neg_impl' dist_neg_impl :derv.


Lemma intro_of_db_neg' :
  forall (L:form -> Prop) (A:form),
    deriv (Add L A) (Impl (Impl A Fa) Fa).
Proof.
  intros.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add (Add L A) (Impl A Fa))
           A
        ).
  apply Ax;auto with ctx.
  apply Ax;auto with ctx.
Qed.

Lemma intro_of_db_neg :
  forall (L :form -> Prop) (A :form),
    deriv L A  -> 
    deriv L (Impl (Impl A Fa) Fa).
Proof.
  intros.
  apply (EImpl L
               A
               (Impl (Impl A Fa) Fa)
        ).
  auto.
  apply IImpl;auto with ctx.
  apply intro_of_db_neg'.
Qed.

Hint Resolve  intro_of_db_neg  intro_of_db_neg' :derv.

(* Methode pour supprimer une hypothèse dans le contexte
  apply (deriv_Weakening
           G
           (Add G <Some formule in the context> ).
  <some tactics to prove the goal > 
  Focus 2.
  auto with ctx derv. 
 *)
Lemma distr_neg_all_ex' :
  forall (G:form -> Prop) (X:Type) (P:X -> form) ,
    deriv (Add G (All(fun x => Impl (Impl (P x) Fa) Fa)  ))
          (Impl (Ex(fun x => Impl (P x) Fa )) Fa).
Proof.
  intros.
  apply INot; auto with ctx derv.
  apply (EEx
           (** Context **)
           (Add (Add G (All (fun x : X => Impl (Impl (P x) Fa) Fa)))
                (Ex (fun x : X => Impl (P x) Fa)))
           (** B **) 
           Fa
           (** X **)
           X
           (** On done P la fonction  **)
           (fun x : X => Impl (P x) Fa)
        ).
  intros.
  apply (ENot_1
           (Add
              (Add (Add G (All (fun x0 : X => Impl (Impl (P x0) Fa) Fa)))
                   (Ex (fun x0 : X => Impl (P x0) Fa))) (Impl (P x) Fa))
           (Impl (P x) Fa)
        ).
  apply Ax; auto with ctx derv.

  apply (EAll
           (Add
              (Add (Add G (All (fun x0 : X => Impl (Impl (P x0) Fa) Fa)))
                   (Ex (fun x0 : X => Impl (P x0) Fa))) (Impl (P x) Fa))
           X
           x
           (fun x0 : X => Impl (Impl (P x0) Fa) Fa) ).
  apply Ax;auto with ctx.
  apply Ax;auto with ctx.
Qed.
Lemma distr_neg_all_ex :
  forall (G:form -> Prop) (X:Type) (P:X -> form) ,
    deriv G (All(fun x => Impl (Impl (P x) Fa) Fa)  ) -> 
    deriv G (Impl (Ex(fun x => Impl (P x) Fa )) Fa).
Proof.
  intros.
  apply (EImpl G
               (All (fun x : X => Impl (Impl (P x) Fa) Fa))
               (Impl (Ex (fun x : X => Impl (P x) Fa)) Fa)
        ).
  auto with ctx.
  apply IImpl;auto with ctx.
  apply distr_neg_all_ex'.
Qed.

Hint Resolve distr_neg_all_ex distr_neg_all_ex'.

Lemma demorgan_ex_to_all' :
  forall (G:form -> Prop) (X:Type) (P:X -> form),
    deriv (Add G (Ex(fun x => Impl (P x) Fa)))
          (Impl (All( fun x => P x)) Fa).
Proof.
  intros.
  apply INot;auto with ctx.
  apply (EEx
           (** ctx **)
           (Add (Add G (Ex (fun x : X => Impl (P x) Fa))) (All (fun x : X => P x)))
           (**B **)
           Fa
           X
           (fun x => Impl (P x) Fa )
        ).
  intros.
  apply (ENot_1
           (Add
              (Add (Add G (Ex (fun x0 : X => Impl (P x0) Fa)))
                   (All (fun x0 : X => P x0))) (Impl (P x) Fa))
           (P x) 
        ).
  apply (EAll
           (Add
              (Add (Add G (Ex (fun x0 : X => Impl (P x0) Fa)))
                   (All (fun x0 : X => P x0))) (Impl (P x) Fa))
           (** X le type **)
           X
           (** x l'element substitue **)
           x
           (** le prédicat **)
           (fun x => P x)
        ).
  (** assuption **)
  apply Ax;auto with ctx.
  (** assuption **)
  apply Ax;auto with ctx.
  (** assuption **)
  apply Ax;auto with ctx.
Qed.

Ltac assumate := apply Ax;auto with ctx.
Lemma demorgan_ex_to_all :
  forall (G:form -> Prop) (X:Type) (P:X -> form),
    deriv G (Ex(fun x => Impl (P x) Fa)) -> 
    deriv G (Impl (All( fun x => P x)) Fa).
Proof.
  intros.
  apply (EImpl
           G
           (Ex (fun x : X => Impl (P x) Fa))
           (Impl (All (fun x : X => P x)) Fa)
        ).
  (** Assuption **)
  auto.
  apply IImpl. auto with ctx.
  apply demorgan_ex_to_all';auto with ctx.
Qed.  

Hint Resolve demorgan_ex_to_all' demorgan_ex_to_all:derv.


Lemma demorgan_all_to_ex_db_neg' :
  forall (G:form -> Prop) (X:Type) (P:X -> form),
    deriv (Add G (Impl (Impl (All (fun x => P x)) Fa ) Fa ) )
          (Impl ( Ex (fun x => Impl (P x) Fa ) ) Fa ).
Proof.
  intros.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add (Add G (Impl (Impl (All (fun x : X => P x)) Fa) Fa))
                (Ex (fun x : X => Impl (P x) Fa)))
           (Impl (All (fun x : X => P x)) Fa)
        ).
  apply demorgan_ex_to_all'.
  assumate.
Qed.

Lemma demorgan_all_to_ex_db_neg :
  forall (G:form -> Prop) (X:Type) (P:X -> form),
    deriv G (Impl (Impl (All (fun x => P x)) Fa ) Fa ) -> 
    deriv G (Impl ( Ex (fun x => Impl (P x) Fa ) ) Fa ).
Proof.
  intros.
  apply (EImpl
           G
           (Impl (Impl (All (fun x : X => P x)) Fa) Fa)
           (Impl (Ex (fun x : X => Impl (P x) Fa)) Fa));auto.
  apply IImpl;auto with ctx.
  apply demorgan_all_to_ex_db_neg'.
Qed.

Hint Resolve demorgan_all_to_ex_db_neg demorgan_all_to_ex_db_neg':derv.

Lemma distr_neg_ex_all' :
  forall (G:form -> Prop) (X:Type) (P:X -> form) ,
    deriv (Add G (Impl (Ex(fun x => Impl (P x) Fa )) Fa))
          (All(fun x => Impl (Impl (P x) Fa) Fa)  ).  
Proof.
  intros.
  apply IAll. intros.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add
              (Add G
                   (Impl (Ex (fun x0 : X => Impl (P x0) Fa)) Fa)) (Impl (P x) Fa))
           (Ex(fun x => Impl (P x) Fa ))
        ).
  apply (IEx
           (Add (Add G (Impl (Ex (fun x0 : X => Impl (P x0) Fa)) Fa)) (Impl (P x) Fa))
           X
           x
           (fun x0 : X => Impl (P x0) Fa)
        ).
  (** assmption **)
  assumate.
  (** assumption **)
  assumate.
Qed.



Lemma distr_neg_ex_all :
  forall (G:form -> Prop) (X:Type) (P:X -> form) ,
    deriv G (Impl (Ex(fun x => Impl (P x) Fa )) Fa) -> 
    deriv G (All(fun x => Impl (Impl (P x) Fa) Fa)).
Proof.
  intros.
  apply (EImpl
           G
           (Impl (Ex (fun x : X => Impl (P x) Fa)) Fa)
           (All (fun x : X => Impl (Impl (P x) Fa) Fa))
        ).
  auto.
  apply IImpl;auto with ctx.
  apply distr_neg_ex_all'.
Qed.

Hint Resolve distr_neg_ex_all' distr_neg_ex_all:derv.

Lemma distr_4_neg_ex' :
  forall (G:form -> Prop) (X:Type) (P:X -> form) ,
    deriv (Add G
               (Impl (Impl (Impl (Impl (Ex(fun x => P x )) Fa) Fa) Fa) Fa)
          )
          (Impl (Impl (Ex(fun x =>  P x)) Fa) Fa).  
Proof.
  intros.
  apply INot;auto with ctx.
  apply (ENot_1 
           (Add (Add G
                     (Impl
                        (Impl
                           (Impl
                              (Impl (Ex (fun x : X => P x)) Fa) Fa) Fa) Fa))
                (Impl (Ex (fun x : X => P x)) Fa))
           (Impl
              (Impl
                 (Impl (Ex (fun x : X => P x)) Fa) Fa) Fa)
        ).
  apply INot;auto with ctx.
  apply (ENot_1
           (Add
              (Add
                 (Add G
                      (Impl
                         (Impl
                            (Impl
                               (Impl (Ex (fun x : X => P x)) Fa) Fa) Fa) Fa))
                 (Impl (Ex (fun x : X => P x)) Fa))
              (Impl (Impl (Ex (fun x : X => P x)) Fa) Fa))
           (Impl (Ex (fun x : X => P x)) Fa)
        ).
  assumate.
  assumate.
  assumate.
Qed.
Lemma distr_4_neg_ex :
  forall (G:form -> Prop) (X:Type) (P:X -> form) ,
    deriv G (Impl (Impl (Impl (Impl (Ex(fun x => P x )) Fa) Fa) Fa) Fa) -> 
    deriv G (Impl (Impl (Ex(fun x =>  P x)) Fa) Fa).
Proof.
  intros.
  apply (EImpl
           G
           (Impl (Impl (Impl (Impl (Ex (fun x : X => P x)) Fa) Fa) Fa) Fa)
           (Impl (Impl (Ex (fun x : X => P x)) Fa) Fa)
        ).
  auto.
  apply IImpl;auto with ctx.
  apply distr_4_neg_ex'.
Qed.

Hint Resolve distr_4_neg_ex distr_4_neg_ex':derv.

Lemma distr_4_neg_atm' :
  forall (G:form -> Prop) (P :Prop),
    deriv (Add G (Impl (Impl (Impl (Impl (Atom P) Fa) Fa) Fa) Fa))
          (Impl (Impl (Atom P) Fa) Fa).
Proof.
  intros.
  apply INot;auto with ctx.
  apply (ENot_1 
           (Add (Add G (Impl (Impl (Impl (Impl (Atom P) Fa) Fa) Fa) Fa))
                (Impl (Atom P) Fa))
           (Impl (Impl (Impl (Atom P) Fa) Fa) Fa)
        ).
  apply INot; auto with ctx.
  apply (ENot_1 
           (Add
              (Add (Add G (Impl (Impl (Impl (Impl (Atom P) Fa) Fa) Fa) Fa))
                   (Impl (Atom P) Fa)) (Impl (Impl (Atom P) Fa) Fa))
           (Impl (Atom P) Fa)
        ).
  assumate.
  assumate.
  assumate.
Qed.

Lemma distr_4_neg_atm :
  forall (G:form -> Prop) (P :Prop),
    deriv G (Impl (Impl (Impl (Impl (Atom P) Fa) Fa) Fa) Fa) -> 
    deriv G (Impl (Impl (Atom P) Fa) Fa).
Proof.
  intros.
  apply (EImpl
           G
           (Impl (Impl (Impl (Impl (Atom P) Fa) Fa) Fa) Fa)
           (Impl (Impl (Atom P) Fa) Fa)
        ).
  auto.
  apply IImpl;auto with ctx.
  apply distr_4_neg_atm'.
Qed.

Hint Resolve distr_4_neg_atm distr_4_neg_atm'.

Lemma distr_neg_or' :
  forall (G : form -> Prop) (A B:form),
    deriv (Add G (Or (Impl (Impl A Fa ) Fa ) (Impl (Impl B Fa ) Fa)))
          (Impl (Impl (Or A B) Fa) Fa).
Proof.
  intros.
  apply INot;auto with ctx.
  apply (EOr
           (Add (Add G (Or (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa)))
                (Impl (Or A B) Fa))
           (Impl (Impl A Fa) Fa)
           (Impl (Impl B Fa) Fa)
           Fa); auto with ctx.
  apply Ax;auto with ctx. 
  apply (ENot_1
           (Add
              (Add (Add G (Or (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa)))
                   (Impl (Or A B) Fa)) (Impl (Impl A Fa) Fa))
           (Impl A Fa)
        ); auto with ctx.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add
              (Add
                 (Add (Add G (Or (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa)))
                      (Impl (Or A B) Fa)) (Impl (Impl A Fa) Fa)) A)
           (Or A B) );auto with ctx.
  apply IOr_1.
  assumate.
  assumate.
  assumate.  
  apply (ENot_1
           (Add
              (Add (Add G (Or (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa)))
                   (Impl (Or A B) Fa)) (Impl (Impl B Fa) Fa))
           (Impl B Fa) );auto with ctx.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add
              (Add
                 (Add (Add G (Or (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa)))
                      (Impl (Or A B) Fa)) (Impl (Impl B Fa) Fa)) B)          
           (Or A B));auto with ctx.
  apply IOr_2.
  assumate.
  assumate.
  assumate.
Qed.

Lemma distr_neg_or :
  forall (G : form -> Prop) (A B:form),
    deriv G (Or (Impl (Impl A Fa ) Fa ) (Impl (Impl B Fa ) Fa)) -> 
    deriv G (Impl (Impl (Or A B) Fa) Fa).
Proof.
  intros.
  apply (EImpl
           G
           (Or (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa))
           (Impl (Impl (Or A B) Fa) Fa)
        ).
  auto.
  apply IImpl;auto with ctx.
  apply distr_neg_or'.
Qed.

Lemma intro_db_neg' (G:form -> Prop) (A:form) :
  deriv (Add G A) (Impl (Impl A Fa) Fa).
Proof.
  intros.
  apply INot;auto with ctx.
  apply (ENot_1 
           (Add (Add G A) (Impl A Fa ))
           A
        );assumate.
Qed.           

Lemma intro_db_neg (G:form -> Prop) (A:form) :
  deriv G A -> 
  deriv G (Impl (Impl A Fa) Fa).
Proof.
  intros.
  apply (EImpl
           G
           A
           (Impl (Impl A Fa) Fa) ).
  auto.
  apply IImpl;auto with ctx.
  apply intro_db_neg'.
Qed.

Lemma elim_db_neg_weak (L:form -> Prop) (A:form) : 
  deriv L (Impl (Impl A Fa) Fa) ->
  deriv L (Impl A Fa) ->
  deriv L Fa.
Proof.
  intros.
  apply (EImpl L
               (Impl A Fa)
        );assumption.
Qed.  
Lemma intro_db_on_Impl' (L:form -> Prop) (A B:form) :
  deriv (Add L (Impl A B))
        (Impl (Impl (Impl A Fa) Fa)
              (Impl (Impl B Fa) Fa)).
Proof.
  apply IImpl;auto with ctx.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add (Add (Add L (Impl A B)) (Impl (Impl A Fa) Fa)) (Impl B Fa))
           (Impl A Fa)
        );auto with ctx.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add
              (Add (Add (Add L (Impl A B)) (Impl (Impl A Fa) Fa)) (Impl B Fa))
              A)
           B);auto with ctx.
  apply (EImpl
           (Add
              (Add
                 (Add (Add L (Impl A B)) (Impl (Impl A Fa) Fa))
                 (Impl B Fa))
              A)
           A);auto with ctx.
  assumate. assumate. apply union_assoc. apply union_assoc. apply Union_introl.
  firstorder. assumate. assumate.
Qed.

Lemma intro_db_on_Impl (L:form -> Prop) (A B:form) :
  deriv L (Impl A B) -> 
  deriv L (Impl (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa) ).
Proof.
  intros.
  apply (EImpl
           L
           (Impl A B)
           (Impl (Impl (Impl A Fa) Fa) (Impl (Impl B Fa) Fa))
        ).
  assumption.
  apply IImpl;auto with ctx.
  apply intro_db_on_Impl'.
Qed. 


(** ******** **)
(** Part 1.2 **)
(** ******** **)


(** Question 1.2.1 **)
Lemma deriv_Weakening (L L':form -> Prop) f :
  deriv L f ->  
  (forall g, L g -> L' g) -> 
  deriv L' f.
Proof.
  intros H. generalize L'.
    
  -induction H.
  (** Begin **)
   *intros;apply ATr. 
   *intros; auto with derv ctx.       
   *intros LHyp Hyp. apply IImpl. auto with ctx. apply IHderiv.
    unfold Add; intros; destruct H1; auto with derv ctx.    
   *intros LHy Hyp. eapply EImpl; auto with ctx.
   *intros; eapply IAnd;auto with ctx.
   *intros; eapply EAnd_1;auto with ctx.
   *intros; eapply EAnd_2;auto with ctx.
   *intros; eapply IOr_1;auto with ctx.
   *intros; eapply IOr_2;auto with ctx.
   *intros LHyp Hyp. apply (EOr LHyp A B).
    **apply IHderiv1; auto with ctx.
    **auto with ctx.
    **apply IHderiv2. unfold Add; intros g HTmp; destruct HTmp;
                        auto with derv ctx.
    **auto with ctx.
    **eapply IHderiv3. unfold Add; intros g HTmp; destruct HTmp;
                         auto with derv ctx.
    *intros; eapply INot;auto with ctx. apply IHderiv.
     unfold Add; intros g HTmp; destruct HTmp; auto with derv ctx.
    *intros; eapply ENot_1;auto with ctx.
    *intros; eapply ENot_2;auto with ctx.
    *intros; eapply IAll;auto with ctx. (* Proof 1 : auto.*)
    *intros; eapply EAll;auto with ctx.
    *intros; eapply IEx;auto with ctx.
    *intros; eapply EEx;auto with ctx.
     intros. apply (H0 x). unfold Add. auto with ctx derv.
     unfold Add. intros g HTmp;destruct HTmp; auto with ctx.
Qed.

Hint Resolve deriv_Weakening:derv.

(** Question 1.2.2 **)
Lemma deriv_substitution (L L': form -> Prop) f :
  deriv L f -> (forall f, L f -> deriv L' f) -> deriv L' f.
Proof.
  intros H. generalize L'.
  induction H;auto with derv ctx.
  (** Begin **)
  * intros. apply ATr.
  * intros LHyp Hyp; apply IImpl. auto with derv ctx. apply IHderiv.
    unfold Add. intros f HTmp; destruct HTmp; auto with derv ctx.
    unfold Add in H0.  apply (deriv_Weakening LHyp (Union LHyp (Singleton A))).
    apply Hyp. auto.
    auto with ctx derv.
    
  *intros LHyp Hyp. eapply EImpl; auto with ctx.
  *intros; eapply EAnd_1;auto with ctx.
  *intros; eapply EAnd_2;auto with ctx.
  *intros LHyp Hyp. apply (EOr LHyp A B).
  +apply IHderiv1; auto with ctx.
  +auto with ctx.
  +apply IHderiv2.
   unfold Add. intros f HTmp; destruct HTmp; auto with derv ctx.
   unfold Add in H0.  apply (deriv_Weakening LHyp (Union LHyp (Singleton A))).
   apply Hyp. auto. auto with ctx derv.
  +auto with ctx.
  +eapply IHderiv3.
   unfold Add. intros f HTmp; destruct HTmp; auto with derv ctx.
   unfold Add in H2.  apply (deriv_Weakening LHyp (Union LHyp (Singleton B))).
   apply Hyp. auto. auto with ctx derv.
   *intros LHyp Hyp; eapply INot;auto with ctx.
    apply IHderiv.
    unfold Add. intros f HTmp; destruct HTmp; auto with derv ctx.
    unfold Add in H.  apply (deriv_Weakening LHyp (Union LHyp (Singleton A))).
    apply Hyp. auto. auto with ctx derv.
   *intros; eapply ENot_1;auto with ctx.
   *intros; eapply IEx;auto with ctx.
   *intros LHyp Hyp; eapply EEx;auto with ctx.
    intros. apply (H0 x). unfold Add. auto with ctx derv.
    
    unfold Add. intros f HTmp; destruct HTmp; auto with derv ctx.
    unfold Add in H2. apply (deriv_Weakening LHyp (Union LHyp (Singleton (P x)))).
    apply Hyp. auto. auto with ctx derv.
Qed.

Hint Resolve deriv_substitution:derv.

(** ******** **)
(**  Part 2  **)
(** ******** **)


(** Question 2.1 **)
Fixpoint nnt (f : form) : form :=
  match f with 
  | Tr =>  Tr
  | Fa =>  Fa 
  | And A B =>
    And (nnt A) (nnt B)
  | Or A B =>
    Impl (Impl (Or (nnt A) (nnt B)) Fa) Fa
  | Impl A B =>
    Impl (nnt A) (nnt B) 
  | All P =>
    All (fun x => nnt (P x))
  | Ex P =>
    Impl (Impl (Ex (fun x => nnt (P x))) Fa) Fa
  | Atom x =>
    Impl (Impl (Atom x) Fa) Fa
  end.


(** Question 2.2.1 **)
Lemma  elim_double_negation (A:form) :
  forall (L: form -> Prop), deriv L (Impl (Impl (nnt A) Fa) Fa)  -> deriv L (nnt A).
Proof.
  induction A.
  - intros; simpl;apply ATr.
  -intros;simpl;apply (EImpl L (Impl Fa Fa)).
   --apply IImpl; auto with derv ctx.
   -- auto with derv ctx.
  - intros. simpl. apply IAnd.
    --apply IHA1.
      apply (EAnd_1 L (Impl (Impl (nnt A1) Fa) Fa) (Impl (Impl (nnt A2) Fa) Fa)).
      apply de_morg_and. apply H.
    --apply IHA2.
      apply (EAnd_2 L (Impl (Impl (nnt A1) Fa) Fa) (Impl (Impl (nnt A2) Fa) Fa)).
      apply de_morg_and. apply H.
  - intros. simpl in *. apply quad_to_double. auto.
  - intros. simpl in *.
    apply dist_neg_impl in H.
    apply IImpl. auto with ctx.
    apply (IHA2).
    (** On doit montrer A |- not not A ***)

    apply (EImpl (Add L (nnt A1))
                 (Impl (Impl (nnt A1) Fa) Fa)
          ).

    (** Premier cas on montre A => not not A **) 
    --apply intro_of_db_neg. apply Ax; auto with ctx.
     
    (** 
      On affaiblit pour montrer 

     L |- not not A => not not B 
    --------------------------------
     L,A1 |- not not A => not not B 

     *)
    --apply (deriv_Weakening L (Add L (nnt A1))).
      apply H.    
      auto with derv ctx.
     
  -intros. simpl in *.
   apply IAll. intros; apply H.
   apply (EAll
            (** context **)
            L
            (** Type **)
            A
            (** arguments *)
            x
            (** Predicate **)
            (fun x => (Impl (Impl (nnt (f x)) Fa) Fa) )
         ).
   (** 
     H : G |- ∀ ¬ ¬ P(x) 
     Goal : G |- ∀ ¬ ¬ P(x) 
     Strategie :
      1 - On montre que ¬ ∃ ¬ P(x) => ∀ ¬ ¬ P(x) grace au lemme "distr_neg_ex_all"
      2 - On montre sur l'hypothèse que  ¬ ¬ ∀ P(x) => ¬ ∃ ¬ P(x) grace au lemme 
          demorgan_all_to_ex_db_neg.
     On conclut.
     ¬(¬p + ¬q) => (¬¬p + ¬¬q)
     ¬¬(p + q) => 
    *)
   apply (distr_neg_ex_all ).
   apply demorgan_all_to_ex_db_neg in H0.
   auto.

  -intros. simpl in *.  apply distr_4_neg_ex. auto.
  -intros; simpl in *. apply distr_4_neg_atm. auto.
Qed.

Hint Resolve elim_double_negation:derv.

(** Somes definitions and properties about
         Contexte of double negation
                                        **)

Lemma set_to_nnt (A:form) (x:form) :
  Singleton A x -> Singleton (nnt A) (nnt x).
Proof.
  revert x.
  induction A;intros;simpl;auto with ctx;
    try ( destruct H || destruct H0 );apply In_singleton.
Qed.   

Hint Resolve set_to_nnt :ctx.

(** Definition of Contexte of double negation  **)

Inductive ctx_nnt (L:form -> Prop) : form -> Prop :=
  Ctx : forall x:form, L x -> ctx_nnt L (nnt x).

(** small properties on ctx_nnt **)

Lemma commut_union_ctx_nnt (Gamma : form -> Prop) (A:form ) :
  forall x:form, ctx_nnt (Union Gamma (Singleton A)) x ->
            Union (ctx_nnt Gamma) (Singleton (nnt A)) x.
Proof.
  intros.
  induction H.
  inversion H.
  apply Union_introl.
  constructor.
  auto.
  firstorder.
Qed.

Lemma ctx_nnt_commut_on_union (Gamma : form -> Prop) (A:form ) :
  forall x:form, deriv (ctx_nnt (Union Gamma (Singleton A))) x ->
            deriv (Union (ctx_nnt Gamma) (Singleton (nnt A))) x.
Proof.
  intros.
  
  apply (deriv_Weakening
           (ctx_nnt (Union Gamma (Singleton A)))
           (Union (ctx_nnt Gamma) (Singleton (nnt A)))
        ).
  assumption.
  apply commut_union_ctx_nnt.
Qed.

Hint Resolve ctx_nnt_commut_on_union commut_union_ctx_nnt:ctx.


(** Question 2.2.2 **)
Lemma soundness_of_nnt (L : form -> Prop) (A: form):  
  deriv L A  ->
  deriv (ctx_nnt L) (nnt A).
Proof.
  intros H. induction H. 

  (** On commence la preuve Par les deux cas de base **)
  -intros. apply ATr.
  -intros; simpl in *; apply Ax. apply Ctx . assumption.

  (** Pas d'induction *)
  -simpl.  apply IImpl;auto with derv ctx.
   (** Le auto se sert du lemme ctx_nnt_commut_on_union pour résoudre le cas *)
   unfold Add in *;auto with ctx.

  - eapply (EImpl).
    +apply IHderiv1;auto with ctx.
    +simpl in IHderiv2; assumption.
     
  -intros; eapply IAnd;auto with ctx.
  -apply (EAnd_1 (ctx_nnt Gamma)  (nnt A) (nnt B) ). auto with ctx.
  -apply (EAnd_2  (ctx_nnt Gamma) (nnt A) (nnt B) ). auto with ctx.
  -simpl. apply distr_neg_or. apply IOr_1. apply intro_of_db_neg. assumption.   
  -simpl. apply distr_neg_or. apply IOr_2. apply intro_of_db_neg. assumption.
  - 
    (** nnt G |- ¬¬nnt C **)
    apply elim_double_negation.
    (** nnt G ¬nnt C |- Fa **)
    apply INot;auto with ctx.
    (** on cut pour avoir : nnt G ¬nnt C |- ¬(nnt A \/ nnt B) **)
    (** Cut Procedure : 
                                                 Assumption
                                      ----------------------------------
nnt G ¬nnt C |- ¬(nnt A \/ nnt B)     nnt G ¬nnt C |- ¬¬(nnt A \/ nnt B)
------------------------------------------------------------------------
              nnt G ¬nnt C |- Fa
     **)
    
    apply (elim_db_neg_weak
             (Add (ctx_nnt Gamma) (Impl (nnt C) Fa)) (Or (nnt A) (nnt B))).
    simpl in IHderiv1.
    apply (deriv_Weakening
             (ctx_nnt Gamma)
             (Add (ctx_nnt Gamma) (Impl (nnt C) Fa))
             (Impl (Impl (Or (nnt A) (nnt B)) Fa) Fa)
          );auto with ctx.
    (**
                  We are here 
        ----------------------------------
         nnt G ¬nnt C |- ¬(nnt A \/ nnt B)
      
     **)
    apply INot;auto with ctx.
    
    (* nnt G, ¬nnt C, (nnt A \/ nnt B) |- Fa *)
    (** De nouveau un cut pour récupérer le but d'origine *)
    apply (ENot_1
             (Add (Add (ctx_nnt Gamma) (Impl (nnt C) Fa)) (Or (nnt A) (nnt B)))
             (nnt C)  
          ).
    (* nnt G, ¬nnt C, (nnt A \/ nnt B) |- nnt C  *)
    (** On peut maintenant utiliser Le schema d'élimination *)
    apply (EOr
             (Add (Add (ctx_nnt Gamma) (Impl (nnt C) Fa)) (Or (nnt A) (nnt B)))
             (nnt A)
             (nnt B)
             (nnt C)
          );auto with ctx.
    (*    
                            trivial 
      ----------------------------------------------------  
      nnt G, ¬nnt C, (nnt A \/ nnt B) |- (nnt A \/ nnt B)  
     *)
    +assumate.

    (**
        On a Assez d'hypothèses pour appliquer l'hypothèse
        d'induction (On nettoie le context avec un weakening avant)
     **)    
    +apply (deriv_Weakening
              (ctx_nnt (Add Gamma A))
              (Add
                 (Add
                    (Add (ctx_nnt Gamma) (Impl (nnt C) Fa))
                    (Or (nnt A) (nnt B))) (nnt A))
              (nnt C)
           );auto with ctx. intros.
     (** On récupère ce qui nous interesse dans l'environnement **)
     assert (forall x,
                (ctx_nnt (Add Gamma A)) x ->
                (Add
                   (Add
                      (Add (ctx_nnt Gamma) (Impl (nnt C) Fa))
                      (Or (nnt A) (nnt B))) 
                   (nnt A)
                ) x
            ).
     unfold Add.
     intros eltm HCtx.
     induction HCtx as [eltm HCtx]. induction HCtx.
     *apply Union_introl. apply Union_introl. apply Union_introl. constructor.
      assumption.
     *apply Union_intror. firstorder. 
     *apply H5. firstorder.
    (* On a finit *)
    +apply (deriv_Weakening
              (ctx_nnt (Add Gamma B))
              (Add
                 (Add
                    (Add (ctx_nnt Gamma) (Impl (nnt C) Fa))
                    (Or (nnt A) (nnt B)))
                 (nnt B))
              (nnt C)
           );auto with ctx. intros.
     (** On récupère ce qui nous interesse dans l'environnement **)
     assert (forall x,
                (ctx_nnt (Add Gamma B)) x ->
                (Add
                   (Add
                      (Add (ctx_nnt Gamma) (Impl (nnt C) Fa))
                      (Or (nnt A) (nnt B))) 
                   (nnt B)
                ) x
            ).
     unfold Add.
     intros eltm HCtx.
     induction HCtx as [eltm HCtx]. induction HCtx.
     *apply Union_introl. apply Union_introl. apply Union_introl. constructor.
      assumption.
     *apply Union_intror. firstorder. 
     *apply H5. firstorder.
    + assumate.
      

  -simpl in *;apply INot; unfold Add in *;auto with ctx.
  -simpl in *;apply (ENot_1 (ctx_nnt Gamma) (nnt A));auto with derv ctx.
  -simpl in *;apply (ENot_2);auto with derv ctx.
  -simpl in *;apply IAll; unfold Add in *;auto with derv ctx.
  -simpl in *;
     eapply (EAll (ctx_nnt Gamma) X a (fun x : X => nnt(P x))); auto with derv ctx.
  -simpl in *.
   apply intro_of_db_neg.
   eapply (IEx
             (ctx_nnt Gamma)
             X
             a
             ( fun x => nnt (P x) )
          ). auto with ctx.
  - (** nnt G |- ¬¬nnt B **)
    apply elim_double_negation.
    (** nnt G ¬nnt B |- Fa **)
    apply INot;auto with ctx.
    (** on cut pour avoir : nnt G ¬nnt G |- ¬(∃ P x) **)
    (** Cut Procedure : 
                                                 Assumption
                                      ----------------------------------
nnt G ¬nnt B |- ¬(nnt ∃ P x)     nnt G ¬nnt B |- ¬¬(nnt ∃ P x)
------------------------------------------------------------------------
              nnt G ¬nnt B |- Fa
     **)   
    apply (elim_db_neg_weak
             (Add (ctx_nnt Gamma) (Impl (nnt B) Fa)) (Ex (fun x : X => nnt (P x)))).
    simpl in IHderiv.
    apply (deriv_Weakening           
             (ctx_nnt Gamma)
             (Add (ctx_nnt Gamma) (Impl (nnt B) Fa))
             (Impl (Impl (Ex (fun x : X => nnt (P x))) Fa) Fa)
          );auto with ctx.
    (**
                  We are here 
        ----------------------------------
         nnt G ¬nnt B |- ¬(nnt ∃ P x)  
      
     **)
    apply INot;auto with ctx.
    
    (* nnt G, ¬nnt B, (nnt ∃ P x) |- Fa *)
    (** De nouveau un cut pour récupérer le but d'origine *)
    apply (ENot_1
             (Add (Add (ctx_nnt Gamma) (Impl (nnt B) Fa))
                  (Ex (fun x : X => nnt (P x))))
             (nnt B)
          ).
    
    apply (EEx
             (Add
                (Add (ctx_nnt Gamma) (Impl (nnt B) Fa))
                (Ex (fun x : X => nnt (P x))))
             (nnt B)
             X
             (fun x:X => nnt (P x) ) 
          ). intros.
    apply (deriv_Weakening
             (ctx_nnt (Add Gamma (P x)))
             (Add
                (Add (Add (ctx_nnt Gamma) (Impl (nnt B) Fa))
                     (Ex (fun x0 : X => nnt (P x0)))) (nnt (P x))
             ) 
             (nnt B)
          ).
    eapply H0;auto with ctx.
    
    *intros.
     unfold Add in *.
     (** On nettoie le context par modification de l'arbre **)
     apply union_assoc_swith_C_A.
     apply Union_intror.
     apply union_assoc_swith_C_A.
     apply Union_intror.
     (** On Conclut par commutativité des contextes **)
     apply commut_union_ctx_nnt in H3. assumption.
    * assumate.
    * assumate.
Qed.


(** ******** **)
(** Partie 3 **)
(** ******** **)


Inductive classic : form -> Prop :=
  Cem P : classic (Or P (Impl P Fa) ).

(** Question 3.1 **) 
Lemma excluded_middle_into_negated_trans (P:form):
  forall L:form -> Prop, deriv L (nnt (Or P (Impl P Fa) )). 
Proof.
  intros.
  (** 
On peut maintenant simmuler l'absurde 
Par la traduction nnt **)
  apply elim_double_negation. simpl.

  (** Begin **)
  apply INot;auto with ctx.
  apply (ENot_1
           (Add L (Impl (Impl (Impl (Or (nnt P) (Impl (nnt P) Fa)) Fa) Fa) Fa))
           (Impl (Impl (Or (nnt P) (Impl (nnt P) Fa)) Fa) Fa)
        );auto with ctx.
  
  apply INot;auto with ctx.
  (** Premier Cas ¬ (nnt A) **)
  apply (ENot_1
           (Add (Add L (Impl (Impl (Impl (Or (nnt P)
                                             (Impl (nnt P) Fa)) Fa) Fa) Fa))
                (Impl (Or (nnt P) (Impl (nnt P) Fa)) Fa))
           (Impl (nnt P) Fa)
        );auto with ctx.
  apply INot;auto with ctx.
  apply (ENot_1
           (Add
              (Add (Add L (Impl (Impl (Impl (Or (nnt P)
                                                (Impl (nnt P) Fa)) Fa) Fa) Fa))
                   (Impl (Or (nnt P) (Impl (nnt P) Fa)) Fa)) 
              (nnt P))
           (Or (nnt P) (Impl (nnt P) Fa))
        );auto with ctx.
  apply IOr_1;auto with ctx.
  assumate.
  assumate.

  (** Deuxieme Cas ¬¬ (nnt A) **)
  apply INot;auto with ctx.
  apply (ENot_1
           (Add
              (Add (Add L (Impl (Impl (Impl (Or (nnt P)
                                                (Impl (nnt P) Fa)) Fa) Fa) Fa))
                   (Impl (Or (nnt P) (Impl (nnt P) Fa)) Fa)) 
              (Impl (nnt P) Fa))
           (Or (nnt P) (Impl (nnt P) Fa))
        );auto with ctx.
  apply IOr_2;auto with ctx.
  assumate.
  assumate.
  assumate.  
Qed.

(** Intermediaire lemma cut for nnt formula **)

Lemma deriv_substitution_nnt (L L': form -> Prop) f :
  deriv (ctx_nnt L) (nnt f) ->
  (forall f, (ctx_nnt L) f -> deriv (ctx_nnt L') f) ->
  deriv (ctx_nnt L') (nnt f).
Proof.
  intros.
  eapply (deriv_substitution (ctx_nnt L) (ctx_nnt L') (nnt f)).
  +assumption.
  +firstorder.
Qed.  

(** Question 3.2 **)

Lemma elimination_of_excluded_middle (L :form -> Prop) (A:form) :
  deriv (Union L classic) A ->
  deriv (ctx_nnt L) (nnt A).
Proof.
  intros.
  apply (deriv_substitution_nnt (Union L classic) L A).
  +apply (soundness_of_nnt ). assumption.
  +intros. induction H0. induction H0.
   *apply soundness_of_nnt. apply Ax. assumption.  
   *induction H0. apply excluded_middle_into_negated_trans.
Qed.
Definition not (A:form) := Impl A Fa.

Hint Unfold not: ctx.

(** ******** **)
(** Partie 4 **)
(** ******** **)

(** Question 4.1 **)

(** Je donne ici deux définition de E 
une qui utilise l'implication logique de Coq  c'est E' 
et une seconde qui utilise l'implication de deriv. 
La justification est que l'on dispose du substitution lemma
Qui nous permet toujour de ramener l'implication à la 
dérivation de deux séquent par l'intèrmédiaire de l'implication 
logique de coq *)  

Inductive E' (X:Type) : form -> Prop :=
  E_refl' :forall x:X,
    E' X (Atom(x = x))
|E_sym' : forall x y:X,
    E' X (Atom( x = y)) ->  E' X (Atom (y = x))
|E_trans' : forall x y z:X,
    E' X ( (Atom( x = y))) -> E' X ( ((Atom (y = z)))) ->
    E' X (((Atom( x = z)) )).
      
(** Nous utiliserons cette définition pour être cohérent avec la 
définition de A ci-dessous **) 
Inductive E (X:Type) : form -> Prop :=
  E_refl :forall x:X,
    E X (Atom(x = x))    
|E_sym : forall x y:X,
    E X (Impl (Atom( x = y)) (Atom (y = x)))
|E_trans : forall x y z:X,
    E X (Impl (Atom( x = y)) (Impl  (Atom (y = z))  (Atom( x = z)) )).


(** Question 4.2 **)
Inductive A : form -> Prop :=
  Ax_Pred :  forall (n:nat),
    A (Atom( 0 <> (S n) ))
 |Ax_Ext : forall (n m:nat),
     A (Impl (Atom(S n = S m)) (Atom( n = m)))
 |Ax_Ind : forall (P : nat ->form),
     A (Impl (P 0)
          (Impl (All( fun (n:nat) => Impl (P n) (P (S n))))
                (All (fun (n:nat) => P n)))
       ).

(** Question 4.3 **)
Definition deriv_PA (L:form -> Prop) (F:form) :=
  deriv (Union (Union L classic) (Union A (E nat))) F.

Definition deriv_HA (L:form -> Prop) (F:form) :=
  deriv (Union L (Union A (E nat))) F.

Definition deriv_HA_nnt (L:form -> Prop) (F:form) :=
  deriv (ctx_nnt (Union L (Union A (E nat)))) F.

Require Import Omega.


(** Deux énoncé La premiere utilise la définition E' et la seconde E **)
(** Question 4.2.1 avec E' **)
Lemma nnt_E'_in_J_is_drv (P:form):
  E' nat P -> deriv (E' nat) (nnt P).
Proof.
  intros. induction H.
  (**  Par l'absurde **)
  -apply elim_double_negation. apply intro_db_neg. apply intro_db_neg.
   apply Ax. apply E_refl'.
  -apply elim_double_negation. apply intro_db_neg. apply intro_db_neg.
   apply Ax. apply E_sym'. auto.
   
  -apply elim_double_negation. apply intro_db_neg. apply intro_db_neg.
   apply Ax.  apply (E_trans' _ x y z);assumption.
Qed.
(** Question 4.2.1 avec E **)
Lemma nnt_E_in_J_is_drv (P:form):
  E nat P -> deriv (E nat) (nnt P).
Proof.
  intros. induction H.
  (**  Par l'absurde **)
  -apply elim_double_negation. apply intro_db_neg. apply intro_db_neg.
   apply Ax. apply E_refl.   
  -simpl. apply IImpl;auto with ctx; apply IImpl;auto with ctx.
   apply (EImpl _ (Impl (Atom (x = y)) Fa)).
   --apply IImpl;auto with ctx.
     apply (EImpl _ (Atom (y = x))).
     ---apply (EImpl _ (Atom (x = y))).
        -----apply Ax. apply Union_intror. auto with ctx.
        ----- apply Ax. do 3 apply Union_introl. apply E_sym.
     ---apply Ax. auto with ctx.
   --apply Ax;auto with ctx.
        
  - simpl. do 3 (apply IImpl;auto with ctx). apply
                                               (EImpl _ (Impl (Atom (y = z)) Fa)).
    -- apply IImpl;auto with ctx. apply (EImpl _ (Impl (Atom (x = y)) Fa)).
       ---apply IImpl;auto with ctx. apply (EImpl _ (Atom (x = z))).
          -----apply (EImpl _ (Atom (y = z))). 
          ------ apply Ax;auto with ctx.
          ------ apply (EImpl _ (Atom (x = y))).
          apply Ax;auto with ctx.
          apply Ax. do 5 apply Union_introl. eapply E_trans.
          ----- apply Ax;auto with ctx.
       ---apply Ax;auto with ctx. do 3 apply Union_introl. auto with ctx.
    -- apply Ax;auto with ctx.
Qed.
(** !! On utilisera La définition de E dans le reste de la preuve. !! **)

Lemma nnt_A_in_J_is_drv (P:form):
  A P -> deriv A (nnt P).
Proof.
  intros. induction H.
  (**  Par l'absurde **)
  +apply elim_double_negation. repeat (apply intro_db_neg). apply Ax.
   apply Ax_Pred.
  +simpl. apply intro_db_on_Impl. apply Ax. apply (Ax_Ext n m ).
  + simpl. apply Ax.
    apply ( Ax_Ind (fun x => nnt (P x)) ).
Qed.

(** Lemma On union of A and E just a consequence of two last lemma**)

Lemma nnt_EA_in_J_is_drv (P:form):
  (Union (E nat) A) P ->  deriv (Union (E nat) A) (nnt P).
Proof.
  intros.
  -inversion_clear H as [ x Assumption_of_E | x Assumption_of_A ].
   --apply (deriv_Weakening (E nat) (Union (E nat) A)).
     --- apply nnt_E_in_J_is_drv. assumption.
     --- intros. apply Union_introl. assumption.
   -- apply (deriv_Weakening A (Union (E nat) A)).
      --- apply nnt_A_in_J_is_drv. assumption.
      --- intros. apply Union_intror. assumption.
Qed.
     
(** Question 4.2.2 **)
Lemma interp_PA_in_HA (L:form -> Prop) (F:form) :
  deriv_PA L F -> deriv_HA_nnt L (nnt F).
Proof.
  unfold deriv_HA_nnt, deriv_PA. intros.  
  apply (deriv_substitution_nnt
           (Union (Union L classic) (Union A (E nat)))
           (Union L (Union A (E nat))) F
        ).
  apply soundness_of_nnt. assumption.
  
  intros f Case_Ctx. 
  inversion_clear Case_Ctx as [temoin Real_case]. clear f.
  induction Real_case as [ temoin Classic | temoin Equa]. 
  *induction Classic as [temoin In_L | temoin In_excl_middl ]. 
  -apply soundness_of_nnt. apply Ax. firstorder.  
  -induction In_excl_middl as [f Excl_middl].
   apply excluded_middle_into_negated_trans.
   * inversion_clear Equa as [temoin' Peano | temoin' Equality ].
     apply soundness_of_nnt. apply Ax. firstorder.
     apply soundness_of_nnt. apply Ax. firstorder.
Qed.

(** **************************************** **)
(** Partie 5 Consistency of Peano Arithmetic **)
(** **************************************** **)


(** Question 5.1 **)

Fixpoint intf  (f:form) :  Prop :=
  match f with
  | Tr => True
  | Fa => False
  | And A B   => (intf A) /\ (intf B) 
  | Or  A B   => (intf A) \/ (intf B) 
  | Impl A B  => (intf A) -> (intf B) 
  | @All A P    => forall (x :A), (intf (P x))
  | @Ex  A P    => exists (x :A), (intf (P x))
  | Atom x    => x
  end.


(** Question 5.2 **)

Lemma soundness_of_intf (L :form -> Prop) (F:form ) :
  deriv L F -> (forall x:form, L x -> (intf x) ) -> intf F.
Proof.
  intros;induction H;firstorder.
  -simpl. intros. apply IHderiv. intros. inversion_clear H3.
   --apply H0;assumption.
   --inversion H4;subst;assumption.
  -apply IHderiv2. intros. inversion_clear H6.
   -- apply H0. assumption.
   --inversion H7. subst. assumption.
  -apply IHderiv3. intros. inversion_clear H6.
   --apply H0. assumption.
   --inversion H7. subst. assumption.
  -simpl in *. intros. apply IHderiv. intros. inversion_clear H3. 
   --apply H0. assumption.
   --inversion H4. subst. assumption.
  - apply (H1 x);auto with ctx. intros. inversion_clear H4.
    --apply H0. assumption.
    -- inversion H5. subst. assumption.
Qed.
Require Import Arith.
Check forall A B C D, A -> (B -> (C -> D)) .
    
(** Question 5.3 **)

Lemma soundness_of_E_A :
  forall x:form, (Union (E nat) A) x -> (intf x) .
Proof.
  intros. induction H.
  -induction H;simpl in *;auto with arith. omega.
  -intros. induction H;simpl;subst;auto with arith.
   -- induction x.
      ---assumption.
      ---apply H0. assumption.
Qed.

(** Definition of Empty context **)
Inductive Empty_ctx : form -> Prop :=.

(** We show that Empty is the neutral element for Union  **)

Lemma Union_left_unit (A : form -> Prop) (x:form): 
  Union Empty_ctx A x <-> A x.
Proof.
  split.
  - intros. inversion_clear H as [x0 Absurd_case | x0 In_A ].
    --inversion Absurd_case.
    --assumption. 
  -intros. apply Union_intror. assumption.
Qed.


(** ***************************************************** **)
(**           Consictency of Arithmetic of Peano          **)        
(** ***************************************************** **)


(** Question 5.4 **)
Lemma Consistency_of_PA  :
  ~ deriv_PA Empty_ctx Fa.
Proof.
  - intro Cons_of_PA.
    --apply interp_PA_in_HA in Cons_of_PA . simpl in Cons_of_PA.
      apply soundness_of_intf in Cons_of_PA.
      --- simpl in Cons_of_PA. assumption.          
      --- intros. inversion_clear H as [ temoin Assumption_of_HA ].
          apply -> Union_left_unit in Assumption_of_HA.
          apply union_comm in Assumption_of_HA.
          apply (soundness_of_intf (Union (E nat) A)).
          apply nnt_EA_in_J_is_drv. assumption.
          apply soundness_of_E_A.
Qed.




