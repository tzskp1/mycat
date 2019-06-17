From mathcomp Require Import all_ssreflect.
Require Import equivalence fundamental.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Section Cats.
Lemma cats_associativity : @Category.associativity_of_morphisms category _ compf funs_equivMixin.
Proof.
  move => /= C D E F h i j.
  set L := @NatMixin _ _ ((j \compf i) \compf h) (j \compf (i \compf h)) (idn _) (idn_map_naturality _).
  set R := @NatMixin _ _ (j \compf (i \compf h)) ((j \compf i) \compf h) (idn _) (idn_map_naturality _).
  do !apply: ex_intro;
  apply (@NaturalIsomorphisms _ _ _ _ L R);
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Defined.

Lemma cats_compm0 : @Category.identity_morphism_is_right_identity category _ idf compf funs_equivMixin.
Proof.
  move => /= C D f.
  by apply: compf0.
Defined.

Lemma cats_comp0m : @Category.identity_morphism_is_left_identity category _ idf compf funs_equivMixin.
Proof.
  move => /= C D f.
  by apply: comp0f.
Defined.

Lemma cats_comp_left : @Category.compatibility_left category _ compf funs_equivMixin.
Proof.
  move => ? ? ? f f' g /= [N] [M] [H].
  set L := @NatMixin _ _ (g \compf f) (g \compf f')
                                  (g \compfn N) (compfn_naturality _ _).
  set R := @NatMixin _ _ (g \compf f') (g \compf f)
                                  (g \compfn M) (compfn_naturality _ _).
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _ L R) => X.
  apply: Isomorphisms => /=;
  (apply: Congruence.etrans;
   first by (apply/symP; apply pres_comp));
  (apply: Congruence.etrans;last by apply id_id);
  apply: pres_equiv; by case: (H X).
Defined.

Lemma cats_comp_right : @Category.compatibility_right category _ compf funs_equivMixin.
Proof.
  move => ? ? ? f g g' /= [N] [M] [H].
  set L := @NatMixin _ _ (g \compf f) (g' \compf f)
                                  (N \compnf f) (compnf_naturality _ _).
  set R := @NatMixin _ _ (g' \compf f) (g \compf f)
                                  (M \compnf f) (compnf_naturality _ _).
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _ L R) => X;
  apply: Isomorphisms => /=;
  by case: (H (f X)).
Defined.

Notation cats_catMixin := (CatMixin cats_associativity cats_compm0 cats_comp0m cats_comp_left cats_comp_right).
Canonical cats_catType := Eval hnf in CatType category cats_catMixin.
End Cats.
Notation cats := cats_catType.

Section Pushout.
Variables C D : category.
Variable F : Fun (C, D).
Notation FC := { B | exists A, F A = B }.
Definition compF (A B C : FC) := 
  @compm _ (Category.class D) (proj1_sig A) (proj1_sig B) (proj1_sig C).

Lemma FC_associativity : @Category.associativity_of_morphisms FC _ compF (fun A B => @equiv D (proj1_sig A) (proj1_sig B)).
Proof.
  move => [??] [??] [??] [??] /= h i j.
  apply compmA.
Defined.

Lemma FC_compm0 : @Category.identity_morphism_is_right_identity FC _ (fun A => @Category.id _ _ (proj1_sig A)) compF (fun A B => @equiv D (proj1_sig A) (proj1_sig B)).
Proof.
  move => [??] [??] /= f.
  apply compm0.
Defined.

Lemma FC_comp0m : @Category.identity_morphism_is_left_identity FC _ (fun A => @Category.id _ _ (proj1_sig A)) compF (fun A B => @equiv D (proj1_sig A) (proj1_sig B)).
Proof.
  move => [??] [??] /= f.
  apply comp0m.
Defined.

Lemma FC_comp_left : @Category.compatibility_left FC _ compF (fun A B => @equiv D (proj1_sig A) (proj1_sig B)).
Proof.
  move => [??] [??] [??] /= f f' g.
  apply comp_left.
Defined.

Lemma FC_comp_right : @Category.compatibility_right FC _ compF (fun A B => @equiv D (proj1_sig A) (proj1_sig B)).
Proof.
  move => [??] [??] [??] /= f g g'.
  apply comp_right.
Defined.

Notation FC_catMixin := (CatMixin FC_associativity FC_compm0 FC_comp0m FC_comp_left FC_comp_right).
Canonical FC_catType := Eval hnf in CatType FC FC_catMixin.
End Pushout.
Notation pushout := FC_catType.

Section Funs.
Variable C D : category.
Lemma funs_associativity : @Category.associativity_of_morphisms _ _ (@compn C D) (@nats_equivMixin C D).
Proof.
  move => C' D' E F h i j X /=.
  apply compmA.
Defined.

Lemma funs_compm0 : @Category.identity_morphism_is_right_identity _ _ (@idn C D) (@compn C D) (@nats_equivMixin C D).
Proof.
  move => C' D' f X.
  apply compm0.
Defined.

Lemma funs_comp0m : @Category.identity_morphism_is_left_identity _ _ (@idn C D) (@compn C D) (@nats_equivMixin C D).
Proof.
  move => C' D' f X.
  apply comp0m.
Defined.

Lemma funs_comp_left : @Category.compatibility_left _ _ (@compn C D) (@nats_equivMixin C D).
Proof.
  move => ? ? ? f f' g /= H X.
  apply comp_left.
  move: f f' H => [f ?] [f' ?] /= H.
  apply H.
Defined.

Lemma funs_comp_right : @Category.compatibility_right _ _ (@compn C D) (@nats_equivMixin C D).
Proof.
  move => ? ? ? f f' g /= H X.
  apply comp_right.
  move: f f' H => [f ?] [f' ?] /= H.
  apply H.
Defined.
End Funs.
Notation funs_catMixin C D := (CatMixin (@funs_associativity C D) (@funs_compm0 C D) (@funs_comp0m C D) (@funs_comp_left C D) (@funs_comp_right C D)).
Canonical funs_catType C D := Eval hnf in CatType Fun (C, D) (funs_catMixin C D).
Notation funs := funs_catType.
Notation "'Fun' ( C , D )" := (funs C D).

Section Opposite.
Variable C : category.
Definition op_comp (A B C' : Ob C) (g : Mor (C', B)) (f : Mor (B, A)) := compm f g.
Definition op_mor := (fun (B A : Ob C) => Mor (A, B)).
Notation op_id := (fun A => @Category.id _ _ A).

Lemma op_associativity : @Category.associativity_of_morphisms _ op_mor op_comp (fun A B => @equiv C B A).
Proof.
  move => ? ? ? ? h i j.
  apply/symP; by apply: compmA.
Defined.

Lemma op_compm0 : @Category.identity_morphism_is_right_identity _ op_mor op_id op_comp (fun A B => @equiv C B A).
Proof.
  move => ? ? /= f.
  by apply comp0m.
Defined.

Lemma op_comp0m : @Category.identity_morphism_is_left_identity _ op_mor op_id op_comp (fun A B => @equiv C B A).
Proof.
  move => ? ? /= f.
  by apply compm0.
Defined.

Lemma op_comp_left : @Category.compatibility_left _ op_mor op_comp (fun A B => @equiv C B A).
Proof.
  move => ? ? ? /= f f' g.
  by apply comp_right.
Defined.

Lemma op_comp_right : @Category.compatibility_right _ op_mor op_comp (fun A B => @equiv C B A). 
Proof.
  move => ? ? ? /= f f' g.
  by apply comp_left.
Defined.

Notation op_catMixin := (CatMixin op_associativity op_compm0 op_comp0m op_comp_left op_comp_right).
Canonical op_catType := Eval hnf in CatType (Ob C) op_catMixin.
End Opposite.
Notation opposite_category := op_catType.
Notation "'Op' C" := (opposite_category C) (at level 1).

Section Opposite.
Variable C : Ob cats.
Local Notation F := (@FunMixin (Op (Op C)) C ssrfun.id (fun x y f => f) _ _ _ : Mor(Op (Op C), C)).
Local Notation G := (@FunMixin C (Op (Op C)) ssrfun.id (fun x y f => f) _ _ _ : Mor(C, Op (Op C))).
Local Notation N := (@NatMixin _ _ (G \compf F) (idf Op (Op C)) (fun X : Ob (Op (Op C)) => id : Mor ((G \compf F) X, (idf Op (Op C)) X)) _).
Local Notation M := (@NatMixin _ _ (idf Op (Op C)) (G \compf F) (fun X : Ob C => id : Mor ((idf Op (Op C)) X, (G \compf F) X)) _).
Local Notation N' := (@NatMixin  _ _ (F \compf G) (idf C) (fun X : Ob C => id : Mor ((F \compf G) X, (idf C) X)) _).
Local Notation M' := (@NatMixin _ _ (idf C) (F \compf G) (fun X : Ob (Op (Op C)) => id : Mor ((idf C) X, (F \compf G) X)) _).
Lemma dualK : @equiv_op (obs_equivType cats) (Op (Op C)) C.
do !apply: ex_intro.
apply: (@Isomorphisms _ _ _ F G) => //.
+ by apply: idf_id_id.
+ by apply: idf_pres_comp.
+ by apply: idf_id_id.
+ by apply: idf_pres_comp.
+ intros; do !apply: ex_intro.
  apply: (@NaturalIsomorphisms _ _ _ _ N M _).
  - move=> ? ? f /=;
    (apply: Congruence.etrans; first by (apply/symP; apply: compm0));
    by apply: compm0.
  - move=> ? ? f /=;
    (apply: Congruence.etrans; first by (apply/symP; apply: compm0));
    by apply: compm0.
  - move=> ? ? X; apply: Isomorphisms; apply/symP; by apply compm0.
+ intros; do !apply: ex_intro.
  apply: (@NaturalIsomorphisms _ _ _ _ N' M' _).
  - move=> ? ? f /=;
    (apply: Congruence.etrans; first by (apply/symP; apply: comp0m));
    by apply: compm0.
  - move=> ? ? f /=;
    (apply: Congruence.etrans; first by (apply/symP; apply: comp0m));
    by apply: compm0.
  - move=> ? ? X; apply: Isomorphisms; apply/symP; by apply compm0.
Qed.
End Opposite.

Section Ordinal.
Variable n : nat.
(* 0 --> 1 *)
(* |     | *)
(* >     > *)
(* 2 --> 3 *)
Definition catnm (x y : ordinal n) :=
  match x, y with
  | Ordinal i _, Ordinal j _ =>
    i <= j : Prop
  end.

Definition catnc
           (x y z : ordinal n)
           (g : catnm y z)
           (f : catnm x y) : catnm x z.
case: x y z f g => [x Hx] [y Hy] [z Hz] /=.
exact: leq_trans.
Defined.
Definition catnm_equivMixin x y := trivial_equivMixin (catnm x y).

Definition catn_id (x : ordinal n) : catnm x x.
case: x => [x Hx] /=.
exact: leqnn.
Defined.

Lemma catn_associativity : Category.associativity_of_morphisms catnc catnm_equivMixin.
Proof. by []. Defined.

Lemma catn_compm0 : Category.identity_morphism_is_right_identity catn_id catnc catnm_equivMixin.
Proof. by []. Defined.

Lemma catn_comp0m : Category.identity_morphism_is_left_identity catn_id catnc catnm_equivMixin.
Proof. by []. Defined.

Lemma catn_comp_left : Category.compatibility_left catnc catnm_equivMixin.
Proof. by []. Defined.

Lemma catn_comp_right : Category.compatibility_right catnc catnm_equivMixin.
Proof. by []. Defined.
Notation catn_catMixin := (CatMixin catn_associativity catn_compm0 catn_comp0m catn_comp_left catn_comp_right).
Canonical catn_catType := Eval hnf in CatType (ordinal n) catn_catMixin.
End Ordinal.
Notation catn := catn_catType.
Example cat0 : category := catn 0.
Example cat1 : category := catn 1.
Example cat2 : category := catn 2.
Example cat4 : category := catn 4.
Notation square := cat4.

Definition smush C D (A : Ob D) :=
  @FunMixin C D (fun _ : Ob C => A)
            (fun _ _ _ => id)
            (fun _ : Ob C => reflP)
            (fun _ _ _ _ _ => comp0m id)
            (fun _ _ _ _ _ => reflP).

Canonical smush_funType C D (A : Ob D) := Eval hnf in FunType C D (@smush C D A).

Section CanonicalEmmbedding0.
Variable C : category.
Local Definition embedding0_ob (A : Ob cat0) :=
  match A with
  | @Ordinal _ m x =>
    match x in (_ = H) return (if H then Ob C else True) with
    | erefl => I
    end
  end.
Local Definition embedding0_mor (A : Ob cat0) :=
  match A with
  | @Ordinal _ m x =>
    match x in (_ = H) return
          (if H then (forall B (_ : Mor(A, B)), Mor(embedding0_ob A, embedding0_ob B)) else True) with
    | erefl => I
    end
  end.

Definition canonical_embedding0 : Fun(cat0, C).
refine (@FunMixin _ _ embedding0_ob embedding0_mor _ _ _)
        => //; case => //.
Defined.
End CanonicalEmmbedding0.

Canonical canon0_funType C := Eval hnf in FunType cat0 C (canonical_embedding0 C).

Section CanonicalEmmbedding2.
Variable C : category.
Local Definition embedding2_ob {T : Type} (E F : T) (A : Ob cat2) :=
  match A with
  | Ordinal 0 _ => E
  | Ordinal 1 _ => F
  | Ordinal _ _ => F (* absurd case *)
  end.

Local Definition embedding2_mor (A B : Ob C) (g : Mor(A, B)) (E F : Ob cat2) (f : Mor(E, F)) :
    Mor(embedding2_ob A B E, embedding2_ob A B F).
case: E F f => [m Hm] [n Hn] f.
case: m Hm f => [|m] Hm f.
 case: n Hn f => [|n] Hn f.
  apply id.
 case: n Hn f => [|n] Hn f.
  apply g.
 case: n Hn f => //.
case: m Hm f => [|m] Hm f.
 case: n Hn f => [|n] Hn //= f.
 case: n Hn f => [|n] Hn //= f.
 apply id.
case: m Hm f => //.
Defined.

Definition canonical_embedding2 (A B : Ob C) (f : Mor(A, B)) : Fun(cat2, C).
refine (@FunMixin _ _ (embedding2_ob A B)
                 (@embedding2_mor A B f)
                 _ _ _) => //.
case => m Hm; do !case:m Hm => [|m] Hm //=; by apply/reflP.
case => [m Hm] [n Hn] [p Hp] h i;
do !case:m Hm h => [|m] Hm h //=;
do !case:n Hn i h => [|n] Hn i h //=;
do !case:p Hp i h => [|p] Hp i h //=;
(try by apply compm0); by apply comp0m.
case => [m Hm] [n Hn] h i H;
do !case:m Hm i h H => [|m] Hm i h H //=;
do !case:n Hn i h H => [|n] Hn i h H //=;
by apply/reflP.
Defined.
End CanonicalEmmbedding2.

Section TrivialCategory.
Variable C : category.
Local Notation "f == g" := (@equiv_op (obs_equivType C) f g).
Definition triv_mor (x y : Ob C) := x == y.
Definition triv_comp (x y z : Ob C) : y == z -> x == y -> x == z.
Proof. move=> H1 H2. by apply/transP; first apply H2. Defined.

Lemma tcat_associativity : @Category.associativity_of_morphisms _ triv_mor triv_comp (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.

Lemma tcat_compm0 : @Category.identity_morphism_is_right_identity _
                                                                  triv_mor
                                                                  (fun _ => reflP) 
                                                                  triv_comp
                                                                  (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.
Lemma tcat_comp0m : @Category.identity_morphism_is_left_identity _
                                                                 triv_mor
                                                                 (fun _ => reflP)
                                                                 triv_comp
                                                                 (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.

Lemma tcat_comp_left : @Category.compatibility_left _ triv_mor triv_comp (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.

Lemma tcat_comp_right : @Category.compatibility_right _ triv_mor triv_comp (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.
Notation tcat_catMixin := (CatMixin tcat_associativity tcat_compm0 tcat_comp0m tcat_comp_left tcat_comp_right).
Definition tcat_catType := Eval hnf in CatType (Ob C) tcat_catMixin.
End TrivialCategory.
Notation tcat := tcat_catType.
Definition tcatn n := tcat (catn n).

Section TrivialEmmbedding.
Variable n : nat.

Definition triv_mor' (x y : nat) := x == y.
Definition triv_id (x : nat) : triv_mor' x x.
  apply/eqP; apply: erefl.
Defined.
Definition triv_comp' (x y z : nat) : y == z -> x == y -> x == z.
Proof. by move/eqP=> -> /eqP ->. Defined.

Lemma tcat_associativity' : @Category.associativity_of_morphisms _ triv_mor' triv_comp' (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.

Lemma tcat_compm0' : @Category.identity_morphism_is_right_identity _
                                                                  triv_mor'
                                                                  triv_id
                                                                  triv_comp'
                                                                  (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.
Lemma tcat_comp0m' : @Category.identity_morphism_is_left_identity _
                                                                 triv_mor'
                                                                 triv_id
                                                                 triv_comp'
                                                                 (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.

Lemma tcat_comp_left' : @Category.compatibility_left _ triv_mor' triv_comp' (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.

Lemma tcat_comp_right' : @Category.compatibility_right _ triv_mor' triv_comp' (fun x y => trivial_equivMixin (x == y)).
Proof. by []. Defined.
Notation tcat_catMixin' := (CatMixin tcat_associativity' tcat_compm0' tcat_comp0m' tcat_comp_left' tcat_comp_right').
Definition tcat_catType' := Eval hnf in CatType nat tcat_catMixin'.

Definition triv_incl (t : Ob (tcatn n)) : Ob tcat_catType' := t.
Definition triv_incl_mor (s t : Ob (tcatn n)) (f : Mor (s, t)) : Mor(triv_incl s, triv_incl t).
Proof.
  suff ->: s = t by apply id.
  move: s t f=> [m i] [m' i'] [f [g p]].
  apply: val_inj.
  apply/eqP.
  rewrite eqn_leq.
  by apply/andP.
Defined.
Lemma triv_pres_equiv : Functor.preserve_equivalence triv_incl_mor.
Proof. by move=> [m i] [m' i'] [f [g p]] [f' [g' p']]. Defined.

Lemma triv_pres_comp : Functor.preserve_composition triv_incl_mor.
Proof. by move=> [m i] [m' i'] [f [g p]] [f' [g' p']]. Defined.

Lemma triv_id_id : Functor.maps_identity_to_identity triv_incl_mor.
Proof. by move=> [m i]. Defined.

Definition trivial_inclusion : Fun(tcatn n, tcat_catType') := FunMixin triv_id_id triv_pres_comp triv_pres_equiv.
End TrivialEmmbedding.
(* because of the silly unify problem *)
Section Product.
Variable C D : category.
Definition prod_mor (a b : Ob C * Ob D) := prod (Mor(fst a, fst b)) (Mor(snd a, snd b)).
Definition prod_id (a : Ob C * Ob D) : prod_mor a a := (@Category.id _ _ (fst a), @Category.id _ _ (snd a)).
Definition prod_comp (a b c : Ob C * Ob D) (bc : prod_mor b c) (ab : prod_mor a b) : prod_mor a c :=
  (fst bc \compm fst ab, snd bc \compm snd ab).
Definition prod_cat_equivMixin A B := prod_equivMixin (@equiv C (fst A) (fst B)) (@equiv D (snd A) (snd B)).

Arguments prod_comp /.
Lemma prod_associativity : @Category.associativity_of_morphisms _ prod_mor prod_comp prod_cat_equivMixin.
Proof. by move=> [??] [??] [??] [??] [??] [??] [??]; split; apply compmA. Qed.

Lemma prod_compm0 : @Category.identity_morphism_is_right_identity _
                                                                  prod_mor
                                                                  prod_id
                                                                  prod_comp
                                                                  prod_cat_equivMixin.
Proof. by move=> [??] [??] [??]; split; apply compm0. Defined.
Lemma prod_comp0m : @Category.identity_morphism_is_left_identity _
                                                                  prod_mor
                                                                  prod_id
                                                                  prod_comp
                                                                  prod_cat_equivMixin.
Proof. by move=> [??] [??] [??]; split; apply comp0m. Defined.

Lemma prod_comp_left : @Category.compatibility_left _ prod_mor prod_comp prod_cat_equivMixin.
Proof. move=> [??] [??] [??] [??] [??] [??] [??]; split; by apply: comp_left. Defined.

Lemma prod_comp_right : @Category.compatibility_right _ prod_mor prod_comp prod_cat_equivMixin.
Proof. move=> [??] [??] [??] [??] [??] [??] [??]; split; by apply: comp_right. Defined.
Notation prod_catMixin := (CatMixin prod_associativity prod_compm0 prod_comp0m prod_comp_left prod_comp_right).
Canonical prod_catType := Eval hnf in CatType (Ob C * Ob D) prod_catMixin.
Definition pfst : Fun(prod_catType, C).
  apply: (@FunMixin prod_catType C fst (fun _ _ => fst)).
+ move=> ?; by apply/reflP.
+ move=> ? ? ? ? ?; by apply/reflP.
+ by move=> ? ? [??] [??] [??].
Defined.

Definition psnd : Fun(prod_catType, D).
  apply: (@FunMixin prod_catType D snd (fun _ _ => snd)).
+ move=> ?; by apply/reflP.
+ move=> ? ? ? ? ?; by apply/reflP.
+ by move=> ? ? [??] [??] [??].
Defined.
End Product.
Notation "a * b" := (prod_catType a b).

Section Point.
Inductive point_ob :=
| pt : point_ob.

Definition point_mor (x y : point_ob) := point_ob.
Definition point_comp (x y z : point_ob) : point_mor y z -> point_mor x y -> point_mor x z := (fun _ _ => pt).

Lemma point_associativity : @Category.associativity_of_morphisms _ _ point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => /= C D E F h i j; by apply/reflP. Defined.

Lemma point_compm0 : @Category.identity_morphism_is_right_identity _ _ (fun _ => pt) point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => /= C D []; by apply/reflP. Defined.

Lemma point_comp0m : @Category.identity_morphism_is_left_identity _ _ (fun _ => pt) point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => /= C D []; by apply/reflP. Defined.

Lemma point_comp_left : @Category.compatibility_left _ _ point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => [] [] [] [] [] [] _; by apply/reflP. Defined.

Lemma point_comp_right : @Category.compatibility_right _ _ point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => [] [] [] [] [] [] _; by apply/reflP. Defined.

Notation point_catMixin := (CatMixin point_associativity point_compm0 point_comp0m point_comp_left point_comp_right).
Canonical point_catType := Eval hnf in CatType _ point_catMixin.
End Point.
Coercion pto_pt (_ : point_ob) := point_catType.

Section Point.
Variable C : category.
Local Definition sp := @smush_funType pt C.
Local Notation Fm := (fun x y (f : Mor(x, y)) => (@NatMixin _ _ (sp x) (sp y) (fun _ => f) _)).
Definition ptC : Fun (C, Fun (pt, C)).
  apply: (@FunMixin _ _ (fun x => @smush pt C x) Fm _ _ _).
  move=> x y f z a f' /=.
  apply: Congruence.etrans; last apply: comp0m.
  by apply/symP; apply: compm0.
  move=> x y [] /=.
  by apply/reflP.
  move=> x y z w f g [] /=.
  by apply/reflP.
  by move=> x y z f f' H [].
Defined.

Definition Cpt : Fun (Fun(pt, C), C).
apply: (@FunMixin _ _ (fun (f: Fun(pt, C)) => f pt) (fun x y f => f pt) _ _ _)=>//.
move=> x; by apply/reflP.
move=> ?????; by apply/reflP.
Defined.

Local Notation N := (@NatMixin _ _ (Cpt \compf ptC) (idf C) (fun X => id) _).
Local Notation M := (@NatMixin _ _ (idf C) (Cpt \compf ptC) (fun X => id) _).
Lemma test X : (ptC \compf Cpt) X = (idf Fun (pt, C)) X.
case: X => /= mo mm mi pc pe /=.

rewrite /smush.

Lemma pointE : @isomorphisms cats C Fun(pt, C) ptC Cpt.
apply: Isomorphisms => /=.
do !apply: ex_intro.
apply: (@NaturalIsomorphisms _ _ _ _ N M _);
 move=> ? ? ?.
apply: Congruence.etrans; last apply: compm0.
by apply/symP; apply: comp0m.
apply: Congruence.etrans; last apply: compm0.
by apply/symP; apply: comp0m.
by apply: Isomorphisms; apply/symP; apply: compm0.
Check (@NatMixin _ _ (ptC \compf Cpt) (idf Fun (pt, C)) (fun X => id) _).
Local Notation N' := (@NatMixin _ _ (ptC \compf Cpt) (idf Fun (pt, C)) (fun X => id) _).
Local Notation M' := (@NatMixin _ _ (idf C) (Cpt \compf ptC) (fun X => id) _).

  apply (@NaturalIsomorphisms _ _ _ _ N M _) => // ??? /=.

Variable a : Ob C.
Print smush_funType.
Check (sp a pt).
Check ((fun _ : pt => a) : Fun(pt, C)).
Local Notation N' := (@NatMixin _ _ _ _ (fun _ => F \compf G) _).
Local Notation M' := (@NatMixin _ _ _ _ (fun _ => id) _).
Proof.
  do !apply: ex_intro.
  apply: (@Isomorphisms _ _ _ F G _ _) => //.
  move=> x y f z a f' /=.
  apply: Congruence.etrans; last apply: comp0m.
  by apply/symP; apply: compm0.
  move=> x y [] /=.
  by apply/reflP.
  move=> x y z w f g [] /=.
  by apply/reflP.
  by move=> x y z f f' H [].
  move=> ?; by apply/reflP.
  move=> ? ? ? /= f g; by apply/reflP.
  intros.
  
  intros.
  do !apply: ex_intro.
  apply: NaturalIsomorphisms.
  case=> mo mm ii pc pe /=.
  Set Printing All.
  move=> [] /=.
  apply (@NaturalIsomorphisms _ _ _ _ N' M' _) => // ??? /=.
  
  rewrite /=.
  rewrite equivE /=.
  vm_compute.
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _ N' M' _).
  
  apply: NaturalIsomorphisms.
  move=> X.
  apply: Isomorphisms.
  rewrite equivE /=.
  Check (@NatMixin _ _ (F \compf G) (idf _) (fun (X : Ob (Fun(pt, C))) =>
                                               ((F \compf G) X) pt
                                                 X pt
        )).
                                                                             (@Category.id _ _ X)))).
  apply (@NaturalIsomorphisms _ _ _ _ ('(F \compf G) id) _ _).
                              N' M' _)=> // ??? /=.
  move=> ? ? ? f.
  Check ('(F \compf G) id).
          (@Category.id _ _ f)).
  Check F.
  Check G.
  Check (@NatMixin _ _ (F \compf G) (idf _) (fun (X : Ob (Fun(pt, C))) =>  ('(F \compf G) (@Category.id _ _ X)) : Mor ((F \compf G) X, (idf (Fun(pt, C))) X)) _).
  Check N'.
Local Notation N' := 
  Check N'.
  Check N'.
  intros.
  rewrite /=.
  move=> [] /=.
  do !apply: ex_intro.
  apply: Isomorphisms.
  
  apply: comp0m.
  apply: compm0.
  rewrite /=.
  Check (@NaturalTransformation _ _ (G \compf F) (idf _) (fun X => @smush pt C X) _). : Mor ((G \compf F) X, _)) _).
  Check N.
  
Local Notation N := 
  
   by apply: (@NaturalIsomorphisms _ _ _ _ N' M' _).
  
End Point.

Section Product.
Variable C : category.
Variables L R : Ob C.

Definition product C  :=
  limit (@trivial_embeddingn 1 _ [tuple of [:: A; B]]).

End Product.
Definition final_object C :=
  limit (canonical_embedding0 C).
Definition kernel C (A B : Ob C) (f : Mor(A, B)) :=
  limit (canonical_embedding2 f).
Definition initial_object C :=
  limit (canonical_embedding0 (Op C)).
Definition cokernel C (A B : Ob C) (f : Mor(A, B)) :=
  limit (@canonical_embedding2 (Op C) _ _ f).

Section TrivialEmmbedding.
Variable C : category.
Local Definition im_c o := @trivial_embedding1 C o.
Fixpoint tcatn' (choice : seq (Ob C)) :=
  match choice with
  | Cons _ x c => prod_catType (im_c x) (tcatn' c)
  | Nil _ => tcatn 1
  end.
(* Local Notation F := (@Functor tcatn' (tcatn n.+1) ssrfun.id _ _ _ _ : Mor(tcatn', tcatn n.+1)). *)
(* Local Notation G := (@Functor (tcatn n.+1) tcatn' ssrfun.id _ _ _ _ : Mor(tcatn n.+1, tcatn')). *)
(* Local Notation N := (@NaturalTransformation _ _ (G \compf F) (idf tcatn') (fun X => id : Mor ((G \compf F) X, _)) _). *)
(* Local Notation M := (@NaturalTransformation _ _ (idf _) (G \compf F) (fun X => id : Mor (_, (G \compf F) X)) _). *)
(* Local Notation N' := (@NaturalTransformation _ _ (F \compf G) (idf _) (fun X => id : Mor ((F \compf G) X, (idf _) X)) _). *)
(* Local Notation M' := (@NaturalTransformation _ _ (idf _) (F \compf G) (fun X => id : Mor ((idf _) X, (F \compf G) X)) _). *)
Variable n : nat.
About ltnSn.
Variable t s : Ob C.
(* Compute (unlift ) (Ordinal (ltnSn n))). *)

Lemma tcatn'_eq choice : @equiv_op (obs_equivType cats) (tcatn (size choice).+1) (tcatn' choice).
Proof.
  elim: choice; first by apply/reflP.
  move=> a c IH /=.
  move: IH => [[fo fm fi fpc fpe] [[go gm gi gpc gpe] [p q]]].
  set z := (Ordinal (ltn0Sn (size c).+1)).
  case: im_c => /= ? [] /=.
  rewrite /im_c .
  
  Check (fun x =>
           match unlift x z with
           | Some y =>
             (a, fo y) : Ob (prod_catType (im_c a) (tcatn' c))
           | None => _
           end).
                              
             a
             (tcatn' c)
             (@pfst (im_c x) (tcatn' c))
     if x == (size c).+1
     then im_c a
     else fo x).
  Check (@Functor (tcatn (size c).+2) (tcatn' c) _ _ _ _ _).
  Check (@Functor (tcatn' c) (tcatn (size c).+2) _ _ _ _ _).
  case: (tcatn 1) => /= ? [] /=.
Local Notation F := 
  
  do !apply: ex_intro.
  Check (@Functor (tcatn' [::]) (tcatn 1) (fun x => x) (fun _ _ x => x) _ _ _ : Mor(tcatn' _, tcatn _)).
  
  rewrite equivE /=.
  Check (@Functor (tcatn _) (tcatn' _) (nth (thead choice) (behead choice)) _ _ _ _ : Mor(tcatn _, tcatn' _)).
Local Notation G := 
  
  Check G .
  do !apply: ex_intro.
  apply (@Isomorphisms _ _ _ G F) => //=;
  intros; do !apply: ex_intro.
   by apply: (@NaturalIsomorphisms _ _ _ _ N' M' _).
  by apply: (@NaturalIsomorphisms _ _ _ _ N M _).
  apply: ex_intro.


Lemma tcat_eq : @equiv_op (obs_equivType cats) (tcatn (size choice)) tcat'.
Proof.
  do !apply: ex_intro.
  apply: (@Isomorphisms _ _ _ G F) => //=;
  intros; do !apply: ex_intro.
   by apply: (@NaturalIsomorphisms _ _ _ _ N' M' _).
  by apply: (@NaturalIsomorphisms _ _ _ _ N M _).
Qed.

Definition triv_emb (t : tcat_catType') : Ob C :=
  nth default choice t.
Definition triv_emb_mor (s t : Ob tcat_catType') (f : Mor (s, t)) : Mor(triv_emb s, triv_emb t).
  match s, t with
  | _, _ => Category.id
  end.
Proof.
suff ->: s = t by apply id.
by move: f => /eqP.
Defined.

Definition trivial_embedding : Fun (tcat_catType', C).
  refine (@Functor _ _ triv_emb _ _ _ _).
  move=> X.
  apply: comp0m.
  apply: compm0.

Lemma triv_id_id' : @Functor.maps_identity_to_identity _ _ triv_emb _. 
Proof.
  move=> m.
  case: choice => //.
  vm_compute.
  destruct eqP.
  elim.
  elim=> //=.
  move=> m /=.
  rewrite /triv_id.
  destruct introTF.
  apply/reflP.
    by move=> [m i]. Defined.

Lemma triv_pres_equiv' : Functor.preserve_equivalence triv_emb_mor.
Proof.
  move=> A B /= f f'.
  rewrite !equivE => _.
  move/eqP: (f) => H.
  move=> ? ? /eqP.
    by move=> [m i] [m' i'] [f [g p]] [f' [g' p']]. Defined.

Lemma triv_pres_comp : Functor.preserve_composition triv_incl_mor.
Proof. by move=> [m i] [m' i'] [f [g p]] [f' [g' p']]. Defined.



End TrivialEmmbedding.

Notation "0" := initial_object.
Notation "1" := final_object.

Section Types.
Canonical types_equivType A B := map_equivType A (eqe_equivType B).
Definition types_compm
           (A B C : Type)
           (f : types_equivType B C)
           (g : types_equivType A B)
  : types_equivType A C := (fun x => f (g x)).
Definition types_id := (fun (A : Type) => ssrfun.id : types_equivType A A).
Lemma types_associativity : Category.associativity_of_morphisms types_compm.
Proof. move => C D E F h i j; by apply/reflP. Defined.
Lemma types_compm0 : Category.identity_morphism_is_right_identity types_id types_compm.
Proof. move => C D f x; by apply/reflP. Defined.
Lemma types_comp0m : Category.identity_morphism_is_left_identity types_id types_compm.
Proof. move => C D f x; by apply/reflP. Defined.
Lemma types_comp_left : Category.compatibility_left types_compm.
Proof.
move => ? ? ? f f' g ff' x.
move: (ff' x); by rewrite !equivE /= /eqe_op /types_compm => ->.
Defined.
Lemma types_comp_right : Category.compatibility_right types_compm.
Proof. move => ? ? ? f g g' gg' x; apply: gg'. Defined.
Definition types_catMixin :=
CatMixin types_associativity types_compm0 types_comp0m types_comp_left types_comp_right.
Canonical types_catType := Eval hnf in CatType Type types_catMixin.
End Types.
Notation types := types_catType.

Section Hom.
Local Notation "f == g" := (@equiv_op _ f g).
Variables C : category.
Variable prod : product (Op C) C.
Local Definition proj1 := (proj1_sig (- prod) (TrivOb 1 0)).
Local Definition proj2 := (proj1_sig (- prod) (TrivOb 1 1)).
Definition hom_ob (p : Ob (limit_object prod)) := Mor (proj1 p, proj2 p) : Ob types.
Arguments hom_ob /.
Arguments op_mor /.
Definition hom_mor (p q : Ob (limit_object prod)) (f : Mor (p, q)) : Mor (hom_ob p, hom_ob q).
Proof.
  move: f => /= f g.
  Print proj1.
  Check (proj1).
  move: (' proj1 f) => f1.
  Check (@compm _ _ (proj2 p) (proj1 p) (proj1 q) f1 g).
  native_compute.
  Set Printing All.
  Check (' proj1 f).
  move: (' proj1 f) g.
  move=> f1 g.
  Check (@compm _ _ (proj2 p) B (proj1 q) f1 g).
  move: (' proj1 f) => /=.
  set B := (proj1 p).
  move=> f1 g.
  Check (@compm _ _ (proj2 p) (proj1 p) (proj1 q) (' proj1 f) (g : Mor (proj2 p, proj1 p))).
  Set Printing All.
  move: f => /=.
  rewrite /=.
  set
                                                                                             
  Check (g \compm (' proj1 f) ).
  rewrite /op_mor.
         : Mor (proj1 q : Ob C, proj1 p : Ob C)).
  Check (' proj2 f : Mor (proj2 p : Ob C, proj2 q : Ob C)).
  Check (g : Mor (proj1 p: Ob (Op C), proj1 q : Ob (Op C))).
  
  Check (g : Mor (proj2 p: Ob C, proj1 p: Ob C)).
  Check ((g : Mor (proj2 p: Ob C, proj1 p: Ob C)) \compm (' proj1 f)).
  Check ((' proj1 f) \compm (g : Mor (proj2 p: Ob C, proj1 p: Ob C))).
  Check ((' proj2 f) \compm g).
  Check (g \compm (' proj2 f)).
  Check (' proj1 f : Mor (proj1 p : Ob C, proj1 q)).
  Check (g : Mor (proj1 p : Ob (Op C), proj2 p: Ob (Op C))).
  Check (g : Mor (proj1 p : Ob (Op C), proj2 q)).
  Check (Mor (proj2 p : Ob C, proj2 q)).
  proj2 p, proj2 q
  Check compm .
  Set Printing All.
  Check (@compm _ _ (' proj2 f) g).
  Check ((' proj2 f) \compm g).
  Check ((' proj2 f) \compm g).
  Check (' proj2 f).
  Print mo.
  move=> /= g.
  About mo.
  Check (proj1 g).
  move=> h.
  Check (proj1 \compm f).
  Check (proj1_sig (- prod) (TrivOb 1 0)).
  Check (proj1# f).
  Check (proj1# \o #proj1).
  Check (fun g => proj1# g).
  set a := (proj1_sig (- prod) (TrivOb 1 0) p).
  set b := (proj1_sig (- prod) (TrivOb 1 1) p).
  set c := (proj1_sig (- prod) (TrivOb 1 0) q).
  set d := (proj1_sig (- prod) (TrivOb 1 1) q).
  move=> g.
  apply: (fun _ => _).
  Check (proj1_sig (- prod) (TrivOb 1 0) p).
  Check (- prod).
  case: p q f.
  Check (proj1 q).
  Check (fun g => proj1 \compm g \compm proj1).
  proj1 
  ttt
  move: prod p q f => /=.
  rewrite /=.
  rewrite /hom_ob.
  
  Mor((proj1_sig (- prod) (TrivOb 1 0) p), (proj1_sig (- prod) (TrivOb 1 1) p)).
Check (Fun (limit_object prod, types)).
Check (- prod).
Check (proj1_sig (- prod) (TrivOb 1 0)).
Check (proj1_sig (- prod) (TrivOb 1 1)).
           proj1_sig (- prod)
           (CC : limit_object prod) :
  
Goal False.
  case: prod => CC /= CCs CCu CCa.
  move: (proj1_sig CCs) => H.
  move: (H (TrivOb 1 1)) => /=.
  rewrite /triv_incl.
  Check (H (TrivOb 1 1)).
  Check (TrivOb 1 1).
  Print triv_ob'.
  
C * C
D * D
Mor (F
Nat (
Check (product C D).
Variable G : Fun (D, C).

End Hom.
Variables C D : category.

Module Adjunction.
Section Axioms.
Variables C D : category.
Variable F : Fun (C, D).
Variable G : Fun (D, C).
Variable n : forall X Y, Mor (F X, Y) -> Mor (X, G Y).
Local Definition adjunction_axiom X Y :=
  { m : Mor (X, G Y) -> Mor (F X, Y) |
    comp (@n X Y) m = ssrfun.id /\ comp m (@n X Y) = ssrfun.id }.
Arguments adjunction_axiom /.
Lemma injectivity X Y :
  adjunction_axiom X Y ->
  injective (fun g (x : Mor (F X, Y)) => @n X Y (g x))
  /\ injective (fun g x => g (@n X Y x) : Mor (X,G Y)).
Proof.
case=> m [] HL HR. split => x y H'.
 + suff: ssrfun.id \o x = ssrfun.id \o y => //.
   by rewrite -HR; apply (f_equal m# H').
 + suff: x \o ssrfun.id = y \o ssrfun.id => //.
    by rewrite -HL; apply (f_equal (#m) H').
Qed.
End Axioms.
Module Exports.
Structure adjunction C D :=
  Adjunction
    {
      left_adj : _;
      right_adj : _;
      adj_map : _;
      adj_axiom : forall X Y, @adjunction_axiom C D left_adj right_adj adj_map X Y;
    }.
Coercion triple_of_adjunction C D (a : adjunction C D) := (left_adj a, right_adj a, @adj_map C D a).
Variables C D I : category.
Variable a : adjunction C D.
Variable d : Fun(I, C).
Variable limd : limit d.
Variable lima : limit (a.1.1 \compf d).
Arguments compfm /.
Arguments compfo /.
(* Arguments compm /. *)
Lemma adjKL :
  a.1.1 \compf a.1.2 \compf a.1.1 == a.1.1.
Proof.
case: a => F G n aa /=.
set N := @NaturalTransformation _ _ F (F \compf G \compf F) (fun X => 'F (@n X (F X) id)).
set M := @NaturalTransformation _ _ (F \compf G \compf F) F (fun X => (proj1_sig (aa (G (F X)) (F X)) id)).
do !apply: ex_intro.
apply: (@NaturalIsomorphisms _ _ _ _ (M _) (N _)).
move=> X X' f.
case: (aa (G (F X)) (F X)) => fX [] Xl Xr.
case: (aa (G (F X')) (F X')) => fX' [] X'l X'r /=.

have: 'F (@n X' (F X') id) \compm fX' id = 'F (@n _ _ (fX' id)).
case: (aa (G (F X')) (F (G (F X')))) => fX'' [] X''l X''r.

have H: n (G (F X')) (F (G (F X'))) (' F (n X' (F X') id) \compm fX' id) = n (G (F X')) (F (G (F X'))) (' F (n (G (F X')) (F X') (fX' id))).

move: (f_equal (fun e => e 
               ) X'r) => <-.
                                                                  
       (fun _ : Mor (F (G (F X')), F (G (F X'))) => ' F
case: (injectivity (aa (G (F X')) (F (G (F X'))))) => ml mr.
move: (ml (fun _ => ' F (n X' (F X') id) \compm fX' id) (fun _ =>  ' F (n (G (F X')) (F X') (fX' id)))) => ML.
apply: mr.
About injectivity.
case: (aa (G (F X')) (F (G (F X')))) => m /= [] ml mr.
congr ('F).
      hhid.
Check 

Check (aa (G (F X')) (F (G (F X'))
     : Mor (F (G (F X')), F (G (F X')))

move: (f_equal (fun e => e (fX' id)) X'r) => <-.
Check ('G (' F (n X' (F X') id))).
                           (fX' id \compm ' F (' G (' F f)))) X''r) => /=.
Check .
case: (aa (G (F X)) (F X')) => fX'' [] X''l X''r.
have: fX' id \compm ' F (' G (' F f)) = fX'' ('G ('F f)).
move: (f_equal (fun e => 'F (e (' G (' F f)))) X''l) => <- /=.
set A := fX'' (' G (' F f)).
Check (fX' id).
F X', F (G (F X'))
move: (f_equal (fun e => e (fX' id \compm ' F (' G (' F f)))) X''r) => /=.
Check (' F (n (G (F X)) (F X') (fX'' ('G ('F f))))).
                           (fX' id \compm ' F (' G (' F f)))) X''r) => <-.hh
Check (fX'' (' G (' F f))).
congr fX''.

have: n (G (F X)) (F X') (fX' id \compm ' F (' G (' F f))) = ' G (' F f).

move: (f_equal (fun e => e (fX' id \compm ' F (' G (' F f)))) X''r) => <- /=.
(fX' id \compm ' F (' G (' F f)))
                           (' G (' F f))) X''r) => /=.
move: (f_equal (fun e => e ('G ('F f))) X''l) => <- /=.

      @n (G (F X)) (F X') (' F f \compm fX id).
Check (@n (G (F X)) (F X') (fX' id \compm ' F (' G (' F f)))).

Check 
move: (f_equal (fun e => e (fX' id \compm ' F (' G (' F f)))) X''r) => /=.
      ).

     : Mor 
  Check 
Check (fX id \compm ' F (' G (' F id))) == fX id.
apply: Congruence.suff_eq.
Check ('F ('G ('F id))).
Check (fX id).

move: (f_equal (fun e => e id) Xl) => <- /=.

Check (fX (n (G (F X)) (F X) (fX id))).
case: (aa X (F X')) => ?.
         (G (F X)) (F X)) => fX [] Xl Xr.
case: (injectivity (aa (G (F X)) (F X))) => Il Ir.
move: (f_equal (fun e => e (fX' id)) X'r) => <- /=.
apply: Ir.
Check (fX' id \compm ' F (' G (' F f))).
rewrite !/comp.
Check (' F (' G (' F f))).
Check (f_equal _ X'r).
have: n (G (F X')) (F X') (fX' id) = id.
rewrite -X'l.
move: X'l X'r => /=.
move:(equal_f X'r).
rewrite /compm.
rewrite /compfm.
apply: Isomorphisms.
move: (H' X) => /=.
move: (H X) => /=.
move=> X Y f.
case: (aa X (F Y))=> m [] /= mL mR.

Print NaturalTransformation.
                            (fun X => (@Isomorphisms _ _ _  (@n X (F X) id) _ _ _))).
  Check (@NaturalTransformation _ _ F (F \compf G \compf F) (fun X => 'F (@n X (F X) id)) _).
                                                                m(fun X => (@n X (F X) id)) _.
  N
Print ex.
Check(fun X =>
| ex_intro m _ => @Isomorphisms _ _ _ _ (m id)
end).
case:  => m [] mL mR.
Check (NaturalIsomorphisms (fun X => (@Isomorphisms _ _ _  (@n X (F X) id) _ _ _))).
apply (fun @Isomorphisms _ _ _ _ ((fun X => (m id)) X)).
(forall X : C, isomorphisms (N X) (M X))
Print Isomorphism.NaturalIsomorphisms.
About NaturalIsomorphisms .
apply: NaturalIsomorphisms => X.
Check ((fun X => (m id)) X).
move: (m id).
apply: Isomorphisms.
apply: Congruence.suff_eq.
apply: mL.
Check ('F (@n X (F X) id)).
Check ('F (@n X (F X) id)).
apply (@Isomorphisms _ _ _ (fst (_, ('F (@n X (F X) id))))
                     (snd ('F (@n X (F X) id), _))) => /=.
rewrite /=.
move: (fun X => (@n (G X) (F (G X)) id)).
Check ).
                   (G X) (F (G X)) id)).
Check (fun X => (@n (G (F X)) (F X))).
Check (fun X => (@n (G (F X)) (F X) (@Category.id _ _ (G (F X))))).
                   (F X) (G (F X)) id)).
case: (aa X (F X))=> Hf1 Hf2.
case: (aa (G (F X)) (F X)) => Hgf1 Hgf2.
move: (Hgf1 (@n X
         ssrfun.id ssrfun.id).
move: (fun X => 'F (@n (G X) (F (G X)) id)).
Check (fun f => 'G f).
Check 'G.
move: (fun X => 
                            (@n (G X) X f))).
                    (F (G X)) id)).
  move=> X.
  mov
move: (n Ld (F Ld) id).
      pres_limit :
  a.1.1 limd == limit_object lima.
Lemma adj_pres_limit :
  a.1.1 limd == limit_object lima.
Proof.
case: limd => /= Ld cd ud uda.
case: lima => /= La ca ua uaa.
case: a cd ud uda ca ua uaa => F G n aa /= cd ud uda ca ua uaa.
move: uda => /=.
rewrite /Limit.universality_axiom.
have: F Ld 
  Ld = solution_of_diagram
case: (aa Ld (F Ld)) => /= Ha1 Ha2.
Check (G (F Ld)).
move: (Ha1 ssrfun.id (fun _ => id)) => /=.
move: (n Ld (F Ld) id).
rewrite /adjunction_axiom.
move: cd 

Print limit_is_the_unique.
apply: limit_is_the_unique.
Check (limit_object (limit d)).
  
  
End Exports.
End Adjunction.
Export Adjunction.Exports.

(* Example pair (C D : category) : category. *)


(* refine (@Category (Ob C * Ob D) *)
(*                   (fun (A B : Ob C * Ob D) => (Mor (fst A, fst B) * Mor (snd A, snd B))) *)
(*                   (fun A B => (@equivMixin C (fst A) (fst B), @equivMixin D (snd A) (snd B))) *)
(*                   (fun A B C => (@comp C (fst A) (fst B) (fst C), @comp D (snd A) (snd B) (snd C))) *)
(*                   _ _ _ _ _ _). *)
(* intros; by apply: associativity_of_morphisms. *)
(* intros; by apply: identity_morphism_is_right_identity. *)
(* intros; by apply: identity_morphism_is_left_identity. *)
(* intros; by apply: compatibility_left. *)
(* intros; by apply: compatibility_right. *)
(* Defined. *)

(* TODO: write about adjunctions. *)

Canonical funs_equivType.
Canonical obs_equivType.
Canonical nats_equivType.
Local Notation "f == g" := (equiv_op f g).
Variables C D : category.
Set Printing All.
Check (obs_equivType cats).
Check (@equiv_op (obs_equivType cats) C D).
Canonical test := Eval hnf in (obs_equivType (Ob cats)).

Check (equiv_op C D).
Print obs_equivType.


Canonical funs_equivType.
Canonical obs_equivType.
Canonical nats_equivType.
