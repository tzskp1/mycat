From mathcomp Require Import all_ssreflect.
Require Import equivalence fundamental.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* Set Printing Universes. *)

(* Section Map. *)
(* Variable C : category. *)
(* Structure map_ob := *)
(*   MapOb { *)
(*     total_dom : Ob C; *)
(*     total_cod : Ob C; *)
(*     total_mor :> Mor (total_dom, total_cod) *)
(*   }. *)
(* Local Notation td := total_dom. *)
(* Local Notation tc := total_cod. *)
(* Local Notation tm := total_mor. *)
(* Import PartialEquiv. *)
(* Definition map_mor f g := *)
(*   @pairing Mor(td f, td g) Mor(tc f, tc g) *)
(*            (fun d c => c \compm tm f == tm g \compm d). *)

(* Definition mapc_equivMixin f g := *)
(*   let S := @partial_equivType (Ob C) (Category.class C) (td f) (td g) in *)
(*   let T := @partial_equivType (Ob C) (Category.class C) (tc f) (tc g) in *)
(*   @pairing_equivMixin S T. *)

(* Definition map_comp f g h (j : map_mor g h) (i : map_mor f g) : map_mor f h. *)
(*   apply (Pairing (j.1 \compm i.1) (j.2 \compm i.2)). *)
(*   case: i => i1 i2 fg. *)
(*   case: j => j1 j2 gh. *)
(*   apply: Congruence.etrans; first apply: compmA. *)
(*   apply: Congruence.etrans; first (apply: subst_right; apply fg). *)
(*   apply: Congruence.etrans; first (apply/symP; apply: compmA). *)
(*   apply: Congruence.etrans; first (apply: subst_left; apply gh). *)
(*   apply: Congruence.etrans; first apply: compmA. *)
(*   apply/reflP. *)
(* Defined. *)

(* Definition map_id f : map_mor f f. *)
(*   apply (Pairing id id). *)
(*   apply: Congruence.etrans; last apply: compm0. *)
(*   apply/symP; apply: comp0m. *)
(* Defined. *)
(* Lemma map_compmA : @Category.associativity_of_morphisms _ _ map_comp (fun a b => @mapc_equivMixin a b _). *)
(* Proof. *)
(* move => /= f g h i [j1 j2 jH] [k1 k2 kH] [l1 l2 lH]. *)
(* by apply: pair; apply: compmA. *)
(* Defined. *)
(* Lemma map_compm0 : @Category.identity_morphism_is_right_identity _ _ map_id map_comp (fun a b => @mapc_equivMixin a b _). *)
(* Proof. *)
(* move => /= f g h. *)
(* by apply: pair; apply: compm0. *)
(* Defined. *)
(* Lemma map_comp0m : @Category.identity_morphism_is_left_identity _ _ map_id map_comp (fun a b => @mapc_equivMixin a b _). *)
(* Proof. *)
(* move => /= f g h. *)
(* by apply: pair; apply: comp0m. *)
(* Defined. *)
(* Lemma map_comp_left : @Category.compatibility_left _ _ map_comp (fun a b => @mapc_equivMixin a b _). *)
(* Proof. *)
(* move => ? ? ? [f1 f2 Hf] [f'1 f'2 Hf'] [g1 g2 Hg] [ff'1 ff'2]. *)
(* by apply: pair; apply: comp_left. *)
(* Defined. *)
(* Lemma map_comp_right : @Category.compatibility_right _ _ map_comp (fun a b => @mapc_equivMixin a b _). *)
(* Proof. *)
(* move => ? ? ? [f1 f2 Hf] [f'1 f'2 Hf'] [g1 g2 Hg] [ff'1 ff'2]. *)
(* by apply: pair; apply: comp_right. *)
(* Defined. *)
(* Canonical map_catMixin := Eval hnf in CatMixin map_compmA map_compm0 map_comp0m map_comp_left map_comp_right. *)
(* Canonical map_catType := Eval hnf in CatType map_ob map_catMixin. *)
(* End Map. *)
(* Notation Map := map_catType. *)
(* Notation "` f" := (MapOb f : Map _) (at level 1). *)
(* Notation dom := total_dom. *)
(* Notation cod := total_cod. *)


Definition smush C D (A : Ob D) :=
  FunType C D (@FunMixin C D (fun _ : Ob C => A)
                         (fun _ _ _ => id)
                         (fun _ : Ob C => reflP)
                         (fun _ _ _ _ _ => comp0m id)
                         (fun _ _ _ _ _ => reflP)).

Section Point.
Inductive point_ob := pt : point_ob.
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
Canonical point_catMixin :=
  Eval hnf in CatMixin point_associativity point_compm0 point_comp0m point_comp_left point_comp_right.
Canonical point_catType := Eval hnf in CatType _ point_catMixin.
Coercion pto_pt (_ : point_ob) := point_catType.
End Point.

Section Point.
Local Notation "f == g" := (equiv_op f g).
Variable C : category.
Local Definition sp := @smush pt C.
Local Definition Fm : forall x y, Mor (x, y) -> Mor(sp x, sp y).
refine (fun x y (f : Mor(x, y)) => (NatType _ _ (@NatMixin _ _ (sp x) (sp y) _ _ (fun _ => f) _))).
move=> ? ? ? /=.
apply: Congruence.etrans.
apply/symP; apply: compm0.
apply: comp0m.
Defined.
Definition ptC_id_id : Functor.maps_identity_to_identity Fm.
move=> ? ? /=; by apply/reflP.
Defined.
Definition ptC_pres_comp : Functor.preserve_composition Fm.
move=> ? ? ? ? ? ? /=; by apply/reflP.
Defined.
Definition ptC_pres_equiv : Functor.preserve_equivalence Fm.
by move=> ? ? ? ? ? /=.
Defined.
Definition ptC_Mixin := FunMixin ptC_id_id ptC_pres_comp ptC_pres_equiv.
Definition ptC := FunType _ _ ptC_Mixin.
Local Definition Gm : forall (x y : Fun(pt, C)), Nat(x, y) -> morph C (x pt) (y pt).
move=> x y f /=.
apply: (f pt).
Defined.
Definition Cpt_id_id : Functor.maps_identity_to_identity Gm.
move=> ? /=; by apply/reflP.
Defined.
Definition Cpt_pres_comp : Functor.preserve_composition Gm.
move=> ? ? ? ? ? /=; by apply/reflP.
Defined.
Definition Cpt_pres_equiv : Functor.preserve_equivalence Gm.
move=> ? ? [f ? ?] [f' ? ?].
apply.
Defined.
Definition Cpt_Mixin := FunMixin Cpt_id_id Cpt_pres_comp Cpt_pres_equiv.
Definition Cpt := FunType _ _ Cpt_Mixin.
Section SpK.
Variable F : Fun(pt, C).
Definition spF x : Mor(sp (F pt) x, F x) :=
  match x with
  | pt => id
  end.
Definition Fsp x : Mor(F x, (smush pt (F pt)) x) :=
  match x with
  | pt => id
  end.

Lemma spK : F == smush pt (F pt).
 have H1: NaturalTransformation.axiom Fsp.
  move=> [] [] [].
  apply: Congruence.etrans.
  apply/symP; apply: comp0m.
  apply: Congruence.etrans; last apply: compm0.
  by apply: id_id.
 have H2: NaturalTransformation.axiom spF.
  move=> [] [] [] /=.
  apply: Congruence.etrans.
  apply/symP; apply: compm0.
  apply: Congruence.etrans; last apply: compm0.
  apply/symP; apply: id_id.
refine (Pairing
          (NatType _ _ (@NatMixin _ _ F (smush pt (F pt)) _ _ Fsp H1))
          (NatType _ _ (@NatMixin _ _ (smush pt (F pt)) F _ _ spF H2)) _).
constructor; case.
+ apply: Congruence.etrans; last (apply/symP; apply comp0m).
  by apply: compm_comp; apply/reflP.
+ apply: Congruence.etrans; last (apply/symP; apply comp0m).
  by apply: compm_comp; apply/reflP.
Defined.
End SpK.
End Point.

Section Point.
Local Notation "f == g" := (equiv_op f g).
Import PartialEquiv.
Lemma pointE C : Fun(pt, C) == C.
apply (Pairing (down C \compf Cpt C)
               (ptC C \compf up C)).
apply: Isomorphisms.
 set Ho :=
 (fun (A : Fun (pt, C)) =>
    eq_rect_r (fun p : C => sp p == A) ([eta symP] (spK A)) (Down.down_up (A pt))
    : ((ptC C \compf up C) \compf (down C \compf Cpt C)) A == idf _ A).
 apply (funaltE Ho); subst Ho.
 case: C => ? []; intros; case => /=.
 apply: Congruence.etrans; first (apply/symP; apply compm0).
 apply: Congruence.etrans; first (apply/symP; apply comp0m).
 apply/reflP.
set Ho := 
(fun A => eq_rect_r (equiv_op^~ A) reflP (Down.up_down A))
: forall A, ((down C \compf Cpt C) \compf (ptC C \compf up C)) A == (idf _) A.
apply (funaltE Ho); subst Ho.
move=> X Y f.
apply: Congruence.etrans; last first.
apply/symP; apply comp0m.
apply: Congruence.etrans; last first.
apply/symP; apply compm0.
have: (id \compm '(idf _) f) \compm id == (id \compm '(idf _) f) \compm id by apply/reflP.
by case: C X Y f => ? [?????????????].
Defined.
End Point.

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
Canonical catn_catMixin := (CatMixin catn_associativity catn_compm0 catn_comp0m catn_comp_left catn_comp_right).
Canonical catn_catType := Eval hnf in CatType (ordinal n) catn_catMixin.
End Ordinal.
Notation catn := catn_catType.
Example cat0 : category := catn 0.
Example cat1 : category := catn 1.
Example cat2 : category := catn 2.
Example cat4 : category := catn 4.
Notation square := cat4.

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
  move: s t f => [m i] [m' i'] [f [g p]].
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

Definition trivial_inclusion_Mixin := FunMixin triv_id_id triv_pres_comp triv_pres_equiv.
Definition trivial_inclusion := FunType _ _ trivial_inclusion_Mixin.
End TrivialEmmbedding.

Local Notation "f == g" := (equiv_op f g).

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

Canonical FC_catMixin := CatMixin FC_associativity FC_compm0 FC_comp0m FC_comp_left FC_comp_right.
Canonical FC_catType := Eval hnf in CatType FC FC_catMixin.
End Pushout.
Notation pushout := FC_catType.

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

Canonical op_catMixin := CatMixin op_associativity op_compm0 op_comp0m op_comp_left op_comp_right.
Canonical op_catType := Eval hnf in CatType (Ob C) op_catMixin.
End Opposite.
Notation opposite_category := op_catType.
Notation "'Op' C" := (opposite_category C) (at level 1).

Section Opposite.
Variable C : Ob cats.
Local Notation "f == g" := (equiv_op f g).
Local Notation F := (FunType _ _ (@FunMixin (Op (Op C)) C _ (fun x y f => f) (fun _ => reflP) (fun _ _ _ _ _ => reflP) (fun _ _ _ _ => ssrfun.id)) : Mor(Op (Op C), C)).
Local Notation G := (FunType _ _ (@FunMixin C (Op (Op C)) _ (fun x y f => f) (fun _ => reflP) (fun _ _ _ _ _ => reflP) (fun _ _ _ _ => ssrfun.id)) : Mor(C, Op (Op C))).
Local Lemma HoFG : forall A, (F \compf G) A == idf _ A.
Proof. move=> X. apply/reflP. Defined.

Local Lemma HoGF : forall A, (G \compf F) A == idf _ A.
Proof. move=> X. apply/reflP. Defined.

Lemma dualK : Op (Op C) == C.
apply: (Pairing F G _); constructor; [apply (funaltE HoGF) | apply (funaltE HoFG) ] => X Y f;
(apply: Congruence.etrans; first (apply/symP; apply: compm0));
(apply: Congruence.etrans; first (apply/symP; apply: comp0m));
apply/reflP.
Defined.
End Opposite.
Section Opposite.
Variables C D : category.
Variable F : Fun(C, D).
Definition op_fun : Fun(Op C, Op D).
apply: (FunType _ _ (@FunMixin (Op C) (Op D) F (fun x y f => 'F f) _ _ _)).
by move=> ?; apply: id_id.
by move=> ? ? ? ? ?; apply: pres_comp.
by move=> ? ? ? ? ?; apply: pres_equiv.
Defined.
End Opposite.

Notation "''Op' F" := (op_fun F) (at level 1).

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
refine (FunType _ _ (@FunMixin _ _ embedding0_ob embedding0_mor _ _ _))
        => //; case => //.
Defined.
End CanonicalEmmbedding0.

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
refine (FunType _ _ (@FunMixin _ _ (embedding2_ob A B)
                 (@embedding2_mor A B f)
                 _ _ _)) => //.
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
Canonical prod_catMixin := (CatMixin prod_associativity prod_compm0 prod_comp0m prod_comp_left prod_comp_right).
Canonical prod_catType := Eval hnf in CatType (Ob C * Ob D) prod_catMixin.
Definition pfst : Fun(prod_catType, C).
  apply: (FunType _ _ (@FunMixin prod_catType C fst (fun _ _ => fst) _ _ _)).
+ move=> ?; by apply/reflP.
+ move=> ? ? ? ? ?; by apply/reflP.
+ by move=> ? ? [??] [??] [??].
Defined.

Definition psnd : Fun(prod_catType, D).
  apply: (FunType _ _ (@FunMixin prod_catType D snd (fun _ _ => snd) _ _ _)).
+ move=> ?; by apply/reflP.
+ move=> ? ? ? ? ?; by apply/reflP.
+ by move=> ? ? [??] [??] [??].
Defined.
End Product.
Notation "a * b" := (prod_catType a b).
Arguments pfst / {_ _}.
Arguments psnd / {_ _}.

Definition final_object C :=
  limit (canonical_embedding0 C).
Definition kernel C (A B : Ob C) (f : Mor(A, B)) :=
  limit (canonical_embedding2 f).
Definition initial_object C :=
  limit (canonical_embedding0 (Op C)).
Definition cokernel C (A B : Ob C) (f : Mor(A, B)) :=
  limit (@canonical_embedding2 (Op C) _ _ f).

Notation "0" := initial_object.
Notation "1" := final_object.

Section Types.
Definition types_equivMixin A B := map_equivMixin A (eqe_equivMixin B).
Definition types_compm (A B C : Type) (f : B -> C) (g : A -> B) : A -> C := (fun x => f (g x)).
Definition types_id := (fun (A : Type) => ssrfun.id : A -> A).
Lemma types_associativity : Category.associativity_of_morphisms types_compm types_equivMixin.
Proof. move => C D E F h i j; by apply/reflP. Defined.
Lemma types_compm0 : Category.identity_morphism_is_right_identity types_id types_compm types_equivMixin.
Proof. move => C D f x; by apply/reflP. Defined.
Lemma types_comp0m : Category.identity_morphism_is_left_identity types_id types_compm types_equivMixin.
Proof. move => C D f x; by apply/reflP. Defined.
Lemma types_comp_left : Category.compatibility_left types_compm types_equivMixin.
Proof.
move => ? ? ? f f' g ff' x.
move: (ff' x); by rewrite !equivE /= /eqe_op /types_compm => ->.
Defined.
Lemma types_comp_right : Category.compatibility_right types_compm types_equivMixin.
Proof. move => ? ? ? f g g' gg' x; apply: gg'. Defined.
Definition types_catMixin :=
CatMixin types_associativity types_compm0 types_comp0m types_comp_left types_comp_right .
Canonical types_catType := Eval hnf in CatType Type types_catMixin.
End Types.
Notation types := types_catType.

(* Section Curry. *)
(* Local Notation "f == g" := (equiv_op f g). *)
(* Variable C D E : category. *)
(* Section CurryOb. *)
(* Variable x : Fun(C * D, E). *)
(* Section CurryObOb. *)
(* Variable c : Ob C. *)
(* Definition curry_obob : Fun (D, E). *)
(* set F := (fun d1 d2 (f : Mor(d1, d2)) *)
(*           => 'x ((id, f) : Mor((c, d1), (c, d2)))). *)
(* apply: (@FunMixin _ _ _ F _ _ _). *)
(* move=> ?; apply: id_id. *)
(* move=> ? ? ? f g. *)
(* apply: Congruence.etrans; last apply: pres_comp. *)
(* apply: pres_equiv. *)
(* apply: Congruence.subst_left. *)
(* by move=> ? ? ? ? H1 H2; split. *)
(* apply: compm0. *)
(* move=> ? ? ? ? H. *)
(* apply: pres_equiv. *)
(* by split => //; apply/reflP. *)
(* Defined. *)
(* End CurryObOb. *)
(* Section CurryObMor. *)
(* Definition curry_obmor c1 c2 (f : Mor(c1, c2)) : Nat(curry_obob c1, curry_obob c2). *)
(* set N := (fun d => 'x ((f, id) : Mor((c1, d), (c2, d))) *)
(*                    : Mor (curry_obob c1 d, curry_obob c2 d)). *)
(* apply (@NatMixin _ _ _ _ N). *)
(* move=> ? ? g. *)
(* apply: Congruence.etrans => /=. *)
(* apply/symP; apply pres_comp. *)
(* apply: Congruence.etrans; last apply pres_comp. *)
(* apply: pres_equiv; split. *)
(*  apply: Congruence.etrans; last apply: comp0m. *)
(*  apply/symP; apply: compm0. *)
(* apply: Congruence.etrans; last apply: compm0. *)
(* apply/symP; apply: comp0m. *)
(* Defined. *)
(* End CurryObMor. *)
(* Definition curry_ob : Fun(C, Fun (D, E)). *)
(* apply (@FunMixin _ _ curry_obob curry_obmor). *)
(* + move=> ? ?; by apply: Congruence.etrans; first apply: id_id; apply/reflP. *)
(* + move=> ? ? ? ? ? ?. *)
(*   apply: Congruence.etrans; last apply: pres_comp. *)
(*   apply: pres_equiv; split; first by apply/reflP. *)
(*   by apply: Congruence.etrans; last apply: compm0; apply/reflP. *)
(* + move=> ? ? ? ? ? ?. *)
(*   by apply: pres_equiv; split; last by apply/reflP. *)
(* Defined. *)
(* End CurryOb. *)
(* Section CurryMor. *)
(* Variables x y : Fun(C * D, E). *)
(* Variable f : Mor(x, y). *)
(* Section CurryMorMor. *)
(* Variable c : Ob C. *)
(* Definition curry_mormor : Nat((curry_ob x) c, (curry_ob y) c). *)
(* apply (@NatMixin _ _ _ _ (fun d => f (c, d) : Mor(curry_ob x c d, curry_ob y c d))). *)
(* by move=> ? ? ? /=; apply: naturality. *)
(* Defined. *)
(* End CurryMorMor. *)
(* Definition curry_mor : Nat(curry_ob x, curry_ob y). *)
(* apply (@NatMixin _ _ (curry_ob x) (curry_ob y) curry_mormor). *)
(* by move=> ? ? ? ? /=; apply: naturality. *)
(* Defined. *)
(* End CurryMor. *)
(* Definition curry : Fun(Fun(C * D, E), Fun(C, Fun (D, E))). *)
(* apply (@FunMixin _ _ curry_ob curry_mor). *)
(* by move=> ? ? ?; apply/reflP. *)
(* by move=> ? ? ? ? ? ? ?; apply/reflP. *)
(* move=> ? ? ? ? H c d; exact (H (c, d)). *)
(* Defined. *)

(* Section UnCurryOb. *)
(* Variable x : Fun(C, Fun(D, E)). *)
(* Definition uncurry_obob cd : Ob E := x cd.1 cd.2. *)
(* Definition uncurry_obmor cd1 cd2 (f : Mor(cd1, cd2)) := ('(x cd2.1) f.2) \compm (('x f.1) cd1.2). *)
(* Definition uncurry_ob : Fun(C * D, E). *)
(* apply (@FunMixin _ _ uncurry_obob uncurry_obmor). *)
(* + move=> [] a b. *)
(*   apply: Congruence.etrans; last (apply/symP; apply: compm0). *)
(*   apply: compm_comp; first by apply id_id. *)
(*   have: ('x id) == id by move=> ?; apply id_id. apply. *)
(* + move=> [??] [??] [??] [f1 f2] [g1 g2]. *)
(*   apply: Congruence.etrans; last first. *)
(*   apply: compm_comp; apply naturality. *)
(*   apply: Congruence.etrans; last (apply/symP; apply: compmA). *)
(*   apply: Congruence.etrans; last first. *)
(*   apply: subst_right. *)
(*   apply: compmA. *)
(*   apply: Congruence.etrans; last first. *)
(*   apply: subst_right. *)
(*   apply: subst_left. *)
(*   apply: naturality. *)
(*   apply: Congruence.etrans; last first. *)
(*   apply: subst_right. *)
(*   apply/symP; apply: compmA. *)
(*   apply: Congruence.etrans; last apply: compmA. *)
(*   apply: Congruence.etrans. *)
(*   apply/symP; apply: naturality. *)
(*   apply: compm_comp; last first. *)
(*   apply: pres_comp. *)
(*   have : (' x (g1 \compm f1) == (' x g1) \compn (' x f1)) *)
(*    by (apply: Congruence.etrans; last apply: pres_comp); apply/reflP. *)
(*   apply. *)
(* + move=> [??] [??] [f ?] [g ?] [??]. *)
(*   apply: compm_comp; first by apply: pres_equiv. *)
(*   have : 'x f == 'x g by apply pres_equiv. *)
(*   apply. *)
(* Defined. *)
(* End UnCurryOb. *)
(* Section UnCurryMor. *)
(* Variables x y : Fun(C, Fun(D, E)). *)
(* Variable f : Mor(x, y). *)
(* Definition uncurry_mormor cd : Mor(uncurry_ob x cd, uncurry_ob y cd) := f cd.1 cd.2. *)
(* Definition uncurry_mor : Nat(uncurry_ob x, uncurry_ob y). *)
(* apply (@NatMixin _ _ (uncurry_ob x) (uncurry_ob y) uncurry_mormor). *)
(* move=> [??] [??] [g h]. *)
(* apply: Congruence.etrans; first (apply/symP; apply: compmA). *)
(* apply: Congruence.etrans; first (apply: subst_left; apply: naturality). *)
(* apply: Congruence.etrans; last (apply: subst_left; apply: naturality). *)
(* apply: Congruence.etrans; last (apply: subst_left; apply/symP; apply: naturality). *)
(* apply: Congruence.etrans; first apply: compmA. *)
(* apply: Congruence.etrans; last (apply/symP; apply: compmA). *)
(* apply: subst_right. *)
(* have: f _ \compm 'x g == 'y g \compm f _ by apply naturality. *)
(* apply. *)
(* Defined. *)
(* End UnCurryMor. *)
(* Definition uncurry : Fun(Fun(C, Fun (D, E)), Fun(C * D, E)). *)
(* apply (@FunMixin _ _ uncurry_ob uncurry_mor). *)
(* + move=> ? ?; apply/reflP. *)
(* + move=> ? ? ? ? ? ?; apply/reflP. *)
(* + move=> ? ? ? ? H c; exact (H c.1 c.2). *)
(* Defined. *)
(* End Curry. *)

(* Lemma curryK C D E :@isomorphisms cats _ _ (curry C D E) (uncurry C D E). *)

(* Section Hom. *)
(* Variables C : category. *)
(* Definition hom_ob (p : Ob ((Op C) * C)) := Mor(pfst p, psnd p) : Ob types. *)
(* Definition hom_mor (p q : Ob (C * (Op C))) (f : Mor (p, q)) : Mor (hom_ob p, hom_ob q) *)
(*   := fun g => ('pfst f) \compm g \compm ('psnd f). *)
(* Axiom hom_id_id : Functor.maps_identity_to_identity hom_mor. *)
(* Axiom hom_pres_comp : Functor.preserve_composition hom_mor. *)
(* Axiom hom_pres_equiv : Functor.preserve_equivalence hom_mor. *)
(* Definition hom := FunMixin hom_id_id hom_pres_comp hom_pres_equiv. *)
(* Canonical hom_funType := Eval hnf in FunType _ _ hom. *)
(* End Hom. *)
