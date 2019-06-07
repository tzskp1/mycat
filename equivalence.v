From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Axioms.
Variables (T : Type) (op : T -> T -> Prop).
Definition symmetricity := forall (f g : T), op f g <-> op g f.
Definition transitivity := forall (f g h : T), op f g -> op g h -> op f h.
Definition reflexivity := forall (f : T), op f f.
End Axioms.

Structure mixin_of T :=
  Mixin { op : _;
          sym : @symmetricity T op;
          trans : @transitivity T op;
          refl : @reflexivity T op;
        }.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation equivType := type.
Notation equivMixin := Mixin.
Notation EquivType T m := (@pack T m).
Notation "[ 'equivMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'equivMixin'  'of'  T ]") : form_scope.
Notation "[ 'equivType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'equivType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'equivType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'equivType'  'of'  T ]") : form_scope.
End Exports.
Export Exports.

Definition equiv_op T := op (class T).

Variables (equiv : equivType)
          (F : equiv -> equiv -> equiv).
Local Notation "f == g" := (equiv_op f g).

Lemma equivE T x : equiv_op x = op (class T) x.
Proof. by []. Qed.

Prenex Implicits equiv_op.

Delimit Scope equiv_scope with EQUIV.
Open Scope equiv_scope.

Local Axiom comp_op : forall f f' g g',
    f == f' -> g == g' -> F f g == F f' g'.
Local Axiom assoc : forall f g h,
  F f (F g h) == F (F f g) h.
Lemma assoc_left f g h i :
  F f (F g h) == i <-> F (F f g) h == i.
Proof.
  split => ?.
   by apply: trans;
    first by apply sym, assoc.
  by apply: trans;
   first by apply assoc.
Qed.

Lemma assoc_right f g h i :
  i == F f (F g h) <-> i == F (F f g) h.
Proof.
  split => ?.
   by apply: trans;
     last by apply assoc.
  by apply: trans;
    last by apply sym, assoc.
Qed.

Definition eqTypeMixin (T : eqType) : mixin_of T.
  refine (@Mixin T
         eq_op
         _
         (fun (f g h : T) (V : f == g) => eq_ind_r (fun x : T => g == h -> x == h) (fun x : g == h => x) (elimTF eqP V))
         (@eqxx T)).
  intros; by rewrite eq_sym.
Defined.

Definition trivialMixin T : mixin_of T :=
  @Mixin _ (fun _ _ => true) (fun _ _ => conj id id) (fun _ _ _ _ x => x) (fun _ => eqxx true).
Definition falseMixin : mixin_of false := trivialMixin false.
Definition unitMixin : mixin_of unit := trivialMixin unit.
Definition trueMixin : mixin_of true := trivialMixin true.
Definition eq_and {x y} {z w} (H:@eq _ x y) (H':@eq _ z w) :=
  match H in @eq _ _ a return @eq _ (x && z) (a && w) with
  | @Logic.eq_refl =>
    match H' in @eq _ _ b return @eq _ (x && z) (x && b) with
    | @Logic.eq_refl => @Logic.eq_refl _ (x && z)
    end
  end.
Definition prodMixin s e (Ms : mixin_of s) (Me : mixin_of e) : mixin_of (s * e).
refine (@Mixin (s * e)
               (fun s' e' : s * e =>
                  let (s1, e1) := s' in
                  let (s2, e2) := e' in
                  op Ms s1 s2 /\ op Me e1 e2)
               _ _ _).
case => [s1 e1] [s2 e2].
by move: (symmetricity Ms s1 s2) (symmetricity Me e1 e2) => -> ->.
case => [s1 e1] [s2 e2] [s3 e3].
case => Hs12 He12.
case => Hs23 He23.
split.
apply (@transitivity _ Ms _ _ _ Hs12 Hs23).
apply (@transitivity _ Me _ _ _ He12 He23).
case => [s1 e1].
split;
  first exact: reflexivity Ms s1.
exact: reflexivity Me e1.
Defined.
Definition natMixin s : mixin_of (ordinal s).
refine (@Mixin _
               (fun a b =>
                  match a, b with
                  | Ordinal a' _, Ordinal b' _ => a' == b'
                  end)
               _ _ _) => //=.
case => [? ?] [? ?].
rewrite eq_sym //.
case => [? ?] [? ?] [? ?].
move/eqP => -> //.
case => [? ?] //.
Defined.
End Equivalence.

(* locally small category *)
Module Axioms.
Section Equiv.
 Import Equivalence.
 Variable objects : Type.
 Variable morphisms : objects -> objects -> Type.
 Variable id : forall (A : objects), morphisms A A.
 Variable comp : forall {A B C : objects}, morphisms B C -> morphisms A B -> morphisms A C.
 Variable cmp: forall (A B : objects), mixin_of (morphisms A B).
 Local Notation "f '\comp' g" := (comp f g) (at level 40).
 Local Notation "f == g" := (op (cmp _ _) f g).
 Local Definition associativity_of_morphisms :=
   forall D E F G
          (h : morphisms D E)
          (i : morphisms E F)
          (j : morphisms F G),
   (j \comp i) \comp h == j \comp (i \comp h).
 Local Definition identity_morphism_is_right_identity :=
   forall A B (f : morphisms A B), f == f \comp id A.
 Local Definition identity_morphism_is_left_identity :=
   forall A B (f : morphisms A B), f == id B \comp f.
 Local Definition compatibility_left :=
   forall D E F (f f': morphisms D E) (g : morphisms E F),
   f == f' -> g \comp f == g \comp f'.
 Local Definition compatibility_right :=
   forall D E F (f : morphisms D E) (g g' : morphisms E F),
   g == g' -> g \comp f == g' \comp f.
End Equiv.
Module Exports.
Polymorphic Structure category :=
  Pack {
      objects : _;
      morphisms : _;
      equiv: _;
      id: _;
      comp: _;
      associativity : @associativity_of_morphisms objects morphisms comp equiv;
      right_idem : @identity_morphism_is_right_identity objects morphisms id comp equiv;
      left_idem : @identity_morphism_is_left_identity objects morphisms id comp equiv;
      comp_left : @compatibility_left objects morphisms comp equiv;
      comp_right : @compatibility_right objects morphisms comp equiv;
    }.
Hint Constructors category.
Notation "f '\comp' g" := (comp f g) (at level 40).
Notation "f == g" := (Equivalence.op (equiv _ _) f g).
Notation "'Ob' C" := (objects C) (at level 1).
Notation "'Mor' ( M , N )" := (morphisms M N) (at level 5).
Arguments id [c A].

Structure functor (domain codomain : category) :=
  Functor {
      map_of_objects :> Ob domain -> Ob codomain;
      map_of_morphisms : forall (A B : Ob domain), Mor (A, B) -> Mor (map_of_objects A, map_of_objects B);
      _ : forall (A : Ob domain),
          (@map_of_morphisms A A id) == id;
      _ : forall (A B C : Ob domain) (f : Mor (A, B)) (g : Mor (B, C)),
          (map_of_morphisms (g \comp f)) == (map_of_morphisms g \comp (map_of_morphisms f));
      _ : forall (A B : Ob domain) (f f' : Mor (A, B)),
          f == f' ->
          (map_of_morphisms f) == (map_of_morphisms f');
    }.
Notation "'Fun' ( C , D )" := (functor C D).
Notation "' F " := (map_of_morphisms F) (at level 1).
End Exports.
End Axioms.
Export Axioms.Exports.

Inductive isomorphisms {C : category} {A B : Ob C} (f : Mor (A, B)) (g : Mor (B, A)) : Prop :=
  Isomorphisms : (g \comp f) == id -> (f \comp g) == id -> isomorphisms f g.

Hint Resolve (proj1 (Equivalence.symmetricity _ _ _)) Equivalence.reflexivity.
Hint Constructors category.
(* Polymorphic Hint Constructors category. *)

Lemma comp0m C (D E : Ob C) (f : Mor (D, E)) : f == id \comp f.
Proof. by apply left_idem. Qed.

Lemma compm0 C (D E : Ob C) (f : Mor (D, E)) : f == f \comp id.
Proof. by apply Equivalence.symmetricity, identity_morphism_is_right_identity. Qed.


Lemma subst_right_up_to_equals {C : category} (D E F : Ob C) (f f' : Mor (D, E)) (g : Mor (E, F)) (h : Mor (D, F)) :
  f == f' -> (h == g \comp f) <-> (h == g \comp f').
Proof.
move => H1.
have : (g \comp f) == (g \comp f') by rewrite /equals; apply: compatibility_left.
rewrite /equals => H3.
split => H2;
 (apply: Equivalence.transitivity;
   first by apply: H2);
 by auto.
Qed.

Lemma subst_left_up_to_equals {C : category} (D E F : Ob C) (f : Mor (D, E)) (g g' : Mor (E, F)) (h : Mor (D, F)) :
  g == g' -> (h == g \comp f) <-> (h == g' \comp f).
Proof.
move => H1.
have : (g \comp f) == (g' \comp f) by rewrite /equals; apply: compatibility_right; auto.
rewrite /equals => H3.
split => H2;
 (apply: Equivalence.transitivity;
   first by apply: H2);
 by auto.
Qed.

(* Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2. *)

Lemma congr_up_to_equals
      {C : category}
      (D E F G : Ob C)
      (f : Mor (D, E))
      (f' : Mor (D, F))
      (g : Mor (E, G))
      (g' : Mor (F, G))
      (h : Mor (E, F)) (i : Mor (F, E)) (I : isomorphisms h i) :
  h \comp f == f' ->
  g == g' \comp h ->
  g \comp f == g' \comp f'.
Proof.
  move => H1 H2.
  case: I => lid rid.
  have: g' \comp (h \comp f) == g' \comp f'.
  rewrite subst_right_up_to_equals; last first.
  apply Equivalence.symmetricity.
  apply: H1.
  exact: Equivalence.reflexivity.
  apply: 
  auto.
  info_auto.
  eauto.
  
  
  g \comp 
  Check (g' \comp h \comp i \comp f').
  have (g' \comp (h \comp f)) == g' \comp h \comp i \comp f'.
  have : g \comp i \comp h \comp f == g' \comp h \comp i \comp f'.
  apply transitivity_lhs.
  rewrite -comp0m.
  About identity_morphism_is_right_identity.
  rewrite -identity_morphism_is_right_identity.
  rewrite subst_right_up_to_equals; last first.
  apply Equivalence.symmetricity.
  apply H1.
  rewrite subst_left_up_to_equals; last first.
  apply Equivalence.symmetricity; apply H2.
  by apply: Equivalence.reflexivity.
Qed.
