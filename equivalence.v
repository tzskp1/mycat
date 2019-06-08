From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Equivalence.

Section Axioms.
Variables (T : Type) (op : rel T).
Definition symmetricity := forall f g, op f g <-> op g f.
Definition transitivity := forall f g h, op f g -> op g h -> op f h.
Definition reflexivity := forall f, op f f.
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
Notation EquivMixin := Mixin.
Notation EquivType T m := (@pack T m).
Notation "[ 'equivMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'equivMixin'  'of'  T ]") : form_scope.
Notation "[ 'equivType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'equivType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'equivType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'equivType'  'of'  T ]") : form_scope.
Hint Resolve sym refl.
End Exports.

End Equivalence.
Export Equivalence.Exports.

Definition equiv_op {T} := Equivalence.op (Equivalence.class T).

Local Notation "f == g" := (equiv_op f g).

Lemma equivE T x : equiv_op x = Equivalence.op (Equivalence.class T) x.
Proof. by []. Qed.

Lemma symP T : Equivalence.symmetricity (@equiv_op T).
Proof. by case: T => ? []. Qed.

Lemma transP T : Equivalence.transitivity (@equiv_op T).
Proof. by case: T => ? []. Qed.

Lemma reflP T : Equivalence.reflexivity (@equiv_op T).
Proof. by case: T => ? []. Qed.

Arguments symP [T f g].
Arguments transP [T f g h].
Arguments reflP [T f].

Prenex Implicits equiv_op symP transP reflP.

Module Congruence.
Section Fundamental.
Variables (e : equivType)
          (lhs rhs : e)
          (eq : lhs == rhs).

Lemma etrans t :
  lhs == t <-> t == rhs.
Proof.
  split => H.
   by apply: Equivalence.trans;
    first by apply Equivalence.sym, H.
  by apply: Equivalence.trans;
   last by apply Equivalence.sym, H.
Qed.
End Fundamental.
(* Section Associativity. *)
(* Variables e1 e12 e2 e23 e3 e13 : equivType. *)
(* Variable F : forall (e1 e2 e3: equivType), e1 -> e2 -> e3. *)
(* Arguments F {e1 e2 e3}. *)
(* Variables (f : e1) (g : e2) (h : e3) (i : e13). *)

(* Definition associativity := *)
(*  (F f (F g h : e23) : e13) == (F (F f g : e12) h : e13). *)

(* Local Axiom assoc : associativity. *)

(* Lemma assoc_lhs : *)
(*   F f (F g h : e23) == i <-> F (F f g : e12) h == i. *)
(* Proof. *)
(*   split => ?. *)
(*    by apply: Equivalence.trans; *)
(*     first by apply Equivalence.sym, assoc. *)
(*   by apply: Equivalence.trans; *)
(*    first by apply assoc. *)
(* Qed. *)

(* Lemma assoc_rhs : *)
(*   i == F f (F g h : e23) <-> i == F (F f g : e12) h. *)
(* Proof. *)
(*   split => ?. *)
(*    by apply: Equivalence.trans; *)
(*     last by apply assoc. *)
(*   by apply: Equivalence.trans; *)
(*    last by apply Equivalence.sym, assoc. *)
(* Qed. *)
(* End Associativity. *)

Section Compatibility.
Variables e1 e2 e3 : equivType.
Variable F : e1 -> e2 -> e3.
Definition compatible := forall f f' g g',
  f == f' -> g == g' -> F f g == F f' g'.
Local Axiom comp_op : compatible.
(* TODO: somthing *)
End Compatibility.
Arguments compatible {e1 e2 e3} _.
End Congruence.

Section EquivEq.
Variable T : eqType.
Lemma eq_symP : @Equivalence.symmetricity T eq_op.
Proof. split; by rewrite eq_sym. Qed.

Lemma eq_transP : @Equivalence.transitivity T eq_op.
Proof. by move=> ? ? ? /eqP -> /eqP ->. Qed.

Lemma eq_reflP : @Equivalence.reflexivity T eq_op.
Proof. by []. Qed.

Definition eq_equivMixin := EquivMixin eq_symP eq_transP eq_reflP.
Definition eq_equivType := EquivType (Equality.sort T) eq_equivMixin.
End EquivEq.
Canonical nat_equivType := Eval compute in eq_equivType nat_eqType.