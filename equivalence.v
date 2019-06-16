From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Module Equivalence.

Section Axioms.
Variables (T : Type) (op : T -> T -> Prop).
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

Arguments equiv_op {T} x : simpl never.
Arguments symP [T f g].
Arguments transP [T f g h].
Arguments reflP [T f].

Prenex Implicits equiv_op symP transP reflP.

Module Congruence.
Lemma etrans (e : equivType) (x y z : e) : x == y -> y == z -> x == z.
Proof. by move=> ?; apply/transP. Defined.
Lemma suff_eq (e : equivType) (x y : e) : x = y -> x == y.
Proof. move=> ->; by apply/reflP. Defined.
Section Compatibility.
Variables e1 e2 e3 : equivType.
Variable F : e1 -> e2 -> e3.
Definition compatible := forall f f' g g',
  f == f' -> g == g' -> F f g == F f' g'.
Variable comp_op : compatible.
Lemma subst_left f f' g :
  f == f' -> F f g == F f' g.
Proof.
  move => ?; apply: comp_op => //; apply reflP.
Qed. 
Lemma subst_right f g g' :
  g == g' -> F f g == F f g'.
Proof.
  move => ?; apply: comp_op => //; apply reflP.
Qed. 
(* TODO: somthing *)
End Compatibility.
Arguments compatible {e1 e2 e3} _.
Arguments etrans {e x y z} _ _.
Arguments subst_right {e1 e2 e3 F} comp_op {_ _ _}.
Arguments subst_left {e1 e2 e3 F} comp_op {_ _ _}.
End Congruence.

Section EqType.
Variable T : eqType.
Lemma eq_symP : @Equivalence.symmetricity T eq_op.
Proof. split; by rewrite eq_sym. Qed.
Lemma eq_transP : @Equivalence.transitivity T eq_op.
Proof. by move=> ? ? ? /eqP -> /eqP ->. Qed.
Lemma eq_reflP : @Equivalence.reflexivity T eq_op.
Proof. by []. Qed.
Definition eq_equivMixin := EquivMixin eq_symP eq_transP eq_reflP.
Canonical eq_equivType := Eval hnf in EquivType (Equality.sort T) eq_equivMixin.
End EqType.

Section Prop'.
Lemma prop_symP : @Equivalence.symmetricity Prop iff.
Proof. move => ??; split; by move => ->. Qed.
Lemma prop_transP : @Equivalence.transitivity Prop iff.
Proof. move=> ? ? ? [] ? ? [] ? ?. split; by auto. Qed.
Lemma prop_reflP : @Equivalence.reflexivity Prop iff.
Proof. by []. Qed.
Canonical prop_equivMixin := EquivMixin prop_symP prop_transP prop_reflP.
Canonical prop_equivType := Eval hnf in EquivType Prop prop_equivMixin.
End Prop'.

Section Map.
Variable d v : Type.
Variable equiv : Equivalence.mixin_of v.
Local Notation "f == g" := (@equiv_op (EquivType _ equiv) f g).
Definition map_op (f : d -> v) (g : d -> v) :=
  forall z, f z == g z.
Lemma map_symP : Equivalence.symmetricity map_op.
Proof. move=> f g; split => /= H z; apply/symP; by apply: H. Qed.
Lemma map_transP : Equivalence.transitivity map_op.
Proof.
move=> ? ? ? H1 H2 z.
apply/transP; first by apply H1.
apply: H2; apply/reflP.
Qed.
Lemma map_reflP : Equivalence.reflexivity map_op.
Proof. move=> f x; apply/reflP. Qed.
Definition map_equivMixin := EquivMixin map_symP map_transP map_reflP.
Canonical map_equivType := Eval hnf in EquivType (d -> v) map_equivMixin.
End Map.

Section eq.
Variable T : Type.
Definition eqe_op := @eq T.
Lemma eqe_symP : Equivalence.symmetricity eqe_op.
Proof. move=> f g; split => H; by apply: esym. Qed.
Lemma eqe_transP : Equivalence.transitivity eqe_op.
Proof. move=> ? ? ? H1 H2. by apply: etrans; first apply H1. Qed.
Lemma eqe_reflP : Equivalence.reflexivity eqe_op.
Proof. move=> f; by apply erefl. Qed.
Definition eqe_equivMixin := EquivMixin eqe_symP eqe_transP eqe_reflP.
Definition eqe_equivType := Eval hnf in EquivType T eqe_equivMixin.
End eq.

Section PullBack.
Variable d v : Type.
Variable equiv : Equivalence.mixin_of v.
Variable map : d -> v.
Local Notation "f == g" := (@equiv_op (EquivType _ equiv) f g).
Definition pull_op (f : d) (g : d) := map f == map g.
Lemma pull_symP : Equivalence.symmetricity pull_op.
Proof. move=> f g; split => /= H; apply/symP; by apply: H. Qed.
Lemma pull_transP : Equivalence.transitivity pull_op.
Proof.
move=> ? ? ? H1 H2.
apply/transP; first by apply H1.
apply: H2; apply/reflP.
Qed.
Lemma pull_reflP : Equivalence.reflexivity pull_op.
Proof. move=> f; apply/reflP. Qed.
Definition pull_equivMixin := EquivMixin pull_symP pull_transP pull_reflP.
Canonical pull_equivType := Eval hnf in EquivType d pull_equivMixin.
End PullBack.
