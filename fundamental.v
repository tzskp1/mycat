From mathcomp Require Import all_ssreflect.
Require Import equivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Module Category.
(* locally small category *)
Section Axioms.
Variable objects : Type.
Variable morphisms : objects -> objects -> Type.
Variable id : forall A, morphisms A A.
Variable comp : forall {A B C}, morphisms B C -> morphisms A B -> morphisms A C.
Variable cat_equivType : forall A B, Equivalence.mixin_of (morphisms A B).
Local Notation "f '\comp' g" := (comp f g) (at level 40).
Local Notation "f == g" := (@equiv_op (EquivType (morphisms _ _) (cat_equivType _ _)) f g).
Definition associativity_of_morphisms :=
  forall D E F G
         (h : morphisms D E)
         (i : morphisms E F)
         (j : morphisms F G),
  (j \comp i) \comp h == j \comp (i \comp h).
Definition identity_morphism_is_right_identity :=
  forall A B (f : morphisms A B), f == f \comp id A.
Definition identity_morphism_is_left_identity :=
  forall A B (f : morphisms A B), f == id B \comp f.
Definition compatibility_left :=
  forall D E F (f f': morphisms D E) (g : morphisms E F),
  f == f' -> g \comp f == g \comp f'.
Definition compatibility_right :=
  forall D E F (f : morphisms D E) (g g' : morphisms E F),
  g == g' -> g \comp f == g' \comp f.
End Axioms.
Structure mixin_of objects :=
  Mixin {
      morphisms : _;
      id: _;
      compm: _;
      equiv: _;
      associativity : @associativity_of_morphisms objects morphisms compm equiv;
      compm0 : @identity_morphism_is_right_identity objects morphisms id compm equiv;
      comp0m : @identity_morphism_is_left_identity objects morphisms id compm equiv;
      comp_left : @compatibility_left objects morphisms compm equiv;
      comp_right : @compatibility_right objects morphisms compm equiv;
    }.

Local Notation class_of := mixin_of (only parsing).

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
Notation category := type.
Notation CatMixin := Mixin.
Notation CatType T m := (@pack T m).
Arguments id objects {m A}.
Notation id := (@Category.id _ (class _) _).
Notation morphisms := morphisms.
Notation compm := compm.
Notation compmA := associativity.
Notation compm0 := compm0.
Definition equiv C := (equiv (class C)).
Notation comp0m := comp0m.
Notation comp_left := comp_left.
Notation comp_right := comp_right.
Arguments compm {objects m A B C} _ _.
Notation "f '\compm' g" := (compm f g) (at level 40).
Notation "'#' f" := (fun g => comp g f) (at level 3).
Notation "f '#'" := (fun g => comp f g) (at level 3).
Notation "'Ob' C" := (sort C) (at level 1).
Notation "'Mor' ( M , N )" := (@morphisms _ (class _) M N) (at level 5).
Notation "[ 'CatMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'CatMixin'  'of'  T ]") : form_scope.
Notation "[ 'category' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'category'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'category' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'category'  'of'  T ]") : form_scope.
End Exports.
End Category.
Export Category.Exports.

Local Notation "f == g" := (@equiv_op (EquivType (morphisms _ _ _) (Category.equiv _ _ _)) f g).

Lemma compm_comp c (A B C : Ob c) : @Congruence.compatible
                                      (EquivType (Mor (_, _)) (Category.equiv _ B C))
                                      (EquivType (Mor (_, _)) (Category.equiv _ A B))
                                      (EquivType (Mor (_, _)) (Category.equiv _ A C))
                                      compm.
Proof.
  move => f g h i H1 H2.
  apply: Equivalence.trans;
    first by apply comp_left, H2.
  by apply comp_right, H1.
Qed.
Notation subst_left := (Congruence.subst_left (@compm_comp _ _ _ _)).
Notation subst_right := (Congruence.subst_right (@compm_comp _ _ _ _)).

Lemma identity_morphism_is_the_unique C (A : Ob C) (id' : Mor (A, A)) :
  (forall B (f : Mor (A, B)), (f \compm id') == f) -> id' == id.
Proof.
move => H.
apply: Congruence.etrans; last by apply H.
apply comp0m.
Qed.

Section TotalEquiv.
Variable C : category.
Structure total :=
  TotalEquiv
    { total_dom : Ob C;
      total_cod : Ob C;
      total_mor :> Mor (total_dom, total_cod) }.
Local Notation td := total_dom.
Local Notation tc := total_cod.
Local Notation tm := total_mor.

Definition total_op (f g : total) :=
  let fA := td f in
  let fB := tc f in
  let fm := tm f in
  let gA := td g in
  let gB := tc g in
  let gm := tm g in
  exists (fgA : fA = gA) (fgB : gB = fB),
    match fgA in (_ = y) return Mor (y, fB) with
    | erefl => fm
    end ==
    match fgB in (_ = y) return Mor (gA, y) with
    | erefl => gm
    end.
Local Arguments total_op f g /.

Lemma total_reflP : Equivalence.reflexivity total_op.
Proof.
  move=> [fA fB f] /=.
  apply: (ex_intro _ (erefl fA)).
  apply: (ex_intro _ (erefl fB)).
  apply: reflP.
Qed.
Lemma total_symP : Equivalence.symmetricity total_op.
Proof.
  move=> [fA fB f] [gA gB g]; split;
  move=> [] /= fgA [] fgB H;
  apply: (ex_intro _ (esym fgA));
  apply: (ex_intro _ (esym fgB));
  move: H; destruct fgA, fgB => /= H;
  by apply/symP.
Qed.
Lemma total_transP : Equivalence.transitivity total_op.
Proof.
  move=> [fA fB f] [gA gB g] [hA hB h] /= [] fgA [] fgB H1 [] ghA [] ghB H2.
  apply: (ex_intro _ (eq_trans fgA ghA)).
  apply: (ex_intro _ (esym (eq_trans (esym fgB) (esym ghB)))).
  destruct fgA, ghA, fgB, ghB => /=.
  by apply/transP; first apply: H1.
Qed.
Definition total_equivMixin := EquivMixin total_symP total_transP total_reflP.
Definition total_equivType (A B E F : Ob C) (_ : Mor(A, B)) (_ : Mor(E, F)) :=
  Eval hnf in EquivType _ total_equivMixin.
End TotalEquiv.

(* Section PartialEquiv. *)
(* Variable C : category. *)
(* Variable cat_eqMixin_ob : Equality.mixin_of (Ob C). *)
(* Variable cat_eqMixin_mor : Equality.mixin_of (total C). *)
(* Variable totalE : *)
(*   forall (A B : Ob C) (f g : Mor(A, B)), *)
(*     @eq_op (EqType _ cat_eqMixin_mor) (TotalEquiv f) (TotalEquiv g) *)
(*     <-> @equiv_op (EquivType _ (Category.equiv _ _ _)) f g. *)
(* Local Notation "f == g" := (@eq_op (EqType _ cat_eqMixin_ob) f g). *)
(* Local Notation td := total_dom. *)
(* Local Notation tc := total_cod. *)
(* Local Notation tm := total_mor. *)

(* Lemma totalE (f : Mor (A, B)) (g : Mor (A, B)) : *)
(*   @equiv_op (total_equivType f g) (TotalEquiv f) (TotalEquiv g) <-> @equiv_op (Mor (A, B)) f g. *)
(* Proof. *)
(* split. *)
(* + case=> fgA [] fgB /=. *)
(*   dependent destruction fgA. *)
(*   by dependent destruction fgB. *)
(* + rewrite !equivE /= => H. *)
(*   apply: (ex_intro _ erefl). *)
(*   by apply: (ex_intro _ erefl). *)
(* Qed. *)
(* End PartialEquiv. *)

Module Functor.
Section Axioms.
Variables domain codomain : category.
Variable map_of_objects : Ob domain -> Ob codomain.
Variable map_of_morphisms : forall A B,
    Mor (A, B) -> Mor (map_of_objects A, map_of_objects B).
Definition maps_identity_to_identity :=
  forall A, @map_of_morphisms A A id == id.
Definition preserve_composition :=
  forall A B C (f : Mor (A, B)) (g : Mor (B, C)),
  map_of_morphisms (g \compm f) == map_of_morphisms g \compm (map_of_morphisms f).
Definition preserve_equivalence :=
  forall A B (f f' : Mor (A, B)),
    f == f' -> map_of_morphisms f == map_of_morphisms f'.
End Axioms.

Structure mixin_of dom cod :=
  Mixin {
      map_of_objects :> _;
      map_of_morphisms : _;
      id_id : @maps_identity_to_identity dom cod map_of_objects map_of_morphisms;
      pres_comp : @preserve_composition dom cod map_of_objects map_of_morphisms;
      pres_equiv : @preserve_equivalence dom cod map_of_objects map_of_morphisms;
    }.

Local Notation class_of := mixin_of (only parsing).

Section ClassDef.
Structure type := Pack {dom; cod; _: class_of dom cod; _ : Type}.
Variables (domT codT : category) (cT : type).
Definition class := let: Pack _ _ c _ := cT return class_of (dom cT) (cod cT) in c.
Definition pack c := @Pack domT codT c (domT -> codT).
Definition clone
           (c : mixin_of domT codT)
           (_ : dom cT -> domT)
           (_ : cod cT -> codT)
           (_ : phant_id (pack c) cT) := pack c.
End ClassDef.

Definition app_fun dom cod (f : mixin_of dom cod) := map_of_objects f.
Definition app_fun_mor dom cod (f : mixin_of dom cod) := map_of_morphisms f.

Module Exports.
Notation "' F" := (@app_fun_mor _ _ F _ _) (at level 1).
Coercion class: type >-> mixin_of.
Coercion app_fun: mixin_of >-> Funclass.
Notation functor := type.
Notation FunMixin := Mixin.
Notation FunType D C m := (@pack D C m).
Notation id_id := id_id.
Notation pres_comp := pres_comp.
Notation pres_equiv := pres_equiv.
Notation "[ 'FunMixin' 'of' T 'to' S ]" := (class _ : mixin_of T S)
  (at level 0, format "[ 'FunMixin'  'of'  T 'to' S ]") : form_scope.
Notation "[ 'functor' 'of' T 'to' S 'for' C ]" := (@clone T S C _ idfun idfun ssrfun.id)
  (at level 0, format "[ 'functor'  'of'  T  'to' S 'for'  C ]") : form_scope.
Notation "[ 'functor' 'of' T 'to' S ]" := (@clone T S _ _ ssrfun.id ssrfun.id ssrfun.id)
  (at level 0, format "[ 'functor'  'of'  T 'to' S ]") : form_scope.
Notation "'Fun' ( C , D )" := (@mixin_of C D).
Section Composition.
Variables (C D E : category) (G : Fun (D, E)) (F : Fun (C, D)).
Definition compfo x := G (F x).
Definition compfm A B (f : Mor (A, B)) := 'G (' F f).
Lemma compf_id_id : @maps_identity_to_identity _ _ compfo compfm.
Proof.
move=> ?.
apply: Congruence.etrans;
 last by apply: id_id.
by apply pres_equiv, id_id.
Defined.
Lemma compf_pres_comp : @preserve_composition _ _ compfo compfm.
Proof.
move=> ? ? ? ? ?.
apply: Congruence.etrans;
 last by apply: pres_comp.
by apply pres_equiv, pres_comp.
Defined.
Lemma compf_pres_equiv : @preserve_equivalence _ _ compfo compfm.
Proof.
move=>? ? ? ? ?;
 by do !apply: pres_equiv.
Defined.
Definition compf :=
  @FunMixin _ _
          compfo
          compfm
          compf_id_id
          compf_pres_comp
          compf_pres_equiv.
End Composition.
Notation "F \compf G" := (compf F G) (at level 40).
Section Identity.
Variables C : category.
Definition idfm (A B : Ob C) (f : Mor (A, B)) := f.
Definition idf_id_id := (fun _  => reflP) : maps_identity_to_identity idfm.
Definition idf_pres_comp := (fun _ _ _ _ _ => reflP) : preserve_composition idfm.
Definition idf_pres_equiv := (fun _ _ _ _ => ssrfun.id) : preserve_equivalence idfm.
Definition idf :=
  @FunMixin _ _ _
          idfm
          idf_id_id
          idf_pres_comp
          idf_pres_equiv.
End Identity.
End Exports.
End Functor.
Export Functor.Exports.

Module NaturalTransformation.
Section Axioms.
Variables C D : category.
Variables F G : Fun (C, D).
Variable map : forall X, Mor (F(X), G(X)).
Arguments map {X}.
Definition naturality_axiom :=
  forall A A' (f : Mor (A, A')), map \compm 'F f == 'G f \compm map.
End Axioms.

Structure mixin_of C D (F G : Fun (C, D)) :=
  Mixin {
      natural_map :> _;
      naturality : @naturality_axiom C D F G natural_map;
    }.

Local Notation class_of := mixin_of (only parsing).

Section ClassDef.
Structure type := Pack {dom; cod; domf; codf; _ : @class_of dom cod domf codf; _ : Type}.
Variables (domT codT : category) (cT : type).
Definition class := let: Pack _ _ _ _ c _ := cT return @class_of (dom cT) (cod cT) (domf cT) (codf cT) in c.
Definition pack c := @Pack _ _ (domf cT) (codf cT) c (dom cT * cod cT).
Definition clone
           (c : @mixin_of _ _ (domf cT) (codf cT))
           (_ : dom cT -> domT)
           (_ : cod cT -> codT)
           (_ : phant_id (pack c) cT) := pack c.
End ClassDef.

Definition app_nat dom cod f g (n : @mixin_of dom cod f g) := natural_map n.

Module Exports.
Notation "'Nat' ( M , N )" := (@mixin_of _ _ M N) (at level 5).
Coercion class: type >-> mixin_of.
Coercion app_nat: mixin_of >-> Funclass.
Notation natural_transformation := type.
Notation NatMixin := Mixin.
Notation NatType D C F G m := (@pack D C F G m).
Notation naturality := naturality.
Notation "[ 'NatMixin' 'of' T 'to' S ]" := (class _ : @mixin_of _ _ T S)
  (at level 0, format "[ 'NatMixin'  'of'  T 'to' S ]") : form_scope.
Section Composition.
Variables C D : category.
Variables F G H : Fun (C, D).
Variables (M : Nat (G, H)) (N : Nat (F, G)).
Definition compn_map X := M X \compm N X.
Lemma compn_naturality : naturality_axiom compn_map.
Proof.
move => ? ? ?.
apply: Congruence.etrans;
 first by apply: compmA.
apply: Congruence.etrans;
  first (apply: subst_right; by apply: (naturality N)).
apply: Congruence.etrans;
 last by apply: compmA.
apply: Congruence.etrans;
  last (apply: subst_left; by apply: (naturality M)).
apply: Congruence.etrans;
 first (apply/symP; by apply: compmA).
by apply/reflP.
Defined.
Definition compn :=
  @NatMixin _ _ _ _ compn_map compn_naturality.
End Composition.
Notation "N \compn M" := (compn N M)  (at level 40).
Section Identity.
Variables C D : category.
Variable F : Fun (C, D).
Definition idn_map X := @Category.id _ (Category.class D) (F X).
Definition idn_map_naturality :=
  (fun (A A' : Ob C) (f : Mor (A, A')) =>
     Congruence.etrans ([eta iffRL symP] (comp0m (' F f))) (compm0 (' F f)))
  : naturality_axiom idn_map.
Definition idn :=
  @NatMixin _ _ _ _ idn_map idn_map_naturality.
End Identity.
Section Composition.
Variables C D E : category.
Variables F G : Fun (C, D).
Variables H : Fun (D, E).
Variables N : Nat (F, G).
Definition compfn_map X := 'H (N X).
Lemma compfn_naturality : @naturality_axiom C E (H \compf F) (H \compf G) compfn_map.
Proof.
move => ? ? ? /=.
apply: Congruence.etrans;
first (apply/symP; by apply pres_comp).
apply/symP.
apply: Congruence.etrans;
first (apply/symP; by apply pres_comp).
apply pres_equiv.
apply/symP; by apply naturality.
Defined.
Definition compfn :=
  @NatMixin C E (H \compf F) (H \compf G) compfn_map compfn_naturality.
End Composition.
Notation "F \compfn N" := (compfn F N)  (at level 40).
Section Composition.
Variables C D E : category.
Variables F G : Fun (D, E).
Variables N : Nat (F, G).
Variables H : Fun (C, D).
Definition compnf_map X := N (H X).
Lemma compnf_naturality : @naturality_axiom C E (F \compf H) (G \compf H) compnf_map.
Proof.
move => ? ? ? /=.
apply: naturality.
Defined.
Definition compnf :=
  @NatMixin C E (F \compf H) (G \compf H) compnf_map compnf_naturality.
End Composition.
Notation "N \compnf F" := (compnf N F)  (at level 40).
End Exports.
End NaturalTransformation.
Export NaturalTransformation.Exports.

Module Isomorphism.
Inductive isomorphisms C (A B: Ob C) (f : Mor (A, B)) (g : Mor (B, A)) : Prop :=
  Isomorphisms : (g \compm f) == id -> (f \compm g) == id -> isomorphisms f g.

Arguments isomorphisms {_ _ _} _ _.
Arguments Isomorphisms {_ _ _} _ _ _ _.

Inductive natural_isomorphisms
          {C D} {F G : Fun (C, D)}
          (N : Nat (F, G)) (M : Nat (G, F)) : Prop :=
  NaturalIsomorphisms :
    (forall (X : Ob C), isomorphisms (N X) (M X)) -> 
    natural_isomorphisms N M.

Section LocalArg.
Variable C : category.
Local Notation iti :=
  (fun (A B : Ob C) =>
     exists (f : Mor (A, B)) g, isomorphisms f g).
Lemma iti_sym :
  Equivalence.symmetricity iti.
Proof.
  move => ? ?.
  split; move=> [N] [M] [H1 H2];
  do !apply: ex_intro;
  by apply (@Isomorphisms _ _ _ M N H2 H1).
Defined.

Lemma iti_refl :
  Equivalence.reflexivity iti.
Proof.
  move => ?; do !apply: ex_intro.
  apply: (@Isomorphisms _ _ _ id id _ _);
  apply/symP => /=;
  by apply comp0m.
Defined.

Lemma iti_trans :
  Equivalence.transitivity iti.
Proof.
  move => ? ? ?.
  move => [f1] [g1] [H11 H12] [f2] [g2] [H21 H22];
  do !apply: ex_intro;
  apply (@Isomorphisms _ _ _ (f2 \compm f1) (g1 \compm g2));
  (apply: Congruence.etrans; first by apply: compmA);
  [ apply: Congruence.etrans; last by apply H11
  | apply: Congruence.etrans; last by apply H22 ];
  apply subst_right;
  (apply/symP; apply: Congruence.etrans; last by apply compmA);
  (apply: Congruence.etrans; first (by apply: comp0m));
  apply subst_left; by apply/symP.
Defined.
End LocalArg.

Section LocalArg.
Variables C D : category.
Local Notation itn :=
  (fun (F G : Fun (C, D)) => 
     exists (N : Nat (F, G)) M, natural_isomorphisms N M).
Lemma itn_sym :
  Equivalence.symmetricity itn.
Proof.
  move => ? ?.
  split; move=> [N] [M] [H];
  do !apply: ex_intro;
  apply: (@NaturalIsomorphisms _ _ _ _ M N) => X;
  by case: (H X).
Defined.

Lemma itn_refl :
  Equivalence.reflexivity itn.
Proof.
  move => X.
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _ (idn X) (idn X)) => x.
  apply: Isomorphisms => /=;
  apply/symP; by apply comp0m.
Defined.

Lemma itn_trans :
  Equivalence.transitivity itn.
Proof.
  move => ? ? ?.
  move => [N1] [M1] [H1] [N2] [M2] [H2];
  do !apply: ex_intro;
  apply (@NaturalIsomorphisms _ _ _ _ (N2 \compn N1) (M1 \compn M2)) => /= X;
  apply: Isomorphisms => /=;
  case: (H1 X) => /= [H11 ?];
  case: (H2 X) => /= [? H22];
  (apply: Congruence.etrans; first by apply: compmA);
  [ apply: Congruence.etrans; last by apply H11
  | apply: Congruence.etrans; last by apply H22 ];
  apply subst_right => /=;
  (apply/symP; apply: Congruence.etrans; last by apply compmA);
  (apply: Congruence.etrans; first (by apply: comp0m));
  apply subst_left; by apply/symP.
Defined.
End LocalArg.

Section LocalArg.
Variables C D : category.
Variables F G : Fun (C, D).
Local Notation eqn :=
  (fun (N : Nat (F, G)) (M : Nat (F, G))
   =>  forall X, N X == M X).
Lemma eqn_sym :
  Equivalence.symmetricity eqn.
Proof.
  move => ? ?.
  split => ? ?; by apply/symP.
Defined.

Lemma eqn_refl :
  Equivalence.reflexivity eqn.
Proof.
  move => ? ?.
  by apply/reflP.
Defined.

Lemma eqn_trans :
  Equivalence.transitivity eqn.
Proof.
  move => ? ? ? H ? ?.
  by (apply/transP; first by apply: H).
Defined.
End LocalArg.

Module Exports.
Notation isomorphisms := isomorphisms.
Notation Isomorphisms := Isomorphisms.
Notation natural_isomorphisms := natural_isomorphisms.
Notation NaturalIsomorphisms := NaturalIsomorphisms.
Definition funs_equivMixin C D := (EquivMixin (@itn_sym C D) (@itn_trans C D) (@itn_refl C D)).
Definition funs_equivType C D := Eval hnf in EquivType (Fun (C, D)) (funs_equivMixin C D).
Definition obs_equivMixin C := (EquivMixin (@iti_sym C) (@iti_trans C) (@iti_refl C)).
Definition obs_equivType C := Eval hnf in EquivType (Ob C) (obs_equivMixin C).
Definition nats_equivMixin C D F G := (EquivMixin (@eqn_sym C D F G) (@eqn_trans C D F G) (@eqn_refl C D F G)).
Definition nats_equivType C D F G := Eval hnf in EquivType (Nat (F, G)) (@nats_equivMixin C D F G).
End Exports.
End Isomorphism.
Export Isomorphism.Exports.

Lemma compf0 C D (f : Fun (C, D)) :
  @equiv_op (funs_equivType C D) f (f \compf (@idf C)).
Proof.
  set L := @NatMixin _ _ f (f \compf idf _) (idn _) (idn_map_naturality _).
  set R := @NatMixin _ _ (f \compf idf _) f (idn _) (idn_map_naturality _).
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _ L R).
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Qed.
  
Lemma comp0f C D (f : Fun (C, D)) :
  @equiv_op (funs_equivType C D) f ((@idf D) \compf f).
Proof.
  set L := @NatMixin _ _ f (idf _ \compf f) (idn _) (idn_map_naturality _).
  set R := @NatMixin _ _ (idf _ \compf f) f (idn _) (idn_map_naturality _).
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _ L R);
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: compm0.
Qed.

Lemma compn0 C D (f g : Fun (C, D)) (n : Nat (f, g)) :
  @equiv_op (nats_equivType f g) n (n \compn (idn f)).
move=> X; by apply: compm0.
Qed.

Lemma comp0n C D (f g : Fun (C, D)) (n : Nat (f, g)) :
  @equiv_op (nats_equivType f g) n ((idn g) \compn n).
move=> X; by apply: comp0m.
Qed.

Section TrivialEquiv.
Variable T : Type.
Lemma trivial_symP : @Equivalence.symmetricity T (fun _ _ => true).
Proof. by []. Qed.
Lemma trivial_transP : @Equivalence.transitivity T (fun _ _ => true).
Proof. by []. Qed.
Lemma trivial_reflP : @Equivalence.reflexivity T (fun _ _ => true).
Proof. by []. Qed.
Definition trivial_equivMixin := EquivMixin trivial_symP trivial_transP trivial_reflP.
End TrivialEquiv.

Module Limit.
Section Axioms.
Variables I C : category.
Variable F : Fun (I, C).
Notation solution_of_diagram L :=
  (sig (fun (s : (forall A, Mor (L, F A))) =>
         forall A B (f : Mor (A, B)), ('F f) \compm (s A) == (s B))).
Definition morphism_of_solutions L L'
      (sL : solution_of_diagram L) (sL' : solution_of_diagram L') :=
    sig (fun l => forall A, (proj1_sig sL' A) == (proj1_sig sL A) \compm l).
Definition universality_axiom L
      (sL : solution_of_diagram L)
      (u : (forall L' (sL' : solution_of_diagram L'), morphism_of_solutions sL sL')) :=
  (forall L' u' (sL' : solution_of_diagram L'),
      (forall A, (proj1_sig sL' A) == (proj1_sig sL A) \compm u') -> proj1_sig (u L' sL') == u').
End Axioms.
Module Exports.
Structure limit I C F :=
  Limit {
      limit_object :> _;
      canonical_solution : _;
      universal_morphism : _;
      universality : @universality_axiom I C F limit_object canonical_solution universal_morphism;
    }.

Notation "- L" := (canonical_solution L).
Local Lemma add_loop I C (F : Fun (I, C)) (limL : limit F) (f : Mor (limL, limL)) :
  let sL := canonical_solution limL in
  (forall (A B : Ob I) (g : Mor (A, B)),
    ('F g) \compm (proj1_sig sL A \compm f) == (proj1_sig sL B \compm f)) ->
    (forall A : Ob I, proj1_sig sL A == proj1_sig sL A \compm f) ->
  f == id.
Proof.
case: limL f => L sL uL pL f /= H H'.
have: proj1_sig (uL L sL) == f.
apply pL, H'.
have: proj1_sig (uL L sL) == id.
apply pL.
move => A.
apply compm0.
move => H1 H2.
apply: Congruence.etrans; last apply: H1.
by apply/symP.
Defined.
  
Lemma limit_is_the_unique I C (F : Fun (I, C)) :
  forall (limL : limit F) (limL' : limit F),
    @equiv_op (obs_equivType C) (limit_object limL) (limit_object limL').
Proof.
move => limL limL' /=.
do !apply: ex_intro.
set u := (@universal_morphism _ _ _ limL' _ (canonical_solution limL)).
set u' := (@universal_morphism _ _ _ limL _ (canonical_solution limL')).
apply (@Isomorphisms _ _ _ (proj1_sig u) (proj1_sig u')).
  apply (@add_loop I C F limL).
  move => A B g /=.
  apply/symP.
  apply: Congruence.etrans; last apply compmA.
  apply subst_left.
  apply/symP.
  apply (proj2_sig (canonical_solution limL)).
 move => A.
 apply: Congruence.etrans; last apply compmA.
 apply: Congruence.etrans; first apply (proj2_sig u A).
 apply subst_left.
 apply: Congruence.etrans; first apply (proj2_sig u' A).
 apply/reflP.
apply (@add_loop I C F limL').
 move => A B g /=.
 apply/symP.
 apply: Congruence.etrans; last apply compmA.
 apply subst_left.
 apply/symP.
 apply (proj2_sig (canonical_solution limL')).
move => A.
apply: Congruence.etrans; last apply compmA.
apply: Congruence.etrans; first apply (proj2_sig u' A).
apply subst_left.
apply: Congruence.etrans; first apply (proj2_sig u A).
apply/reflP.
Defined.
End Exports.
End Limit.
Export Limit.Exports.