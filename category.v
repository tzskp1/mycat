From mathcomp Require Import all_ssreflect.
Require Import equivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing Universes. *)
Set Universe Polymorphism.

Module Category.
(* locally small category *)
Section Axioms.
Variable objects : Type.
Variable morphisms : objects -> objects -> equivType.
Variable id : forall A, morphisms A A.
Variable comp : forall {A B C}, morphisms B C -> morphisms A B -> morphisms A C.
Local Notation "f '\comp' g" := (comp f g) (at level 40).
Local Notation "f == g" := (@equiv_op (morphisms _ _) f g).
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
End Axioms.
Structure mixin_of objects :=
  Mixin {
      morphisms : _;
      id: _;
      compm: _;
      associativity : @associativity_of_morphisms objects morphisms compm;
      compm0 : @identity_morphism_is_right_identity objects morphisms id compm;
      comp0m : @identity_morphism_is_left_identity objects morphisms id compm;
      comp_left : @compatibility_left objects morphisms compm;
      comp_right : @compatibility_right objects morphisms compm;
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
Arguments id {objects m A}.
Notation id := (@Category.id _ (class _) _).
Notation morphisms := morphisms.
Notation compm := compm.
Notation compmA := associativity.
Notation compm0 := compm0.
Notation comp0m := comp0m.
Notation comp_left := comp_left.
Notation comp_right := comp_right.
Arguments compm {objects m A B C} _ _.
Notation "f '\compm' g" := (compm f g) (at level 40).
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

Local Notation "f == g" := (@equiv_op _ f g).

Lemma compm_comp c (A B C : Ob c) : @Congruence.compatible
                                      (Mor (B, C))
                                      (Mor (A, B))
                                      (Mor (A, C))
                                     compm.
Proof.
  move => f g h i H1 H2.
  apply: Equivalence.trans;
    first by apply comp_left, H2.
  by apply comp_right, H1.
Qed.
Local Notation subst_left := (Congruence.subst_left (@compm_comp _ _ _ _)).
Local Notation subst_right := (Congruence.subst_right (@compm_comp _ _ _ _)).

Lemma identity_morphism_is_the_unique C (A : Ob C) (id' : Mor (A, A)) :
  (forall {B : Ob C} (f : Mor (A, B)), (f \compm id') == f) -> id' == id.
Proof.
move => H.
apply: Congruence.etrans; last by apply H.
apply comp0m.
Qed.

Module Functor.
Section Axioms.
Variables domain codomain : category.
Variable map_of_objects : Ob domain -> Ob codomain.
Variable map_of_morphisms : forall A B,
    Mor (A, B) -> Mor (map_of_objects A, map_of_objects B).
Local Definition maps_identity_to_identity :=
  forall A, @map_of_morphisms A A id == id.
Local Definition preserve_composition :=
  forall A B C (f : Mor (A, B)) (g : Mor (B, C)),
  map_of_morphisms (g \compm f) == map_of_morphisms g \compm (map_of_morphisms f).
Local Definition preserve_equivalence :=
  forall A B (f f' : Mor (A, B)),
    f == f' -> map_of_morphisms f == map_of_morphisms f'.
End Axioms.
Module Exports.
Structure functor dom cod :=
  Functor {
      map_of_objects : Ob dom -> Ob cod;
      map_of_morphisms : forall A B,
          Mor (A, B) -> Mor (map_of_objects A, map_of_objects B);
      id_id : @maps_identity_to_identity dom cod map_of_objects map_of_morphisms;
      pres_comp : @preserve_composition dom cod map_of_objects map_of_morphisms;
      pres_equiv : @preserve_equivalence dom cod map_of_objects map_of_morphisms;
    }.
Coercion map_of_objects : functor >-> Funclass.
Notation "'Fun' ( C , D )" := (functor C D).
Notation "' F " := (@map_of_morphisms _ _ F _ _) (at level 1).
Section Composition.
Variables (C D E : category) (G : Fun (D, E)) (F : Fun (C, D)).
Definition compfo x := G (F x).
Definition compfm A B (f : Mor (A, B)) := 'G ('F f).
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
Definition composition_of_functors :=
  @Functor _ _
          compfo
          compfm
          compf_id_id
          compf_pres_comp
          compf_pres_equiv.
End Composition.
Notation "F \compf G" := (composition_of_functors F G) (at level 40).
Section Identity.
Variables C : category.
Definition idfm (A B : Ob C) (f : Mor (A, B)) := f.
Definition idf_id_id := (fun _  => reflP) : maps_identity_to_identity idfm.
Definition idf_pres_comp := (fun _ _ _ _ _ => reflP) : preserve_composition idfm.
Definition idf_pres_equiv := (fun _ _ _ _ => ssrfun.id) : preserve_equivalence idfm.
Definition identity_of_functor :=
  @Functor _ _ _
          idfm
          idf_id_id
          idf_pres_comp
          idf_pres_equiv.
End Identity.
Notation idf := identity_of_functor.
End Exports.
End Functor.
Export Functor.Exports.

Module NaturalTransformation.
Section Axioms.
Variables C D : category.
Variables F G : Fun (C, D).
Variable map : forall X, Mor (F(X), G(X)).
Arguments map {X}.
Local Definition naturality_axiom :=
  forall A A' (f : Mor (A, A')), map \compm 'F f == 'G f \compm map.
End Axioms.
Module Exports.
Structure natural_transformation {C D} (F G : Fun (C, D)) :=
  NaturalTransformation {
      natural_map :> _;
      naturality : @naturality_axiom C D F G natural_map;
    }.
Notation "'Nat' ( M , N )" := (natural_transformation M N) (at level 5).
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
Definition composition_of_natural_transformations :=
  @NaturalTransformation _ _ _ _ compn_map compn_naturality.
End Composition.
Notation "N \compn M" := (composition_of_natural_transformations N M)  (at level 40).
Section Identity.
Variables C D : category.
Variable F : Fun (C, D).
Definition idn_map X := @Category.id _ (Category.class D) (F X).
Definition idn_map_naturality :=
  (fun (A A' : Ob C) (f : Mor (A, A')) =>
     Congruence.etrans ([eta iffRL symP] (comp0m (' F f))) (compm0 (' F f)))
  : naturality_axiom idn_map.
Definition identity_natural_transformation :=
  @NaturalTransformation _ _ _ _ idn_map idn_map_naturality.
End Identity.
Notation idn := identity_natural_transformation.
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
Definition composition_of_natural_transformation_functor :=
  @NaturalTransformation C E (H \compf F) (H \compf G) compfn_map compfn_naturality.
End Composition.
Notation "F \compfn N" := (composition_of_natural_transformation_functor F N)  (at level 40).
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
Definition composition_of_functor_natural_transformation :=
  @NaturalTransformation C E (F \compf H) (G \compf H) compnf_map compnf_naturality.
End Composition.
Notation "N \compnf F" := (composition_of_functor_natural_transformation N F)  (at level 40).
End Exports.
End NaturalTransformation.
Export NaturalTransformation.Exports.

Module Isomorphism.
Inductive isomorphisms {C} {A B: Ob C} (f : Mor (A, B)) (g : Mor (B, A)) : Prop :=
  Isomorphisms : (g \compm f) == id -> (f \compm g) == id -> isomorphisms f g.

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
     exists (f : Mor (A, B)) (g : Mor (B, A)), isomorphisms f g).
Lemma iti_sym :
  Equivalence.symmetricity iti.
Proof.
  move => ? ?.
  split; move=> [N [M [H1 H2]]];
  do !apply: ex_intro;
  by (apply Isomorphisms; first by apply: H2).
Defined.

Lemma iti_refl :
  Equivalence.reflexivity iti.
Proof.
  move => ?; do !apply: ex_intro.
  apply Isomorphisms;
  apply/symP;
  by apply compm0.
Defined.

Lemma iti_trans :
  Equivalence.transitivity iti.
Proof.
  move => ? ? ?.
  move => [f1 [g1 [H11 H12]]] [f2 [g2 [H21 H22]]];
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

Notation iti_equivMixin C := (EquivMixin (@iti_sym C) (@iti_trans C) (@iti_refl C)).

Lemma ni_sym C D (F G : Fun (C, D)) (N : Nat (F, G)) (M : Nat (G, F)) :
  natural_isomorphisms N M <-> natural_isomorphisms M N.
Proof.
  split; case => H;
  apply: NaturalIsomorphisms => X;
  by case: (H X).
Defined.

Lemma ni_refl C D (F : Fun (C, D)) :
  natural_isomorphisms (@idn _ _ F) (@idn _ _ F).
Proof.
  apply: NaturalIsomorphisms => X.
  apply: Isomorphisms => /=;
  apply/symP; by apply comp0m.
Defined.

Lemma ni_trans C D (F G H : Fun (C, D))
      (N1 : Nat (F, G)) (M1 : Nat (G, F))
      (N2 : Nat (G, H)) (M2 : Nat (H, G)) :
  natural_isomorphisms N1 M1
  -> natural_isomorphisms N2 M2
  -> natural_isomorphisms (N2 \compn N1) (M1 \compn M2).
Proof.
  move=> [H1] [H2].
  apply: NaturalIsomorphisms => X.
  apply: Isomorphisms => /=;
  [ case: (H1 X) => HX _;
    case: (H2 X) => ? _
  | case: (H1 X) => _ ?;
    case: (H2 X) => _ HX ];
  (apply: Congruence.etrans;
   first (by apply: compmA));
  (apply/symP; apply: Congruence.etrans;
    first (by apply/symP; apply HX));
  apply: subst_right;
  (apply: Congruence.etrans; last (by apply: compmA));
  (apply: Congruence.etrans; first (by apply: comp0m));
  apply: subst_left; by apply/symP.
Defined.

Section LocalArg.
Variables C D : category.
Local Notation itn :=
  (fun (F G : Fun (C, D)) => 
     exists (N : Nat (F, G)) (M : Nat (G, F)), natural_isomorphisms N M).
Lemma itn_sym :
  Equivalence.symmetricity itn.
Proof.
  move => ? ?.
  split; move=> [N [M H]];
  do !apply: ex_intro;
  rewrite ni_sym; by apply: H.
Defined.

Lemma itn_refl :
  Equivalence.reflexivity itn.
Proof.
  move => ?.
  do !apply: ex_intro.
  exact: ni_refl.
Defined.

Lemma itn_trans :
  Equivalence.transitivity itn.
Proof.
  move => ? ? ?.
  move => [N1 [M1 H1]] [N2 [M2 H2]].
  do !apply: ex_intro.
  apply ni_trans; first (by apply H1);
  by apply H2.
Defined.
End LocalArg.

Notation itn_equivMixin C D := (EquivMixin (@itn_sym C D) (@itn_trans C D) (@itn_refl C D)).

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

Notation eqn_equivMixin C D F G := (EquivMixin (@eqn_sym C D F G) (@eqn_trans C D F G) (@eqn_refl C D F G)).

Module Exports.
Notation isomorphisms := isomorphisms.
Notation Isomorphisms := Isomorphisms.
Notation natural_isomorphisms := natural_isomorphisms.
Notation NaturalIsomorphisms := NaturalIsomorphisms.
Canonical funs_equivType C D := Eval hnf in EquivType (Fun (C, D)) (itn_equivMixin C D).
Canonical obs_equivType C := Eval hnf in EquivType (Ob C) (iti_equivMixin C).
Canonical nats_equivType C D F G := Eval hnf in EquivType (Nat (F, G)) (eqn_equivMixin C D F G).
End Exports.
End Isomorphism.
Export Isomorphism.Exports.

Section CategoryOfCategories.
Lemma cats_associativity : @Category.associativity_of_morphisms category _ composition_of_functors.
Proof.
  move => /= C D E F h i j.
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ ((j \compf i) \compf h) (j \compf (i \compf h)) (natural_map (idn _)) (idn_map_naturality _))
                              (@NaturalTransformation _ _ (j \compf (i \compf h)) ((j \compf i) \compf h) (natural_map (idn _)) (idn_map_naturality _))).
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Defined.

Lemma cats_compm0 : @Category.identity_morphism_is_right_identity category _ idf composition_of_functors.
Proof.
  move => /= C D f.
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ f (f \compf idf _) (natural_map (idn _)) (idn_map_naturality _))
                              (@NaturalTransformation _ _ (f \compf idf _) f (natural_map (idn _)) (idn_map_naturality _))).
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Defined.

Lemma cats_comp0m : @Category.identity_morphism_is_left_identity category _ idf composition_of_functors.
Proof.
  move => /= C D f.
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ f (idf _ \compf f) (natural_map (idn _)) (idn_map_naturality _))
                              (@NaturalTransformation _ _ (idf _ \compf f) f (natural_map (idn _)) (idn_map_naturality _))).
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: compm0.
Defined.

Lemma cats_comp_left : @Category.compatibility_left category _ composition_of_functors.
Proof.
  move => ? ? ? f f' g /= [] N [] M [H].
  do !apply: ex_intro.
  refine (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ (g \compf f) (g \compf f')
                                                      (natural_map (g \compfn N)) (compfn_naturality _ _))
                              (@NaturalTransformation _ _ (g \compf f') (g \compf f) 
                                                      (natural_map (g \compfn M)) (compfn_naturality _ _)) _) => X.
  apply: Isomorphisms => /=;
  (apply: Congruence.etrans;
   first by (apply/symP; apply pres_comp));
  (apply: Congruence.etrans;last by apply id_id);
  apply: pres_equiv; by case: (H X).
Defined.

Lemma cats_comp_right : @Category.compatibility_right category _ composition_of_functors.
Proof.
  move => ? ? ? f g g' /= [] N [] M [H].
  do !apply: ex_intro.
  refine (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ (g \compf f) (g' \compf f)
                                                      (natural_map (N \compnf f)) (compnf_naturality _ _))
                              (@NaturalTransformation _ _ (g' \compf f) (g \compf f)
                                                      (natural_map (M \compnf f)) (compnf_naturality _ _)) _) => X.
  apply: Isomorphisms => /=;
  by case: (H (f X)).
Defined.

Notation cats_catMixin := (CatMixin cats_associativity cats_compm0 cats_comp0m cats_comp_left cats_comp_right).
Canonical cats_catType := Eval hnf in CatType category cats_catMixin.
End CategoryOfCategories.
Notation cats := cats_catType.

Section Pushout.
Variables C D : category.
Variable F : Fun (C, D).
Notation FC := { B | exists A, F A = B }.
Definition compF (A B C : FC) := 
  @compm _ (Category.class D) (proj1_sig A) (proj1_sig B) (proj1_sig C).

Lemma FC_associativity : @Category.associativity_of_morphisms FC _ compF.
Proof.
  move => [??] [??] [??] [??] /= h i j.
  apply compmA.
Defined.

Lemma FC_compm0 : @Category.identity_morphism_is_right_identity FC _ (fun A => @Category.id _ _ (proj1_sig A)) compF.
Proof.
  move => [??] [??] /= f.
  apply compm0.
Defined.

Lemma FC_comp0m : @Category.identity_morphism_is_left_identity FC _ (fun A => @Category.id _ _ (proj1_sig A)) compF.
Proof.
  move => [??] [??] /= f.
  apply comp0m.
Defined.

Lemma FC_comp_left : @Category.compatibility_left FC _ compF.
Proof.
  move => [??] [??] [??] /= f f' g.
  apply comp_left.
Defined.

Lemma FC_comp_right : @Category.compatibility_right FC _ compF.
Proof.
  move => [??] [??] [??] /= f g g'.
  apply comp_right.
Defined.

Notation FC_catMixin := (CatMixin FC_associativity FC_compm0 FC_comp0m FC_comp_left FC_comp_right).
Canonical FC_catType := Eval hnf in CatType FC FC_catMixin.
End Pushout.
Notation pushout := FC_catType.

Section Opposite.
Variable C : category.
Definition compo (A B C' : Ob C) (g : Mor (C', B)) (f : Mor (B, A)) := compm f g.
Definition mo (B A : Ob C) := Mor (A, B).

Lemma op_associativity : @Category.associativity_of_morphisms _ mo compo.
Proof.
  move => ? ? ? ? h i j.
  apply/symP; by apply: compmA.
Defined.

Lemma op_compm0 : @Category.identity_morphism_is_right_identity _ mo (fun A => @Category.id _ _ A) compo.
Proof.
  move => ? ? /= f.
  by apply comp0m.
Defined.

Lemma op_comp0m : @Category.identity_morphism_is_left_identity _ mo (fun A => @Category.id _ _ A) compo.
Proof.
  move => ? ? /= f.
  by apply compm0.
Defined.

Lemma op_comp_left : @Category.compatibility_left _ mo compo.
Proof.
  move => ? ? ? /= f f' g.
  by apply comp_right.
Defined.

Lemma op_comp_right : @Category.compatibility_right _ mo compo.
Proof.
  move => ? ? ? /= f f' g.
  by apply comp_left.
Defined.

Notation op_catMixin := (CatMixin op_associativity op_compm0 op_comp0m op_comp_left op_comp_right).
Canonical op_catType := Eval hnf in CatType (Ob C) op_catMixin.
End Opposite.
Notation opposite_category := op_catType.
Notation "'Op' C" := (opposite_category C) (at level 1).

Section CategoryOfFunctors.
Variable C D : category.
Lemma funs_associativity : Category.associativity_of_morphisms (@composition_of_natural_transformations C D).
Proof.
  move => C' D' E F h i j X /=.
  apply compmA.
Defined.

Lemma funs_compm0 : Category.identity_morphism_is_right_identity (@idn C D) (@composition_of_natural_transformations C D).
Proof.
  move => C' D' f X.
  apply compm0.
Defined.

Lemma funs_comp0m : Category.identity_morphism_is_left_identity (@idn C D) (@composition_of_natural_transformations C D).
Proof.
  move => C' D' f X.
  apply comp0m.
Defined.

Lemma funs_comp_left : Category.compatibility_left (@composition_of_natural_transformations C D).
Proof.
  move => ? ? ? f f' g /= H X.
  apply comp_left.
  move: f f' H => [f ?] [f' ?] /= H.
  apply H.
Defined.

Lemma funs_comp_right : Category.compatibility_right (@composition_of_natural_transformations C D).
Proof.
  move => ? ? ? f f' g /= H X.
  apply comp_right.
  move: f f' H => [f ?] [f' ?] /= H.
  apply H.
Defined.

End CategoryOfFunctors.
Notation funs_catMixin C D := (CatMixin (@funs_associativity C D) (@funs_compm0 C D) (@funs_comp0m C D) (@funs_comp_left C D) (@funs_comp_right C D)).
Canonical funs_catType C D := Eval hnf in CatType Fun (C, D) (funs_catMixin C D).
Notation funs := funs_catType.

Notation "'Fun' ( C , D )" := (funs C D).

Module Limit.
Section Axioms.
Variables I C : category.
Variable F : Fun (I, C).
Local Notation solution_of_diagram L :=
  (sig (fun (s : (forall A, Mor (L, F A))) =>
         forall A B (f : Mor (A, B)), ('F f) \compm (s A) == (s B))).
Local Definition morphism_of_solutions L L'
      (sL : solution_of_diagram L) (sL' : solution_of_diagram L') :=
    sig (fun l => forall A, (proj1_sig sL' A) == (proj1_sig sL A) \compm l).
Local Definition universality_axiom L
      (sL : solution_of_diagram L)
      (u : (forall L' (sL' : solution_of_diagram L'), morphism_of_solutions sL sL')) :=
  (forall L' u' (sL' : solution_of_diagram L'),
      (forall A, (proj1_sig sL' A) == (proj1_sig sL A) \compm u') -> proj1_sig (u L' sL') == u').
End Axioms.
Module Exports.
Structure limit I C F L :=
  Pack {
      canonical_solution : _;
      universal_morphism : _;
      universality : @universality_axiom I C F L canonical_solution universal_morphism;
    }.

Local Lemma add_loop I C (F : Fun (I, C)) (L : Ob C) (limL : limit F L) (f : Mor (L, L)) :
  let sL := canonical_solution limL in
  (forall (A B : Ob I) (g : Mor (A, B)),
    ('F g) \compm (proj1_sig sL A \compm f) == (proj1_sig sL B \compm f)) ->
    (forall A : Ob I, proj1_sig sL A == proj1_sig sL A \compm f) ->
  f == id.
Proof.
case: limL => sL uL pL /= H H'.
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
  
Lemma limit_is_the_unique I C (F : Fun (I, C)) (L L' : Ob C) :
 forall (limL : limit F L) (limL' : limit F L'), L == L'.
Proof.
move => limL limL' /=.
do !apply: ex_intro.
set u := (@universal_morphism _ _ _ _ limL' _ (canonical_solution limL)).
set u' := (@universal_morphism _ _ _ _ limL _ (canonical_solution limL')).
apply (@Isomorphisms _ _ _ (proj1_sig u) (proj1_sig u')).
  apply (@add_loop I C F L limL).
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
apply (@add_loop I C F L' limL').
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

Section Ordinal.
Variable n : nat.
(* 0 --> 1 *)
(* |     | *)
(* >     > *)
(* 2 --> 3 *)
Definition catnm (x y : ordinal n) :=
  match x, y with
  | Ordinal i _, Ordinal j _ =>
    i <= j
  end.
Section TrivialEquiv.
Variable x y : ordinal n.
Lemma catnm_symP : @Equivalence.symmetricity (catnm x y) (fun _ _ => true).
Proof. by []. Qed.
Lemma catnm_transP : @Equivalence.transitivity (catnm x y) (fun _ _ => true).
Proof. by []. Qed.
Lemma catnm_reflP : @Equivalence.reflexivity (catnm x y) (fun _ _ => true).
Proof. by []. Qed.
Definition catnm_equivMixin := EquivMixin catnm_symP catnm_transP catnm_reflP.
Canonical catnm_equivType := EquivType (catnm x y) catnm_equivMixin.
End TrivialEquiv.

Definition catnc
           (x y z : ordinal n)
           (g : catnm y z)
           (f : catnm x y) : catnm x z.
case: x y z f g => [x Hx] [y Hy] [z Hz] /=.
exact: leq_trans.
Defined.

Definition catn_id (x : ordinal n) : catnm x x.
case: x => [x Hx] /=.
exact: leqnn.
Defined.

Lemma catn_associativity : Category.associativity_of_morphisms catnc.
Proof. by []. Defined.

Lemma catn_compm0 : Category.identity_morphism_is_right_identity catn_id catnc.
Proof. by []. Defined.

Lemma catn_comp0m : Category.identity_morphism_is_left_identity catn_id catnc.
Proof. by []. Defined.

Lemma catn_comp_left : Category.compatibility_left catnc.
Proof. by []. Defined.

Lemma catn_comp_right : Category.compatibility_right catnc.
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

Definition canonical_embedding1 C (A : Ob C) :=
  {|
    map_of_objects := fun _ : cat1 => A;
    map_of_morphisms := fun _ _ _ => id;
    id_id := fun _ : cat1 => reflP;
    pres_comp := fun _ _ _ _ _ => comp0m id;
    pres_equiv := fun _ _ _ _ _ => reflP
  |}.
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
refine (@Functor _ _ embedding0_ob embedding0_mor _ _ _)
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
refine (@Functor _ _ (embedding2_ob A B)
                 (@embedding2_mor A B f)
                 _ _ _) => //.
case => m Hm; do !case:m Hm => [|m] Hm //=; by apply/reflP.
case => [m Hm] [n Hn] [p Hp] h i;
do !case:m Hm h => [|m] Hm h //=;
do !case:n Hn i h => [|n] Hn i h //=;
do !case:p Hp i h => [|p] Hp i h //=;
(try by apply compm0); by apply comp0m.
case => [m Hm] [n Hn] h i H.
do !case:m Hm i h H => [|m] Hm i h H //=;
do !case:n Hn i h H => [|n] Hn i h H //=;
by apply/reflP.
Defined.
End CanonicalEmmbedding2.

Definition final_object C L := limit (canonical_embedding0 C) L.
Definition kernel C (A B : Ob C) (f : Mor(A, B)) L := limit (canonical_embedding2 f) L.
Definition initinal_object C L := limit (canonical_embedding0 (Op C)) L.
Definition cokernel C (A B : Ob C) (f : Mor(A, B)) L :=
  limit (@canonical_embedding2 (Op C) _ _ f) L.

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

(* Inductive adjunction {C D : category} (F : Fun (C, D)) (G : Fun (D, C)) (f : Nat (F, G)) : Type := *)
(*   Adjunction : forall (A : Ob C) *)
(*                       (B : Ob D) *)
(*                       (f : Hom (A , G(B)) -> Hom (F(A), B)), *)
(*     injective f -> *)
(*     surjective f -> adjunction  *)
    
(* TODO: write about adjunctions. *)