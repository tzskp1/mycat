From mathcomp Require Import all_ssreflect.
Require Import equivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Set Printing Universes.

Local Notation "f == g" := (equiv_op f g).

Inductive pairing@{m p} (S T : Type@{m}) (P : S -> T -> Type@{p}) : Type@{p} :=
  Pairing : forall f g, P f g -> pairing P.
Arguments pairing {_ _} _.
Arguments Pairing {_ _ _} _ _.
Notation "p '.1'" := match p with
                     | Pairing f _ _ => f
                     end.
Notation "p '.2'" := match p with
                     | Pairing _ f _ => f
                     end.
Notation "'#' f" := (fun g => comp g f) (at level 3).
Notation "f '#'" := (fun g => comp f g) (at level 3).

Module Category.
Section Axioms.
Universe u.
Variable objects : Type@{u}.
Variable morphisms : objects -> objects -> Type@{u}.
Variable id : forall A, morphisms A A.
Variable comp : forall A B C,
    morphisms B C -> morphisms A B -> morphisms A C.
Variable cat_equivMixin: forall A B, Equivalence.mixin_of (morphisms A B).
Local Notation "f '\comp' g" := (comp f g) (at level 40).
Local Notation "f == g" := (@equiv_op@{u} (EquivType@{u} _ (cat_equivMixin _ _)) f g).

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

Structure mixin_of@{u} (objects : Type@{u}) :=
  Mixin {
      morphisms; id; compm; equiv;
      compmA: @associativity_of_morphisms@{u} objects morphisms compm equiv;
      compm0 : @identity_morphism_is_right_identity@{u} objects morphisms id compm equiv;
      comp0m : @identity_morphism_is_left_identity@{u} objects morphisms id compm equiv;
      comp_left : @compatibility_left@{u} objects morphisms compm equiv;
      comp_right : @compatibility_right@{u} objects morphisms compm equiv;
    }.

Local Notation class_of := mixin_of (only parsing).

Section ClassDef.
Structure type@{u} := Pack {sort; _ : class_of@{u} sort; _ : Type@{u}}.
Universe u.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type@{u}) (cT : type@{u}).
Definition class := let: Pack _ c _ := cT return class_of@{u} cT in c.
Definition pack c := @Pack@{u} T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.
End ClassDef.

Module Notations.
Coercion sort : type >-> Sortclass.
Notation category := type.
Notation CatMixin := Mixin.
Notation CatType T m := (@pack T m).
Arguments id {objects m} A.
Notation id := (@Category.id _ (class _) _).
Notation "'Mor' ( M , N )" := (@morphisms _ (class _) M N) (at level 5).
Definition morph C := @morphisms (sort C) (class C).
Arguments morph _ _ _ : clear implicits.
Notation compm := compm.
Arguments compm {_ _ A B C} _ _ /.
Notation equiv C := (equiv (class C)).
Notation compmA := compmA.
Notation compm0 := compm0.
Notation comp0m := comp0m.
Notation comp_left := comp_left.
Notation comp_right := comp_right.
Notation "f '\compm' g" := (compm f g) (at level 40).
Notation "'Ob' C" := (sort C) (at level 1).
Notation "[ 'CatMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'CatMixin'  'of'  T ]") : form_scope.
Notation "[ 'category' 'of' T 'for' C ]" := (@clone T C _ idfun (fun x => x))
  (at level 0, format "[ 'category'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'category' 'of' T ]" := (@clone T _ _ (fun x => x) (fun x => x))
  (at level 0, format "[ 'category'  'of'  T ]") : form_scope.
End Notations.

Module Down.
Import Notations.
Section Down.
Universes t u.
Constraint t < u.
Definition down (C : category@{t}) : category@{u}.
case: C => c m _.
apply (@Category.Pack@{u} c) => //.
case: m => mo mm cm ce ca ir il cl cr.
set ce' := (fun a b => Equivalence.down@{t u} (ce a b)).
apply (@Category.Mixin@{u} c mo mm cm ce').
+ move=> a b e f h i j.
  move: (ca a b e f h i j).
  by rewrite !equivE Equivalence.downK.
+ move=> a b f.
  move: (ir a b f).
  by rewrite !equivE Equivalence.downK.
+ move=> a b f.
  move: (il a b f).
  by rewrite !equivE Equivalence.downK.
+ move=> a b e f f' g.
  move: (cl a b e f f' g).
  rewrite !equivE Equivalence.downK => H H'.
  move: (H H'); by rewrite Equivalence.downK.
+ move=> a b e f f' g.
  move: (cr a b e f f' g).
  rewrite !equivE Equivalence.downK => H H'.
  move: (H H'); by rewrite Equivalence.downK.
Defined.
End Down.
End Down.
Include Down.

Module Equivalence.
Import Notations.
Canonical partial_equivType T (C : mixin_of T) (A B : T) :=
  Eval hnf in EquivType _ (Category.equiv C A B).
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
Defined.
Notation subst_left := (Congruence.subst_left (@compm_comp _ _ _ _)).
Notation subst_right := (Congruence.subst_right (@compm_comp _ _ _ _)).
Lemma identity_morphism_is_the_unique (C : category) (A : Ob C) (id' : Mor (A, A)) :
  (forall B (f : Mor (A, B)), (f \compm id') == f) -> id' == Category.id A.
Proof.
move => H.
apply: Congruence.etrans; last by apply H.
apply comp0m.
Qed.

Section Isomorphism.
Inductive isomorphisms@{u} (C : category@{u}) (A B: Ob C) (f : Mor (A, B)) (g : Mor (B, A)) : Type@{u} :=
  Isomorphisms : (g \compm f) == id -> (f \compm g) == id -> isomorphisms f g.
Arguments isomorphisms {_ _ _} _ _.
Arguments Isomorphisms {_ _ _} _ _ _ _.

Universe u.
Variable C : category@{u}.
Local Notation piso :=
  (fun A B => pairing (@isomorphisms C A B)).
Lemma piso_sym : Equivalence.symmetricity piso.
Proof.
move=> ? ? [N M] [H1 H2];
apply (@Pairing _ _ _ M N);
by constructor.
Defined.

Lemma piso_refl : Equivalence.reflexivity piso.
Proof.
move => ?; apply (Pairing id id).
by constructor; apply/symP; apply comp0m.
Defined.

Lemma piso_trans : Equivalence.transitivity piso.
Proof.
move => ? ? ?.
move => [f1 g1] [H11 H12] [f2 g2] [H21 H22].
apply (Pairing (f2 \compm f1) (g1 \compm g2)).
constructor;
(apply: Congruence.etrans; first by apply: compmA);
[ apply: Congruence.etrans; last by apply H11
| apply: Congruence.etrans; last by apply H22 ];
apply subst_right;
(apply/symP; apply: Congruence.etrans; last by apply compmA);
(apply: Congruence.etrans; first (by apply: comp0m));
apply subst_left; by apply/symP.
Defined.
Definition obs_equivMixin := EquivMixin@{u} piso_sym piso_trans piso_refl.
Definition obs_equivType := Eval hnf in EquivType@{u} (Ob C) obs_equivMixin.
End Isomorphism.

Structure total (C : category) :=
  TotalEquiv
    { total_dom : Ob C;
      total_cod : Ob C;
      total_mor : Mor (total_dom, total_cod)
    }.
Local Notation td := total_dom.
Local Notation tc := total_cod.
Local Notation tm := total_mor.
Coercion TotalEquiv : morphisms >-> total.
Definition total_op C (f g : total C) :=
  @pairing (pairing (@isomorphisms C (td f) (td g))) (pairing (@isomorphisms C (tc f) (tc g)))
           (fun p1 p2 => p2.1 \compm tm f == tm g \compm p1.1).
Local Arguments total_op C f g /.

Lemma total_reflP C : Equivalence.reflexivity (@total_op C).
Proof.
  move=> [fA fB f].
  apply (Pairing (@Pairing _ _ (fun x y => isomorphisms x y) id id (Isomorphisms (symP (compm0 _)) (symP (compm0 _))))
                 (@Pairing _ _ (fun x y => isomorphisms x y) id id (Isomorphisms (symP (compm0 _)) (symP (compm0 _))))).
  apply: Congruence.etrans; first (apply/symP; apply: comp0m).
   by apply: compm0.
Qed.

Lemma total_symP C : Equivalence.symmetricity (@total_op C).
Proof.
  move=> [fA fB f] [gA gB g] /= [H1 H2] H3.
  move: H1 H2 H3 => 
  [p11 p12 [p11H p12H]] [p21 p22 [p21H p22H]] H3.
  apply (Pairing (Pairing p12 p11 (Isomorphisms p12H p11H)) (Pairing p22 p21 (Isomorphisms p22H p21H))).
  apply: Congruence.etrans.
  apply: subst_right.
  apply: compm0.
  apply: Congruence.etrans.
  apply/symP; apply: compmA.
  apply: Congruence.etrans.
  apply: subst_right.
  apply/symP; apply: p12H.
  apply: Congruence.etrans.
  apply/symP; apply: compmA.
  apply: subst_left.
  apply: Congruence.etrans.
  apply: compmA.
  apply: Congruence.etrans.
  apply: subst_right.
  apply/symP; apply: H3.
  apply: Congruence.etrans.
  apply/symP; apply: compmA.
  apply: Congruence.etrans.
  apply: subst_left.
  apply: p21H.
  apply/symP; apply: comp0m.
Qed.
Lemma total_transP C : Equivalence.transitivity (@total_op C).
Proof.
  move=> [fA fB f] [gA gB g] [hA hB h] /= [p11 p12 p1H] [p21 p22 p2H].
  move: p11 p1H => [p111 p112 [p111H p112H]].
  move: p12 => [p121 p122 [p121H p122H]].
  move: p22 p2H => [p221 p222 [p221H p222H]].
  move: p21 => [p211 p212 [p211H p212H]].
  move=> /= p1H p2H.
  apply: (Pairing
           (Pairing (p211 \compm p111) (p112 \compm p212) _)
           (Pairing (p221 \compm p121) (p122 \compm p222) _)).
  constructor.
   apply: Congruence.etrans; first apply: compmA.
   apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: compmA).
   apply: Congruence.etrans; first (apply: subst_right; apply: subst_left; apply: p211H).
   apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: comp0m).
   apply p111H.
  apply: Congruence.etrans; first apply: compmA.
  apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: compmA).
  apply: Congruence.etrans; first (apply: subst_right; apply: subst_left; apply: p112H).
  apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: comp0m).
  apply p212H.
  constructor.
   apply: Congruence.etrans; first apply: compmA.
   apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: compmA).
   apply: Congruence.etrans; first (apply: subst_right; apply: subst_left; apply: p221H).
   apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: comp0m).
   apply p121H.
  apply: Congruence.etrans; first apply: compmA.
  apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: compmA).
  apply: Congruence.etrans; first (apply: subst_right; apply: subst_left; apply: p122H).
  apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: comp0m).
  apply p222H.
  apply: Congruence.etrans; first apply: compmA.
  apply: Congruence.etrans; first (apply: subst_right; apply: p2H).
  apply: Congruence.etrans; first (apply/symP; apply: compmA).
  apply: Congruence.etrans; first (apply: subst_left; apply: p1H).
  apply: Congruence.etrans; first apply: compmA.
  apply/reflP.
Qed.
Definition total_equivMixin C := EquivMixin (@total_symP C) (@total_transP C) (@total_reflP C).
Canonical total_equivType C := Eval hnf in EquivType (total C) (total_equivMixin C).
Local Notation "f ~ g" := (@equiv_op (total_equivType _) (TotalEquiv f) (TotalEquiv g)) (at level 30).

Lemma suff_partial C (A B : Ob C) (f : Mor (A, B)) (g : Mor (A, B)) : f == g -> f ~ g.
Proof.
move=> H.
apply (Pairing (@Pairing _ _ (fun x y => isomorphisms x y) id id (Isomorphisms (symP (compm0 _)) (symP (compm0 _))))
               (@Pairing _ _ (fun x y => isomorphisms x y) id id (Isomorphisms (symP (compm0 _)) (symP (compm0 _))))).
apply: Congruence.etrans; first (apply/symP; apply: comp0m).
by apply: Congruence.etrans; last apply: compm0.
Qed.

(* Lemma necs_partial C (A B : Ob C) (f : Mor (A, B)) (g : Mor (A, B)) : f ~ g -> f == g. *)
(* Proof. *)
(* move=> [[p11 p12 [p11H p12H]] [p21 p22 [p21H p22H]] H]. *)
(* apply: Congruence.etrans; first apply: comp0m. *)
(* apply: Congruence.etrans; first (apply: subst_left; apply/symP; apply: p21H). *)
(* apply: Congruence.etrans; first apply: compmA. *)
(* apply: Congruence.etrans; first (apply: subst_right; apply: H). *)
(* rewrite /=. *)
(* Qed. *)
End Equivalence.

Module Exports.
Include Notations.
Include Equivalence.
Coercion down : category >-> category.
End Exports.
End Category.
Export Category.Exports.

Module Functor.
Section Axioms.
Universes u u'.
Variable domain : category@{u}.
Variables codomain : category@{u'}.
Variable map_of_objects : Ob domain -> Ob codomain.
Variable map_of_morphisms :
  forall A B, Mor(A, B) -> Mor(map_of_objects A, map_of_objects B).
Definition maps_identity_to_identity :=
  forall A, @map_of_morphisms A A (Category.id A) == (Category.id (map_of_objects A)).
Definition preserve_composition :=
  forall A B C (f : Mor(A, B)) (g : Mor(B, C)),
  map_of_morphisms (g \compm f) == map_of_morphisms g \compm (map_of_morphisms f).
Definition preserve_equivalence :=
  forall A B (f f' : Mor(A, B)),
    f == f' -> map_of_morphisms f == map_of_morphisms f'.
End Axioms.

Structure mixin_of@{u u'}
          (dom : category@{u})
          (cod : category@{u'}) map_of_objects :=
  Mixin {
      map_of_morphisms;
      id_id : @maps_identity_to_identity dom cod map_of_objects map_of_morphisms;
      pres_comp : @preserve_composition dom cod map_of_objects map_of_morphisms;
      pres_equiv : @preserve_equivalence dom cod map_of_objects map_of_morphisms;
    }.
Local Notation class_of := mixin_of (only parsing).

Section ClassDef.
Structure type@{u u'} dom cod :=
  Pack { map; _: @class_of@{u u'} dom cod map; _: Type@{u}; _: Type@{u'} }.
Universes u u'.
Variables (domT : category@{u})
          (codT : category@{u'})
          (cT : @type domT codT)
          (mapT : Ob domT -> Ob codT).
Definition class := let: Pack _ c _ _ := cT return @class_of@{u u'} _ _ (map cT) in c.
Definition pack c := @Pack domT codT mapT c (Ob domT) (Ob codT).
Definition clone (c : mixin_of mapT) (_ : phant_id (pack c) cT) := pack c.
End ClassDef.

Module Notations.
Definition app_fun_mor (dom cod : category) (f : type dom cod) :=
  @map_of_morphisms _ _ _ (class f).
Arguments app_fun_mor /.
Notation "' F" := (@app_fun_mor _ _ F _ _) (at level 1).
Coercion map: type >-> Funclass.
Notation functor := type.
Notation FunMixin := Mixin.
Notation FunType C D m := (@pack C D _ m).
Notation id_id := (id_id (class _)).
Notation pres_comp := (pres_comp (class _)).
Notation pres_equiv := (pres_equiv (class _)).
Notation "'Fun' ( C , D )" := (@type C D).
End Notations.

Module Composition.
Import Notations.
Section compf.
Variables (C D E : category) (G : Fun (D, E)) (F : Fun (C, D)).
Definition compfm A B (f : Mor(A, B)) : Mor((G \o F) A, (G \o F) B) := 'G ('F f).
Lemma compf_id_id : maps_identity_to_identity compfm.
Proof.
move=> ?.
apply: Congruence.etrans;
 last by apply: id_id.
by apply pres_equiv, id_id.
Defined.
Lemma compf_pres_comp : preserve_composition compfm.
Proof.
move=> ? ? ? ? ?.
apply: Congruence.etrans;
 last by apply: pres_comp.
by apply pres_equiv, pres_comp.
Defined.
Lemma compf_pres_equiv : preserve_equivalence compfm.
Proof.
move=>? ? ? ? ?;
 by do !apply: pres_equiv.
Defined.
Definition compf_Mixin :=
  FunMixin compf_id_id compf_pres_comp compf_pres_equiv.
Definition compf := FunType _ _ compf_Mixin.
End compf.
Notation "F \compf G" := (compf F G) (at level 40).
End Composition.

Module Identity.
Import Notations.
Section idf.
Variable C : category.
Definition idfm (A B : Ob C) (f : Mor (A, B)) := f.
Definition idf_id_id := (fun _  => reflP) : maps_identity_to_identity idfm.
Definition idf_pres_comp := (fun _ _ _ _ _ => reflP) : preserve_composition idfm.
Definition idf_pres_equiv := (fun _ _ _ _ => (fun x => x)) : preserve_equivalence idfm.
Definition idf_Mixin := FunMixin idf_id_id idf_pres_comp idf_pres_equiv.
Definition idf := FunType _ _ idf_Mixin.
End idf.
End Identity.

Module Exports.
Include Notations.
Include Composition.
Include Identity.
End Exports.
End Functor.
Export Functor.Exports.

Module NaturalTransformation.
Section Axioms.
Universes u u'.
Variable C : category@{u}.
Variable D : category@{u'}.
Variables F G : (functor@{u u'} C D).
Variable map : forall X, Mor (F X, G X).
Arguments map {X}.
Definition naturality_axiom :=
  forall A A' (f : Mor (A, A')), map \compm 'F f == 'G f \compm map.
End Axioms.

Structure mixin_of@{u u'} (C : category@{u}) (D : category@{u'}) F G natural_map :=
  Mixin { naturality : @naturality_axiom C D F G natural_map }.

Local Notation class_of := mixin_of (only parsing).

Section ClassDef.
Universes u u'.
Variable dom : category@{u}.
Variable cod : category@{u'}.
Structure type domf codf := Pack { map; _ : @class_of@{u u'} dom cod domf codf map; _ : Type@{u'} }.
Variables (domfT codfT : functor@{u u'} dom cod) (cT : type domfT codfT)
          (mapT : forall X , Mor(domfT X, codfT X)).
Definition class := let: Pack _ c _ := cT return @class_of dom cod domfT codfT (map cT) in c.
Definition pack c := @Pack domfT codfT mapT c (forall X, Mor(domfT X, codfT X)).
End ClassDef.

Module Notations.
Definition app_nat dom cod f g (n : @type dom cod f g) := map n.
Arguments app_nat /.
Notation "'Nat' ( M , N )" := (@type _ _ M N) (at level 5).
Coercion app_nat: type >-> Funclass.
Notation natural_transformation := type.
Notation NatMixin := Mixin.
Notation NatType F G m := (@pack _ _ F G _ m).
Definition naturality' C D F G N := @naturality C D F G _ (class N).
Notation naturality :=  naturality'.
Notation "[ 'NatMixin' 'of' T 'to' S ]" := (class _ : @mixin_of _ _ T S)
  (at level 0, format "[ 'NatMixin'  'of'  T 'to' S ]") : form_scope.
End Notations.

Module Identity.
Import Notations.
Section idn.
Universes u u'.
Variable C : category@{u}.
Variable D : category@{u'}.
Variable F : functor@{u u'} C D.
Definition idn_map X := @Category.id@{u'} _ (Category.class D) (F X).
Lemma idn_map_naturality : naturality_axiom idn_map.
move=> ? ? ? /=.
apply: Congruence.etrans; last apply: compm0.
by apply/symP; apply: comp0m.
Defined.
Definition idn := NatType F F (NatMixin@{u u'} idn_map_naturality).
End idn.
End Identity.

Module Composition.
Import Notations.
Section compn.
Universes u u'.
Variable C : category@{u}.
Variable D : category@{u'}.
Variables F G H : functor@{u u'} C D.
Variable M : natural_transformation@{u u'} G H.
Variable N : natural_transformation@{u u'} F G.
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
Definition compn := NatType _ _ (NatMixin compn_naturality).
End compn.
Notation "N \compn M" := (compn N M)  (at level 40).

Section compfn.
Import Notations.
Universes u u' u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Variable E : category@{u''}.
Variable F G : functor@{u u'} C D.
Variable H : functor@{u' u''} D E.
Variable N : natural_transformation@{u u'} F G.
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
  NatType _ _ (NatMixin compfn_naturality).
End compfn.
Notation "F \compfn N" := (compfn F N) (at level 40).

Section compnf.
Universes u u' u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Variable E : category@{u''}.
Variable F G : functor@{u' u''} D E.
Variable N : natural_transformation@{u' u''} F G.
Variable H : functor@{u u'} C D.
Definition compnf_map X := N (H X).
Lemma compnf_naturality : @naturality_axiom C E (F \compf H) (G \compf H) compnf_map.
Proof.
move => ? ? ? /=.
apply: naturality.
Defined.
Definition compnf :=
  NatType _ _ (NatMixin compnf_naturality).
End compnf.
Notation "N \compnf F" := (compnf N F)  (at level 40).
End Composition.

Module Exports.
Include Notations.
Include Identity.
Include Composition.
End Exports.
End NaturalTransformation.
Export NaturalTransformation.Exports.

Module Limit.
Section Axioms.
Variables I C : category.
Variable F : Fun (I, C).
Notation solution_of_diagram L :=
  (sigT (fun (s : (forall A, Mor (L, F A))) =>
         forall A B (f : Mor (A, B)), ('F f) \compm (s A) == (s B))).
Local Definition proj1_sigT A P (t : sigT P) :=
  match t with
  | existT x _ => x : A
  end.
Local Definition proj2_sigT A P (t : sigT P) :=
  match t as e return P (@proj1_sigT A P e) with
  | existT x y => y
  end.
Definition morphism_of_solutions L L'
      (sL : solution_of_diagram L) (sL' : solution_of_diagram L') :=
    sigT (fun l => forall A, (proj1_sigT sL' A) == (proj1_sigT sL A) \compm l).
Definition universality_axiom L
      (sL : solution_of_diagram L)
      (u : (forall L' (sL' : solution_of_diagram L'), morphism_of_solutions sL sL')) :=
  (forall L' u' (sL' : solution_of_diagram L'),
      (forall A, (proj1_sigT sL' A) == (proj1_sigT sL A) \compm u') -> proj1_sigT (u L' sL') == u').
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
Local Lemma add_loop (I C : category)  (F : Fun (I, C)) (limL : limit F) (f : Mor (limL, limL)) :
  let sL := canonical_solution limL in
  (forall (A B : Ob I) (g : Mor (A, B)),
    ('F g) \compm (proj1_sigT sL A \compm f) == (proj1_sigT sL B \compm f)) ->
    (forall A : Ob I, proj1_sigT sL A == proj1_sigT sL A \compm f) ->
  f == id.
Proof.
case: limL f => L sL uL pL f /= H H'.
have: proj1_sigT (uL L sL) == f.
apply pL, H'.
have: proj1_sigT (uL L sL) == id.
apply pL.
move => A.
apply compm0.
move => H1 H2.
apply: Congruence.etrans; last apply: H1.
by apply/symP.
Defined.
  
Lemma limit_is_the_unique (I C : category) (F : Fun (I, C)) :
  forall (limL : limit F) (limL' : limit F),
    @equiv_op (obs_equivType C) (limit_object limL) (limit_object limL').
Proof.
move => limL limL' /=.
apply: Pairing.
set u := (@universal_morphism _ _ _ limL' _ (canonical_solution limL)).
set u' := (@universal_morphism _ _ _ limL _ (canonical_solution limL')).
apply (@Isomorphisms _ _ _ (proj1_sigT u) (proj1_sigT u')).
  apply (@add_loop I C F limL).
  move => A B g /=.
  apply/symP.
  apply: Congruence.etrans; last apply compmA.
  apply subst_left.
  apply/symP.
  apply (proj2_sigT (canonical_solution limL)).
 move => A.
 apply: Congruence.etrans; last apply compmA.
 apply: Congruence.etrans; first apply (proj2_sigT u A).
 apply subst_left.
 apply: Congruence.etrans; first apply (proj2_sigT u' A).
 apply/reflP.
apply (@add_loop I C F limL').
 move => A B g /=.
 apply/symP.
 apply: Congruence.etrans; last apply compmA.
 apply subst_left.
 apply/symP.
 apply (proj2_sigT (canonical_solution limL')).
move => A.
apply: Congruence.etrans; last apply compmA.
apply: Congruence.etrans; first apply (proj2_sigT u' A).
apply subst_left.
apply: Congruence.etrans; first apply (proj2_sigT u A).
apply/reflP.
Defined.
End Exports.
End Limit.
Export Limit.Exports.

Section Funs.
Section Isomorphism.
Universes u u' u''.
Constraint u <= u''.
Constraint u' <= u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Variables F G : functor@{u u'} C D.
Local Notation fniso :=
  (fun (N M : natural_transformation@{u u'} F G)
   => forall X, N X == M X).
Lemma fniso_sym : Equivalence.symmetricity@{u''} fniso.
Proof. move => ? ? ? ?. by apply/symP. Defined.

Lemma fniso_refl : Equivalence.reflexivity@{u''} fniso.
Proof. move => ? ?. by apply/reflP. Defined.

Lemma fniso_trans : Equivalence.transitivity@{u''} fniso.
Proof. move => ? ? ? H ? ?. by (apply/transP; first by apply: H). Defined.
Definition nats_equivMixin := Eval hnf in EquivMixin@{u''} fniso_sym fniso_trans fniso_refl.
Definition nats_equivType := Eval hnf in EquivType@{u''} (natural_transformation@{u u'} F G) nats_equivMixin.
End Isomorphism.

Universes u u' u''.
Constraint u <= u''.
Constraint u' <= u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Lemma funs_associativity : @Category.associativity_of_morphisms@{u''} _ _ (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof. move => C' D' E F h i j X /=. apply compmA. Defined.

Lemma funs_compm0 : @Category.identity_morphism_is_right_identity@{u''} _ _ (@idn C D) (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof. move => C' D' f X. apply compm0. Defined.

Lemma funs_comp0m : @Category.identity_morphism_is_left_identity@{u''} _ _ (@idn C D) (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof. move => C' D' f X. apply comp0m. Defined.

Lemma funs_comp_left : @Category.compatibility_left@{u''} _ _ (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof.
  move => ? ? ? f f' g /= H X.
  apply comp_left.
  rewrite /=.
  move: f f' H => [f ? ?] [f' ? ?] H.
  apply H.
Defined.

Lemma funs_comp_right : @Category.compatibility_right@{u''} _ _ (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof.
  move => ? ? ? f f' g /= H X.
  apply comp_right.
  move: f f' H => [f ? ?] [f' ? ?] H.
  apply H.
Defined.
Canonical funs_catMixin := CatMixin@{u''} funs_associativity funs_compm0 funs_comp0m funs_comp_left funs_comp_right.
Canonical funs := Eval hnf in CatType@{u''} (functor@{u u'} C D) funs_catMixin.
End Funs.
Notation "'Fun' ( C , D )" := (funs C D).

Section Cats.
Section Isomorphism.
Inductive natural_isomorphisms@{u u'}
          (C : category@{u})
          (D : category@{u'})
          (F G : functor@{u u'} C D)
          (N : natural_transformation@{u u'} F G)
          (M : natural_transformation@{u' u} G F)
: Type@{max(u,u')} :=
  NaturalIsomorphisms :
    (forall X, isomorphisms@{u'} (N X) (M X)) -> 
    natural_isomorphisms N M.

Arguments natural_isomorphisms {_ _ _ _} _ _.
Arguments NaturalIsomorphisms {_ _ _ _} _ _ _.

Universes u u' u''.
Constraint u <= u''.
Constraint u' <= u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Local Notation pniso :=
  (fun F G => (pairing (@natural_isomorphisms C D F G))).
Lemma pniso_sym : Equivalence.symmetricity pniso.
Proof.
move => ? ?.
move=> [N M] [H]; apply (Pairing M N).
apply NaturalIsomorphisms => X.
case: (H X) => H1 H2; by constructor.
Defined.

Lemma pniso_refl : Equivalence.reflexivity pniso.
Proof.
move => X; apply: Pairing.
apply (@NaturalIsomorphisms _ _ _ _ (idn X) (idn X)) => x.
apply: Isomorphisms => /=;
apply/symP; by apply comp0m.
Defined.

Lemma pniso_trans : Equivalence.transitivity pniso.
Proof.
move => ? ? ?.
move => [N1 M1] [H1] [N2 M2] [H2];
apply: Pairing;
apply (@NaturalIsomorphisms _ _ _ _ (N2 \compn N1) (M1 \compn M2)) => /= X;
case: (H1 X) => /= [H11 ?];
case: (H2 X) => /= [? H22];
apply: Isomorphisms => /=;
(apply: Congruence.etrans; first by apply: compmA);
[ apply: Congruence.etrans; last by apply H11
| apply: Congruence.etrans; last by apply H22 ];
apply subst_right => /=;
(apply/symP; apply: Congruence.etrans; last by apply compmA);
(apply: Congruence.etrans; first (by apply: comp0m));
apply subst_left; by apply/symP.
Defined.
Definition funs_equivMixin := Eval hnf in EquivMixin pniso_sym pniso_trans pniso_refl.
Definition funs_equivType := Eval hnf in EquivType (functor@{u u'} C D) funs_equivMixin.
End Isomorphism.

Universes u u' u'' u'''.
Constraint u <= u'''.
Constraint u' <= u'''.
Constraint u'' <= u'''.
Lemma cats_associativity : @Category.associativity_of_morphisms@{u'''} _ _ compf@{u u' u''} funs_equivMixin.
Proof.
  move => /= C D E F h i j.
  set L := NatType _ _ (@NatMixin _ _ ((j \compf i) \compf h) (j \compf (i \compf h)) (idn _) (idn_map_naturality _)).
  set R := NatType _ _ (@NatMixin _ _ (j \compf (i \compf h)) ((j \compf i) \compf h) (idn _) (idn_map_naturality _)).
  apply: Pairing.
  apply (@NaturalIsomorphisms _ _ _ _ L R);
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Defined.
Lemma cats_compm0 : @Category.identity_morphism_is_right_identity@{u'''} category _ idf compf@{u u' u''} funs_equivMixin.
Proof.
  move => /= C D f.
  set L := NatType _ _ (@NatMixin _ _ f (f \compf idf _) (idn _) (idn_map_naturality _)).
  set R := NatType _ _ (@NatMixin _ _ (f \compf idf _) f (idn _) (idn_map_naturality _)).
  apply: Pairing;
  apply (@NaturalIsomorphisms _ _ _ _ L R).
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Defined.

Lemma cats_comp0m : @Category.identity_morphism_is_left_identity@{u'''} category _ idf compf@{u u' u''} funs_equivMixin.
Proof.
  move => /= C D f.
  set L := NatType _ _ (@NatMixin _ _ f (idf _ \compf f) (idn _) (idn_map_naturality _)).
  set R := NatType _ _ (@NatMixin _ _ (idf _ \compf f) f (idn _) (idn_map_naturality _)).
  apply: Pairing;
  apply (@NaturalIsomorphisms _ _ _ _ L R);
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: compm0.
Defined.

Lemma cats_comp_left : @Category.compatibility_left@{u'''} category _ compf@{u u' u''} funs_equivMixin.
Proof.
  move => ? ? ? f f' g [N M [H]].
  apply: (Pairing 
            (NatType _ _ (@NatMixin _ _ (g \compf f) (g \compf f')
                                    (g \compfn N) (compfn_naturality _ _)))
            (NatType _ _ (@NatMixin _ _ (g \compf f') (g \compf f)
                                    (g \compfn M) (compfn_naturality _ _)))).
  apply: NaturalIsomorphisms => X.
  apply: Isomorphisms; case: (H X) => /= H1 H2;
  (apply: Congruence.etrans;
   first by (apply/symP; apply pres_comp));
  (apply: Congruence.etrans; last by apply id_id);
  by apply: pres_equiv.
Defined.

Lemma cats_comp_right : @Category.compatibility_right@{u'''} category _ compf@{u u' u''} funs_equivMixin.
Proof.
  move => ? ? ? f g g' [N M] [H].
  set L := NatType _ _ (@NatMixin _ _ (g \compf f) (g' \compf f)
                                  (N \compnf f) (compnf_naturality _ _)).
  set R := NatType _ _ (@NatMixin _ _ (g' \compf f) (g \compf f)
                                  (M \compnf f) (compnf_naturality _ _)).
  apply: Pairing.
  apply (@NaturalIsomorphisms _ _ _ _ L R) => X;
  apply: Isomorphisms; by case: (H (f X)).
Defined.
Canonical cats_catMixin := Eval hnf in CatMixin cats_associativity cats_compm0 cats_comp0m cats_comp_left cats_comp_right.
Canonical cats := Eval hnf in CatType@{u'''} category cats_catMixin.
Canonical obs_equivType.
Canonical cats_obs_equivType := Eval hnf in EquivType category (obs_equivMixin cats).
End Cats.