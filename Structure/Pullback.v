Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(* Given a cospan in C:

           A         B
            \       /
           f \     / g
              \   /
                v
                C

   This can be thought of, set-theoretically, as the equation:

      ∀ a ∈ A, b ∈ B, f(b) = g(a)

   Which is a strong statement, requiring that every element of A agree with
   an element of B, through f and g. A pullback is a subset of the cartesian
   product of A and B, X ⊆ A × B, such that (a, b) ∈ X, where the following
   diagram commutes:

                 X
               /   \
           pA /     \ pB
             /       \
            A         B
             \       /
            f \     / g
               \   /
                 v
                 C

   An example of this is an INNER JOIN of two SQL tables, where f projects a
   primary key from A, and g a foreign key referencing A, so that X contains
   exactly those pairs of rows from A and B where id(A) = fkey(B).

   Wikipedia: "In fact, the pullback is the universal solution to finding a
   commutative square like this. In other words, given any commutative square
   [replacing in the above X with Y, and pA and pB with qA and qB] there is a
   unique function h : Y → X such that pA ∘ h ≈ qA and pB ∘ h ≈ qB." *)

(* Definition, in terms of morphisms and universal properties:

   Wikipedia: "A pullback of the morphisms f and g consists of an object P
   [Pull] and two morphisms p1 : P → X [pullback_fst] and p2 : P → Y
   [pullback_snd] for which the diagram

       P ---p2---> Y
       |           |
     p1|           |g
       |           |
       X ---f----> Z

   commutes. Moreover, the pullback (P, p1, p2) must be universal with respect
   to this diagram. That is, for any other such triple (Q, q1, q2) for which
   the following diagram commutes, there must exist a unique u : Q → P (called
   a mediating morphism) such that

    p1 ∘ u = q1,    p2 ∘ u = q2

   jww (2017-06-01): TODO
   As with all universal constructions, a pullback, if it exists, is unique up
   to isomorphism. In fact, given two pullbacks (A, a1, a2) and (B, b1, b2) of
   the same cospan X → Z ← Y, there is a unique isomorphism between A and B
   respecting the pullback structure." *)

Record Pullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) := {
  Pull : C;
  pullback_fst : Pull ~> x;
  pullback_snd : Pull ~> y;

  pullback_commutes : f ∘ pullback_fst ≈ g ∘ pullback_snd;

  ump_pullbacks : ∀ Q (q1 : Q ~> x) (q2 : Q ~> y), f ∘ q1 ≈ g ∘ q2
    → ∃! u : Q ~> Pull, pullback_fst ∘ u ≈ q1 ∧ pullback_snd ∘ u ≈ q2
}.

Coercion pullback_ob {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z)
         (L : Pullback f g) := @Pull _ _ _ _ _ _ L.

Require Import Category.Construction.Opposite.

Definition Pushout {C : Category} {x y z : C^op} (f : x ~> z) (g : y ~> z) :=
  Pullback f g.

(* jww (2017-06-01): TODO *)
(* Wikipedia: "A weak pullback of a cospan X → Z ← Y is a cone over the cospan
   that is only weakly universal, that is, the mediating morphism u : Q → P
   above is not required to be unique." *)

(* jww (2017-06-01): TODO *)
(* Wikipedia: "The pullback is similar to the product, but not the same. One
   may obtain the product by "forgetting" that the morphisms f and g exist,
   and forgetting that the object Z exists. One is then left with a discrete
   category containing only the two objects X and Y, and no arrows between
   them. This discrete category may be used as the index set to construct the
   ordinary binary product. Thus, the pullback can be thought of as the
   ordinary (Cartesian) product, but with additional structure. Instead of
   "forgetting" Z, f, and g, one can also "trivialize" them by specializing Z
   to be the terminal object (assuming it exists). f and g are then uniquely
   determined and thus carry no information, and the pullback of this cospan
   can be seen to be the product of X and Y." *)

(* jww (2017-06-02): *)
(* Wikipedia: "... another way of characterizing the pullback: as the
   equalizer of the morphisms f ∘ p1, g ∘ p2 : X × Y → Z where X × Y is the
   binary product of X and Y and p1 and p2 are the natural projections. This
   shows that pullbacks exist in any category with binary products and
   equalizers. In fact, by the existence theorem for limits, all finite limits
   exist in a category with a terminal object, binary products and
   equalizers." *)




Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); try f_equiv; cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); try f_equiv; cat.

Theorem pullback_implies_monic {C : Category} {A B : C} (f : A ~> B) 
  (pb : Pullback f f) (pbISO : pb ≅ A) (H : (@pullback_fst _ _ _ _ _ _ pb) ∘ (from pbISO) ≈ id(x:=A)) 
  (I : (@pullback_snd _ _ _ _ _ _ pb) ∘ (from pbISO) ≈ id(x:=A)) : Monic f.
Proof.
  destruct pb. simpl in *. rename Pull0 into P. rename pullback_fst0 into p1. rename pullback_snd0 into p2.
  assert (GOOL : ∀ z (g1 g2 : z ~> A), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2).
  + intros.
    destruct pbISO. simpl in *. apply ump_pullbacks0 in X. destruct X. rename unique_obj into u. 
    destruct unique_property as [p1U p2U]. 
    assert(HEEEELP :  ∃! v : z ~> A, (p1 ∘ from ∘ v ≈ g1) ∧ (p2 ∘ from ∘ v ≈ g2)). 
    {
       exists (to ∘ u).
       +++ split.
           ++++ reassociate_left. rewrite comp_assoc with (f := from) (g := to) (h := u). rewrite iso_from_to. cat.
           ++++ reassociate_left. rewrite comp_assoc with (f := from) (g := to) (h := u). rewrite iso_from_to. cat.
       +++ intros. specialize uniqueness with (from ∘ v).
           destruct X. rewrite <- comp_assoc in e. rewrite <- comp_assoc in e0.
           assert (ANDESHUN : p1 ∘ (from ∘ v) ≈ g1 ∧ p2 ∘ (from ∘ v) ≈ g2 ).
           { split; assumption. }
           apply uniqueness in ANDESHUN. rewrite ANDESHUN. reassociate_right. rewrite iso_to_from. cat.
      }
      destruct HEEEELP. rename unique_obj into v. 
      destruct unique_property as [LEFT RIGHT]. 
      rewrite H in LEFT. rewrite I in RIGHT.
      rewrite <- LEFT. rewrite <- RIGHT. cat.
  + refine ({|
      monic := GOOL
    |}).
Defined.


Theorem pullback_unique {C : Category} {A X Y : C} (f : X ~> A) (g : Y ~> A)
  (pp pq : Pullback f g) : pp ≅ pq.
Proof.
  destruct pp. destruct pq. simpl in *. 
  rename Pull0 into P. rename Pull1 into Q. rename pullback_fst0 into p1. rename pullback_fst1 into q1.
  rename pullback_snd0 into p2. rename pullback_snd1 into q2.
  pose proof (ump_pullbacks0 Q q1 q2 pullback_commutes1) as from_iso. 
  pose proof (ump_pullbacks1 P p1 p2 pullback_commutes0) as to_iso.
  destruct from_iso as [j Hj uniqueness_j]. destruct to_iso as [i Hi uniqueness_i].
  destruct Hj as [Hj_p1 Hj_p2].
  destruct Hi as [Hi_q1 Hi_q2].

  assert (p1_ji : p1 ∘ j ∘ i ≈ p1). { rewrite Hj_p1. cat. }
  assert (p2_ji : p2 ∘ j ∘ i ≈ p2). { rewrite Hj_p2. cat. }

  assert (q1_ij : q1 ∘ i ∘ j ≈ q1). { rewrite Hi_q1. cat. }
  assert (q2_ij : q2 ∘ i ∘ j ≈ q2). { rewrite Hi_q2. cat. }

  pose proof (ump_pullbacks0 P p1 p2 pullback_commutes0) as H.
  destruct H as [u Hu uniqueness_u].

  pose proof (ump_pullbacks1 Q q1 q2 pullback_commutes1) as H.
  destruct H as [v Hv uniqueness_v].

  rewrite <- comp_assoc in p1_ji. rewrite <- comp_assoc in p2_ji.
  assert (TMP : p1 ∘ (j ∘ i) ≈ p1 ∧ p2 ∘ (j ∘ i) ≈ p2). { auto. }
  pose proof (uniqueness_u (j ∘ i) TMP) as uji.
  clear TMP.

  rewrite <- comp_assoc in q1_ij. rewrite <- comp_assoc in q2_ij.
  assert (TMP : q1 ∘ (i ∘ j) ≈ q1 ∧ q2 ∘ (i ∘ j) ≈ q2). { auto. }
  pose proof (uniqueness_v (i ∘ j) TMP) as vij.
  clear TMP.
  
    unshelve refine {|to := i; from := j|}.
    + rewrite <- vij. apply uniqueness_v. split; cat.
    + rewrite <- uji. apply uniqueness_u. split; cat.
Qed.



Theorem problmemm {C : Category} {A B} (f : A ~> B) (MF : Monic f) :
  @Pullback C A A B f f.
Proof.
  unshelve refine {|Pull := A; pullback_fst := id(x:=A); pullback_snd := id(x:=A)|}.
  + cat.
  + intros. exists q1. 
    ++ split; cat. destruct MF. apply monic in X. assumption.
    ++ intros. destruct X0. simpl in *. rewrite <- e. cat. 
Qed.
