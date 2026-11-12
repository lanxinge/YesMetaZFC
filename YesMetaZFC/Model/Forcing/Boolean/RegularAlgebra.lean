import YesMetaZFC.Model.Forcing.Boolean.RegularSet
import YesMetaZFC.SetTheory.Boolean.CompleteHom

/-! # 任意实际条件序的模型内部完备布尔代数

序是包含，交是实际集合交，剩余沿所有加强读取；双重否定由原正则性证明。
上确界只量化模型内部的集合族，来自同一正则开载体上的并集正则化。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
include hZF

theorem ropen_imp_l {B R z A C : M.Domain} (O : Cond_order_d M B R z)
    (left : Ropen_d B R z A) (right : Ropen_d B R z C) :
    ∃ V, Ropen_d B R z V ∧ ∀ p, M.mem p V ↔ M.mem p B ∧ p ≠ z ∧
      ∀ q, Below_d M B R z q p → M.mem q A → M.mem q C := by
  let ρ : Env M 5 := ⟨fun i => [B,R,z,A,C].get i,fun _ => B⟩
  let φ : UnarySchema 5 := { body := set[6] ⟪⌜(.newest : Term 6)⌝ₛ ≠ ⌜(.bound 3 : Term 6)⌝ₛ ∧
    (∀ q, ⌜below_m⌝ₚ(⌜(.bound 1 : Term 6)⌝ₛ,⌜(.bound 2 : Term 6)⌝ₛ,⌜(.bound 3 : Term 6)⌝ₛ,q,⌜(.newest : Term 6)⌝ₛ) →
      q ∈ ⌜(.bound 4 : Term 6)⌝ₛ → q ∈ ⌜(.bound 5 : Term 6)⌝ₛ)⟫ }
  obtain ⟨V,values⟩ := ZF.separation_exists_d hZF φ ρ B
  have read p : M.mem p V ↔ M.mem p B ∧ p ≠ z ∧
      ∀ q, Below_d M B R z q p → M.mem q A → M.mem q C := by
    apply (values p).trans (and_congr_right fun _ => ?_)
    simp only [φ,Formula.extensionalNe,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      below_sat_l M hZF.1,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
    rfl
  refine ⟨V,⟨fun p hp => ⟨((read p).mp hp).1,((read p).mp hp).2.1⟩,?_,?_⟩,read⟩
  · intro p q hp hq h
    exact (read q).mpr ⟨hq.1,hq.2.1,fun r hr => ((read p).mp h).2.2 r (below_trans_l O hp hr hq)⟩
  · intro p hp hz dense
    refine (read p).mpr ⟨hp,hz,fun q hq hA => right.2.2 q hq.1 hq.2.1 ?_⟩
    intro r hr
    obtain ⟨s,hs,hV⟩ := dense r (below_trans_l O hp hr hq)
    exact ⟨s,hs,((read s).mp hV).2.2 s (below_refl_l O hs.1 hs.2.1)
      (left.2.1 q s hq.1 (below_trans_l O hq.1 hs hr) hA)⟩

theorem ropen_completion_l {B R z : M.Domain} (O : Cond_order_d M B R z) :
    ∃ K S e, (∀ V, M.mem V K ↔ Ropen_d B R z V) ∧ (∀ p, ¬ M.mem p e) ∧
      (∀ U V, Entry_d M U V S ↔ M.mem U K ∧ M.mem V K ∧ M.MemberSubset U V) ∧
      BooleanZF.Cba_d I K S e := by
  obtain ⟨K,family⟩ := ropen_family_l hZF B R z
  obtain ⟨e,empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have he := (family e).mpr (Ropen_d.empty_l O empty)
  let φ : BinarySchema 0 := { body := .subset (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0,fun _ => K⟩
  obtain ⟨S,_,values⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ K
  have read U V : Entry_d M U V S ↔ M.mem U K ∧ M.mem V K ∧ M.MemberSubset U V :=
    (values U V).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_subset_iff ..)
  have order : BooleanZF.Order_d I K S := {
    refl := fun U hU => (read U U).mpr ⟨hU,hU,fun _ h => h⟩
    trans := fun U V W hU _ hW uv vw => (read U W).mpr ⟨hU,hW,
      fun p hp => ((read V W).mp vw).2.2 p (((read U V).mp uv).2.2 p hp)⟩
    antisymm := fun U V _ _ uv vu => hZF.1.eq_of_same_members U V
      (fun p => ⟨((read U V).mp uv).2.2 p,((read V U).mp vu).2.2 p⟩) }
  have inter A C (hA : M.mem A K) (hC : M.mem C K) : ∃ V, M.mem V K ∧
      (∀ p, M.mem p V ↔ M.mem p A ∧ M.mem p C) ∧ BooleanZF.Meet_d I K S A C V := by
    obtain ⟨V,hV,meet⟩ := ropen_inter_l hZF ((family A).mp hA) ((family C).mp hC)
    have memV := (family V).mpr hV
    refine ⟨V,memV,meet,memV,?_⟩
    intro D hD
    change Entry_d M D V S ↔ Entry_d M D A S ∧ Entry_d M D C S
    simp only [read,hD,hA,hC,memV,true_and]
    exact ⟨fun sub => ⟨fun p hp => ((meet p).mp (sub p hp)).1,fun p hp => ((meet p).mp (sub p hp)).2⟩,
      fun ⟨left,right⟩ p hp => (meet p).mpr ⟨left p hp,right p hp⟩⟩
  have implication A C (hA : M.mem A K) (hC : M.mem C K) : ∃ V, BooleanZF.Imp_d I K S A C V ∧
      ∀ p, M.mem p V ↔ M.mem p B ∧ p ≠ z ∧ ∀ q, Below_d M B R z q p → M.mem q A → M.mem q C := by
    obtain ⟨V,regular,imp⟩ := ropen_imp_l hZF O ((family A).mp hA) ((family C).mp hC)
    have hV := (family V).mpr regular
    refine ⟨V,⟨hV,?_⟩,imp⟩
    intro D hD
    constructor
    · intro dv J meet
      have ja := BooleanZF.meet_bounds_d I order meet
      apply (read J C).mpr
      refine ⟨meet.1,hC,?_⟩
      intro p hp
      have hd := ((read J D).mp ja.1).2.2 p hp
      have bound := ((family D).mp hD).1 p hd
      exact ((imp p).mp (((read D V).mp dv).2.2 p hd)).2.2 p (below_refl_l O bound.1 bound.2)
        (((read J A).mp ja.2).2.2 p hp)
    · intro all
      obtain ⟨J,_,meet,hJ⟩ := inter D A hD hA
      have sub := ((read J C).mp (all J hJ)).2.2
      apply (read D V).mpr
      refine ⟨hD,hV,fun p hp => (imp p).mpr ?_⟩
      have bound := ((family D).mp hD).1 p hp
      exact ⟨bound.1,bound.2,fun q hq hqA => sub q ((meet q).mpr
        ⟨((family D).mp hD).2.1 p q bound.1 hq hp,hqA⟩)⟩
  have unique {A C U V} (a : BooleanZF.Imp_d I K S A C U) (b : BooleanZF.Imp_d I K S A C V) : U = V :=
    order.antisymm U V a.1 b.1 ((b.2 U a.1).mpr ((a.2 U a.1).mp (order.refl U a.1)))
      ((a.2 V b.1).mpr ((b.2 V b.1).mp (order.refl V b.1)))
  have complete : ∀ A, M.MemberSubset A K → ∃ V, BooleanZF.Bsup_d I K S A V := by
    intro A sub
    obtain ⟨V,hV,upper,least⟩ := ropen_sup_l hZF O family sub
    exact ⟨V,hV,(fun U hU => (read U V).mpr ⟨sub U hU,hV,upper U hU⟩),
      fun W hW bound => (read V W).mpr ⟨hV,hW,least W hW (fun U hU => ((read U W).mp (bound U hU)).2.2)⟩⟩
  refine ⟨K,S,e,family,empty,read,⟨⟨order,he,fun U hU => (read e U).mpr ⟨he,hU,fun p hp => (empty p hp).elim⟩,
    (fun A C hA hC => (inter A C hA hC).imp fun _ h => h.2.2),
    (fun A C hA hC => (implication A C hA hC).imp fun V h => h.1),?_⟩,complete⟩⟩
  intro A U V hA first second
  obtain ⟨U',first',firstRead⟩ := implication A e hA he
  have eq := unique first' first
  subst U'
  obtain ⟨V',second',secondRead⟩ := implication U e first.1 he
  have eq := unique second' second
  subst V'
  apply hZF.1.eq_of_same_members V A
  intro p
  constructor
  · intro hp
    obtain ⟨hpB,hpz,never⟩ := (secondRead p).mp hp
    apply Classical.byContradiction
    intro no
    obtain ⟨q,hq,neg⟩ := regular_neg_witness_l ((family A).mp hA).2 hpB hpz no
    exact empty q (never q hq ((firstRead q).mpr ⟨hq.1,hq.2.1,fun r hr h => (neg r hr h).elim⟩))
  · intro hp
    have bound := ((family A).mp hA).1 p hp
    refine (secondRead p).mpr ⟨bound.1,bound.2,?_⟩
    intro q hq hu
    exact ((firstRead q).mp hu).2.2 q (below_refl_l O hq.1 hq.2.1)
      (((family A).mp hA).2.1 p q bound.1 hq hp)

theorem ropen_meet_values_l {B R z K S e A C V : M.Domain}
    (family : ∀ U, M.mem U K ↔ Ropen_d B R z U)
    (order : ∀ U V, Entry_d M U V S ↔ M.mem U K ∧ M.mem V K ∧ M.MemberSubset U V)
    (algebra : BooleanZF.Boolean_d I K S e) (hA : M.mem A K) (hC : M.mem C K)
    (meet : BooleanZF.Meet_d I K S A C V) : ∀ p, M.mem p V ↔ M.mem p A ∧ M.mem p C := by
  obtain ⟨D,hD,inter⟩ := ropen_inter_l hZF ((family A).mp hA) ((family C).mp hC)
  have hd := (family D).mpr hD
  have dv := (meet.2 D hd).mpr ⟨(order D A).mpr ⟨hd,hA,fun p hp => ((inter p).mp hp).1⟩,
    (order D C).mpr ⟨hd,hC,fun p hp => ((inter p).mp hp).2⟩⟩
  have bounds := BooleanZF.meet_bounds_d I algebra.order meet
  exact fun p => ⟨fun hp => ⟨((order V A).mp bounds.1).2.2 p hp,((order V C).mp bounds.2).2.2 p hp⟩,
    fun hp => ((order D V).mp dv).2.2 p ((inter p).mpr hp)⟩

end YesMetaZFC.Model.Forcing.Internal
