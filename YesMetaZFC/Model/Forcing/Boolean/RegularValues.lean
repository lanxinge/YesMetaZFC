import YesMetaZFC.Model.Forcing.Boolean.RegularAlgebra

/-! # 正则开补与内部上确界的逐条件刻画 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {B R z K S e : M.Domain} (O : Cond_order_d M B R z)
  (family : ∀ U, M.mem U K ↔ Ropen_d B R z U)
  (order : ∀ U V, Entry_d M U V S ↔ M.mem U K ∧ M.mem V K ∧ M.MemberSubset U V)
include O family order

theorem ropen_neg_values_l (algebra : BooleanZF.Boolean_d I K S e)
    (empty : ∀ p, ¬ M.mem p e) {A V : M.Domain} (hA : M.mem A K)
    (neg : BooleanZF.Imp_d I K S A e V) :
    ∀ p, M.mem p V ↔ M.mem p B ∧ p ≠ z ∧ Neg_d M B R z (fun q => M.mem q A) p := by
  obtain ⟨W,regular,values⟩ := ropen_imp_l hZF O ((family A).mp hA) ((family e).mp algebra.bot_mem)
  have hw := (family W).mpr regular
  have imp : BooleanZF.Imp_d I K S A e W := by
    refine ⟨hw,fun D hd => ⟨?_,?_⟩⟩
    · intro dw J meet
      have bounds := BooleanZF.meet_bounds_d I algebra.order meet
      apply (order J e).mpr
      refine ⟨meet.1,algebra.bot_mem,fun p hp => ?_⟩
      have pD := ((order J D).mp bounds.1).2.2 p hp
      have pos := ((family D).mp hd).1 p pD
      exact ((values p).mp (((order D W).mp dw).2.2 p pD)).2.2 p (below_refl_l O pos.1 pos.2)
        (((order J A).mp bounds.2).2.2 p hp)
    · intro all
      obtain ⟨J,meet⟩ := algebra.meet D A hd hA
      have inter : ∀ p, M.mem p J ↔ M.mem p D ∧ M.mem p A :=
        ropen_meet_values_l hZF family order algebra hd hA meet
      apply (order D W).mpr
      refine ⟨hd,hw,fun p hp => ?_⟩
      have pos := ((family D).mp hd).1 p hp
      exact (values p).mpr ⟨pos.1,pos.2,fun q hq qa => ((order J e).mp (all J meet)).2.2 q
        ((inter q).mpr ⟨((family D).mp hd).2.1 p q pos.1 hq hp,qa⟩)⟩
  have eq := imp.unique_l I algebra.order neg
  subst W
  intro p
  exact (values p).trans (and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h q hq ha => empty q (h q hq ha),fun h q hq ha => (h q hq ha).elim⟩)

theorem ropen_sup_values_l (algebra : BooleanZF.Order_d I K S) {D V : M.Domain} (sub : M.MemberSubset D K)
    (sup : BooleanZF.Bsup_d I K S D V) : ∃ U, M.IsUnionOf U D ∧
      ∀ p, M.mem p V ↔ M.mem p B ∧ p ≠ z ∧ Dense_d M B R z (fun q => M.mem q U) p := by
  obtain ⟨U,union⟩ := KP.exists_union (ZF.modelsKP hZF) D
  obtain ⟨W,regular,values⟩ := ropen_closure_l hZF O U
  have hw := (family W).mpr regular
  have lower : Lower_d M B R z (fun q => M.mem q U) := by
    intro p q hp hq hu
    obtain ⟨A,hA,pa⟩ := (union p).mp hu
    exact (union q).mpr ⟨A,hA,((family A).mp (sub A hA)).2.1 p q hp hq pa⟩
  have upper A (ha : M.mem A D) : Entry_d M A W S := by
    apply (order A W).mpr
    refine ⟨sub A ha,hw,fun p hp => ?_⟩
    have pos := ((family A).mp (sub A ha)).1 p hp
    exact (values p).mpr ⟨pos.1,pos.2,dense_intro_l O lower pos.1 ((union p).mpr ⟨A,ha,hp⟩)⟩
  have vw := sup.2.2 W hw upper
  have wv : Entry_d M W V S := by
    apply (order W V).mpr
    refine ⟨hw,sup.1,fun p hp => ?_⟩
    obtain ⟨hp,hz,dense⟩ := (values p).mp hp
    apply ((family V).mp sup.1).2.2 p hp hz
    intro q hq
    obtain ⟨r,hr,hu⟩ := dense q hq
    obtain ⟨A,ha,ra⟩ := (union r).mp hu
    exact ⟨r,hr,((order A V).mp (sup.2.1 A ha)).2.2 r ra⟩
  have eq := algebra.antisymm W V hw sup.1 wv vw
  subst W
  exact ⟨U,union,values⟩

variable {G : M.Domain → Prop} (generic : Generic_d M B R z G)
include generic

theorem ropen_hit_neg_l (algebra : BooleanZF.Boolean_d I K S e)
    (empty : ∀ p, ¬ M.mem p e) {A V : M.Domain} (hA : M.mem A K) (neg : BooleanZF.Imp_d I K S A e V) :
    (∃ p, G p ∧ M.mem p V) ↔ ¬ ∃ p, G p ∧ M.mem p A := by
  have values := ropen_neg_values_l hZF O family order algebra empty hA neg
  let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
  have defined : Defined_d M (fun p => M.mem p A) := ⟨1,φ,⟨fun _ => A,fun _ => A⟩,fun _ => Iff.rfl⟩
  apply Iff.trans ?_ (generic_neg_l O hZF generic defined ((family A).mp hA).2.1)
  exact exists_congr fun p => and_congr_right fun hp => (values p).trans
    ⟨fun h => h.2.2,fun h => ⟨(generic.proper p hp).1,(generic.proper p hp).2,h⟩⟩

theorem ropen_hit_sup_l (algebra : BooleanZF.Order_d I K S)
    {D V : M.Domain} (sub : M.MemberSubset D K) (sup : BooleanZF.Bsup_d I K S D V) :
    (∃ p, G p ∧ M.mem p V) ↔ ∃ A, M.mem A D ∧ ∃ p, G p ∧ M.mem p A := by
  obtain ⟨U,union,values⟩ := ropen_sup_values_l hZF O family order algebra sub sup
  constructor
  · rintro ⟨p,hp,pV⟩
    obtain ⟨q,hq,qU⟩ := generic.meets p hp U ((values p).mp pV).2.2
    obtain ⟨A,ha,qa⟩ := (union q).mp qU
    exact ⟨A,ha,q,hq,qa⟩
  · rintro ⟨A,ha,p,hp,pa⟩
    exact ⟨p,hp,((order A V).mp (sup.2.1 A ha)).2.2 p pa⟩

end YesMetaZFC.Model.Forcing.Internal
