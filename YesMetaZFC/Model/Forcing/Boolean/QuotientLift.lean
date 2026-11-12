import YesMetaZFC.Model.Forcing.Boolean.QuotientDensity
import YesMetaZFC.Model.Forcing.Boolean.RegularGeneric

/-! # 将中间模型的稠密名字提升到原布尔代数

在 π(Y) 内选取首阶段条件，取得旧条件见证 Z，再取 Z∧i([q])。
伴随的相容判据保证此交非零；它同时保证首阶段接受 q，因而读出稠密集中的 Z。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def Qhit_d (Q T w c A J L V σ b : M.Domain) : Prop := ∃ q a y x t,
  Below_d M Q T w q c ∧ M.mem a A ∧ M.mem q a ∧
  (∀ U, Ropen_d Q T w U → M.mem q U → M.MemberSubset a U) ∧
  Entry_d M a y J ∧ M.mem x L ∧ Entry_d M b y V ∧ Entry_d M b x V ∧
  Check_d M c x t ∧ Mem_force_d M Q T w q t σ

include hZF

theorem qhit_defined_l (Q T w c A J L V σ : M.Domain) : Defined_d M (Qhit_d Q T w c A J L V σ) := by
  let ρ : Env M 9 := ⟨fun i => [Q,T,w,c,A,J,L,V,σ].get i,fun _ => Q⟩
  let φ : UnarySchema 9 := { body := set[10] ⟪ ∃ q, ∃ a, ∃ y, ∃ x, ∃ t,
    ⌜below_m⌝ₚ(⌜(.bound 1 : Term 10)⌝ₛ,⌜(.bound 2 : Term 10)⌝ₛ,⌜(.bound 3 : Term 10)⌝ₛ,q,⌜(.bound 4 : Term 10)⌝ₛ) ∧
    a ∈ ⌜(.bound 5 : Term 10)⌝ₛ ∧ q ∈ a ∧
    (∀ U, ⌜ropen_m⌝ₚ(⌜(.bound 1 : Term 10)⌝ₛ,⌜(.bound 2 : Term 10)⌝ₛ,⌜(.bound 3 : Term 10)⌝ₛ,U) → q ∈ U → a ⊆ U) ∧
    ⌜entry_m⌝ₚ(a,y,⌜(.bound 6 : Term 10)⌝ₛ) ∧ x ∈ ⌜(.bound 7 : Term 10)⌝ₛ ∧
    ⌜entry_m⌝ₚ(⌜(.newest : Term 10)⌝ₛ,y,⌜(.bound 8 : Term 10)⌝ₛ) ∧
    ⌜entry_m⌝ₚ(⌜(.newest : Term 10)⌝ₛ,x,⌜(.bound 8 : Term 10)⌝ₛ) ∧
    ⌜check_m⌝ₚ(⌜(.bound 4 : Term 10)⌝ₛ,x,t) ∧
    ⌜mem_force_m⌝ₚ(⌜(.bound 1 : Term 10)⌝ₛ,⌜(.bound 2 : Term 10)⌝ₛ,⌜(.bound 3 : Term 10)⌝ₛ,q,t,⌜(.bound 9 : Term 10)⌝ₛ)⟫ }
  refine ⟨9,φ,ρ,fun b => ?_⟩
  simp only [UnarySchema.denote,φ,Qhit_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff,below_sat_l M hZF.1,ropen_sat_l hZF,entry_sat_l M hZF.1,
    check_sat_l M hZF.1,mem_force_sat_l M hZF.1,Definitional.Term.eval_weaken]
  rfl

theorem quotient_dense_l {Q T w K S e u A L V d J P c τ ν σ q a y X x t : M.Domain}
    (O : Cond_order_d M Q T w)
    (family : ∀ a, M.mem a K ↔ Ropen_d Q T w a)
    (order : ∀ a b, Entry_d M a b S ↔ M.mem a K ∧ M.mem b K ∧ M.MemberSubset a b)
    (source : BooleanZF.Boolean_d I K S e) (empty : ∀ q, ¬ M.mem q e)
    (interval : BooleanZF.Bi_d I K S u A) (target : BooleanZF.Boolean_d I L V d)
    (hom : BooleanZF.Bh_d I A S e L V d J) (fn : M.IsSetFunctionFromTo I P L A)
    (adj : ∀ b a, Entry_d M b a P → BooleanZF.Badj_d I A S L V J b a)
    (hc : M.mem c Q) (name : Qname_d Q c L d P τ) (relation : Check_d M c V ν)
    (hσ : Name_d M Q σ) (check : Check_d M c x t)
    (hq : Below_d M Q T w q c) (ay : Entry_d M a y J)
    (minimal : ∀ U, Ropen_d Q T w U → M.mem q U → M.MemberSubset a U)
    (hX : M.mem X L) (Xy : Entry_d M X y V) (Xx : Entry_d M X x V) (hx : M.mem x L)
    (dense : Forces_d M Q T w (stage_dense_m (.bound 3) (.bound 2) (.bound 1) (.bound 0))
      (stage_env_l M τ ν σ t) q) : Dense_d M L V d (Qhit_d Q T w c A J L V σ) X := by
  have small := interval.boolean_l I source
  have regular a (ha : M.mem a A) := (family a).mp ((interval.carrier a).mp ha).1
  have nonempty {a} (nz : a ≠ e) : ∃ r, M.mem r a := by
    apply Classical.byContradiction
    intro no
    exact nz (hZF.1.eq_of_same_members a e (fun r => ⟨fun hr => (no ⟨r,hr⟩).elim,fun hr => (empty r hr).elim⟩))
  intro Y hY
  obtain ⟨b,hb,Yb⟩ := fn.2.2 Y hY.1
  have Yadj := adj Y b Yb
  have nz := Yadj.positive_l I small target hom.zero hY.2.1
  have by' := (Yadj.2.2 a y ay).mp (target.order.trans Y X y hY.1 hX
    (hom.function.output_mem_of_pairMember ay) hY.2.2 Xy)
  have sub := ((order b a).mp by').2.2
  obtain ⟨r,rb⟩ := nonempty nz
  obtain ⟨s,sq,sb⟩ := ropen_condition_refine_l hZF O hq.1 hq.2.1 minimal (regular b hb) sub rb
  obtain ⟨v,checkY,_,_⟩ := zf_check_l M hZF hc Y
  have sc := below_trans_l O hc sq hq
  have member := (name.force_l hZF O hc fn regular Yb checkY sc).mpr ⟨hY.2.1,sb⟩
  have named : ∀ v : Term 4, Name_d M Q (v.eval (stage_env_l M τ ν σ t)) := by
    intro v
    cases v with
    | free _ => exact name.1
    | bound i =>
      exact Fin.cases (check_name_l M (check_range_l M hZF) hc check)
        (Fin.cases hσ (Fin.cases (check_name_l M (check_range_l M hZF) hc relation) (fun _ => name.1))) i
  have lower := (forces_regular_l O hZF _ _ named).1 q s hq.1 sq dense
  obtain ⟨r,Z,tZ,rs,hZ,Zz,checkZ,memberZ,ZY,hitZ⟩ := name.dense_witness_l hZF O hc relation hσ checkY check
    (target.order.trans Y X x hY.1 hX hx hY.2.2 Xx) sc member lower
  have rc := below_trans_l O hc rs sc
  obtain ⟨bZ,hbZ,Zb⟩ := fn.2.2 Z hZ
  have rbZ := ((name.force_l hZF O hc fn regular Zb checkZ rc).mp memberZ).2
  obtain ⟨a',reg,ra,minimal'⟩ := ropen_condition_l hZF O rs.1 rs.2.1
  have sub' := minimal' bZ (regular bZ hbZ) rbZ
  have ha'K := (family a').mpr reg
  have ha' := (interval.carrier a').mpr ⟨ha'K,(order a' u).mpr ⟨ha'K,interval.bound,
    fun r hr => ((order bZ u).mp ((interval.carrier bZ).mp hbZ).2).2.2 r (sub' r hr)⟩⟩
  obtain ⟨v',hv',av⟩ := hom.function.2.2 a' ha'
  obtain ⟨m,meet⟩ := small.meet bZ a' hbZ ha'
  have global := (interval.meet_l I source hbZ ha').mp meet
  have values := ropen_meet_values_l hZF family order source ((interval.carrier bZ).mp hbZ).1 ha'K global
  have cmp := (boolean_cmp_meet_l hZF small meet).mpr (fun eq => empty r (eq ▸ (values r).mpr ⟨rbZ,ra⟩))
  obtain ⟨W,wm⟩ := target.meet Z v' hZ hv'
  have positive := (boolean_cmp_meet_l hZF target wm).mp
    ((badj_cmp_l hZF small target hom (adj Z bZ Zb) av).mpr cmp)
  have bounds := BooleanZF.meet_bounds_d I target.order wm
  exact ⟨W,⟨wm.1,positive,target.order.trans W Z Y wm.1 hZ hY.1 bounds.1 ZY⟩,
    r,a',v',Z,tZ,rc,ha',ra,minimal',av,hZ,bounds.2,bounds.1,checkZ,hitZ⟩

end YesMetaZFC.Model.Forcing.Internal
