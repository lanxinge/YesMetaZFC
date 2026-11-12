import YesMetaZFC.Model.Forcing.Boolean.IntermediateQuotient
import YesMetaZFC.Model.Forcing.Boolean.RegularValues
import YesMetaZFC.Model.Forcing.Boolean.ConditionValue
import YesMetaZFC.SetTheory.Boolean.Adjoint
import YesMetaZFC.SetTheory.Boolean.Interval

/-! # 商条件的规范投影判据

伴随律将目标中的相容性化为源中的相容性。对于实际正则开泛型，
与全部被接受元素相容等价于自身被接受，从而消去商定义中的全称相容条件。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem boolean_cmp_meet_l {A R z a b m : M.Domain} (h : BooleanZF.Boolean_d I A R z)
    (meet : BooleanZF.Meet_d I A R a b m) : Cmp_d M A R z a b ↔ m ≠ z := by
  constructor
  · rintro ⟨r,hr,rb⟩ eq
    have rm := (meet.2 r hr.1).mpr ⟨hr.2.2,rb⟩
    exact hr.2.1 (h.order.antisymm r z hr.1 h.bot_mem (eq ▸ rm) (h.bot_le r hr.1))
  · intro nz
    have bounds := BooleanZF.meet_bounds_d I h.order meet
    exact ⟨m,⟨meet.1,nz,bounds.1⟩,bounds.2⟩

theorem badj_cmp_l {A R z B S w F b a c y : M.Domain}
    (L : BooleanZF.Boolean_d I A R z) (K : BooleanZF.Boolean_d I B S w)
    (h : BooleanZF.Bh_d I A R z B S w F) (ba : BooleanZF.Badj_d I A R B S F b a)
    (cy : Entry_d M c y F) : Cmp_d M B S w b y ↔ Cmp_d M A R z a c := by
  have hc := h.function.input_mem_of_pairMember cy
  have hy := h.function.output_mem_of_pairMember cy
  obtain ⟨n,cn⟩ := L.imp c z hc L.bot_mem
  obtain ⟨t,ht,nt⟩ := h.function.2.2 n cn.1
  have yt := h.neg c n y t cy nt cn
  obtain ⟨m,bm⟩ := K.meet b y ba.1 hy
  obtain ⟨d,ad⟩ := L.meet a c ba.2.1 hc
  obtain ⟨y',ty⟩ := K.imp t w ht K.bot_mem
  have ty : BooleanZF.Imp_d I B S t w y := K.double_neg y t y' hy yt ty ▸ ty
  obtain ⟨c',nc⟩ := L.imp n z cn.1 L.bot_mem
  have nc : BooleanZF.Imp_d I A R n z c := L.double_neg c n c' hc cn nc ▸ nc
  have zeros : m = w ↔ d = z :=
    (K.neg_test_l I ba.1 ht ty bm).symm.trans ((ba.2.2 n t nt).trans (L.neg_test_l I ba.2.1 cn.1 nc ad))
  exact (boolean_cmp_meet_l hZF K bm).trans ((not_congr zeros).trans (boolean_cmp_meet_l hZF L ad).symm)

variable {Q T w K S e : M.Domain} (O : Cond_order_d M Q T w)
  (family : ∀ a, M.mem a K ↔ Ropen_d Q T w a)
  (order : ∀ a b, Entry_d M a b S ↔ M.mem a K ∧ M.mem b K ∧ M.MemberSubset a b)
  (algebra : BooleanZF.Boolean_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) K S e)
  (empty : ∀ q, ¬ M.mem q e)
  {H : M.Domain → Prop} (generic : Generic_d M Q T w H)
include O family order algebra empty generic

omit O in
theorem ropen_hit_cmp_l {a b : M.Domain} (ha : M.mem a K) (hb : M.mem b K)
    (hitA : ∃ q, H q ∧ M.mem q a) (hitB : ∃ q, H q ∧ M.mem q b) : Cmp_d M K S e a b := by
  obtain ⟨m,meet⟩ := algebra.meet a b ha hb
  have inter := ropen_meet_values_l hZF family order algebra ha hb meet
  obtain ⟨q,_,qm⟩ := (ropen_hit_inter_l ((family a).mp ha) ((family b).mp hb) inter generic).mpr ⟨hitA,hitB⟩
  exact (boolean_cmp_meet_l hZF algebra meet).mpr (fun eq => empty q (eq ▸ qm))

theorem ropen_hit_iff_all_cmp_l {a : M.Domain} (ha : M.mem a K) :
    (∃ q, H q ∧ M.mem q a) ↔ ∀ c, M.mem c K → (∃ q, H q ∧ M.mem q c) → Cmp_d M K S e a c := by
  refine ⟨fun hit c hc hhit => ropen_hit_cmp_l hZF family order algebra empty generic ha hc hit hhit,?_⟩
  intro all
  apply Classical.byContradiction
  intro no
  obtain ⟨n,neg⟩ := algebra.imp a e ha algebra.bot_mem
  have hit := (ropen_hit_neg_l hZF O family order generic algebra empty ha neg).mpr no
  obtain ⟨r,hr,rn⟩ := all n neg.1 hit
  exact hr.2.1 (algebra.disjoint_l I ha hr.1 neg hr.2.2 rn)

theorem ropen_interval_hit_neg_l {u A a n : M.Domain} (interval : BooleanZF.Bi_d I K S u A)
    (hit : ∃ q, H q ∧ M.mem q u) (ha : M.mem a A) (neg : BooleanZF.Imp_d I A S a e n) :
    (∃ q, H q ∧ M.mem q n) ↔ ¬ ∃ q, H q ∧ M.mem q a := by
  obtain ⟨v,av⟩ := algebra.imp a e ((interval.carrier a).mp ha).1 algebra.bot_mem
  obtain ⟨m,meet⟩ := algebra.meet u v interval.bound av.1
  have eq := (interval.imp_l I algebra ha av meet).unique_l I (interval.boolean_l I algebra).order neg
  subst m
  have inter := ropen_meet_values_l hZF family order algebra interval.bound av.1 meet
  exact (ropen_hit_inter_l ((family u).mp interval.bound) ((family v).mp av.1) inter generic).trans
    ((and_iff_right hit).trans (ropen_hit_neg_l hZF O family order generic algebra empty ((interval.carrier a).mp ha).1 av))

theorem ropen_interval_hit_iff_all_cmp_l {u A a : M.Domain} (interval : BooleanZF.Bi_d I K S u A)
    (hit : ∃ q, H q ∧ M.mem q u) (ha : M.mem a A) :
    (∃ q, H q ∧ M.mem q a) ↔ ∀ c, M.mem c A → (∃ q, H q ∧ M.mem q c) → Cmp_d M A S e a c := by
  have L := interval.boolean_l I algebra
  constructor
  · intro hhit c hc chit
    obtain ⟨m,meet⟩ := L.meet a c ha hc
    have global := (interval.meet_l I algebra ha hc).mp meet
    have cmp := ropen_hit_cmp_l hZF family order algebra empty generic
      ((interval.carrier a).mp ha).1 ((interval.carrier c).mp hc).1 hhit chit
    exact (boolean_cmp_meet_l hZF L meet).mpr ((boolean_cmp_meet_l hZF algebra global).mp cmp)
  · intro all
    apply Classical.byContradiction
    intro no
    obtain ⟨n,neg⟩ := L.imp a e ha L.bot_mem
    have nhit := (ropen_interval_hit_neg_l hZF O family order algebra empty generic interval hit ha neg).mpr no
    obtain ⟨r,hr,rn⟩ := all n neg.1 nhit
    exact hr.2.1 (L.disjoint_l I ha hr.1 neg hr.2.2 rn)

theorem Qread_d.projection_l {N : Structure.{v}} {j : M.Domain → N.Domain} (inj : Function.Injective j)
    {u A L V d J x a : M.Domain} {D : N.Domain} (interval : BooleanZF.Bi_d I K S u A)
    (hit : ∃ q, H q ∧ M.mem q u) (target : BooleanZF.Boolean_d I L V d)
    (hom : BooleanZF.Bh_d I A S e L V d J) (read : Qread_d j H A L V d J D)
    (xa : BooleanZF.Badj_d I A S L V J x a) :
    N.mem (j x) D ↔ x ≠ d ∧ ∃ q, H q ∧ M.mem q a := by
  have source := interval.boolean_l I algebra
  have accept := ropen_interval_hit_iff_all_cmp_l hZF O family order algebra empty generic interval hit xa.2.1
  constructor
  · intro hx
    obtain ⟨y,_,yz,eq,all⟩ := (read (j x)).mp hx
    have eq := inj eq
    subst y
    refine ⟨yz,accept.mpr (fun c hc chit => ?_)⟩
    obtain ⟨v,_,cv⟩ := hom.function.2.2 c hc
    exact (badj_cmp_l hZF source target hom xa cv).mp (all c v hc chit cv)
  · rintro ⟨nz,hitA⟩
    exact (read (j x)).mpr ⟨x,xa.1,nz,rfl,fun c v hc chit cv =>
      (badj_cmp_l hZF source target hom xa cv).mpr (accept.mp hitA c hc chit)⟩

end YesMetaZFC.Model.Forcing.Internal
