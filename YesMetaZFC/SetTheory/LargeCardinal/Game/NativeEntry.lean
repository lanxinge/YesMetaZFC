import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.Descriptive.Coding.Prefix

/-! # 完整原前缀随同一次真实落子精确追加

背景每个取值先读成原历史中的真实事件。旧事件沿历史包含保持，控制记录
给出新历史中的事件唯一性；根图单射性再把取值相等读回原字母表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem Tg_prefix_d.event_l {X R k A z p f : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (C : (smdl_structure_l I (R := R) nx).Domain)
    (ct : (smdl_structure_l I (R := R) nx).TransitiveSet C)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (c b h : (rt_model_l C nc).Domain)
    (prior : Tg_prefix_d I k A X R C.val c.val.val b.val.val h.val.val z p f)
    {i x : M.Domain} (value : Rd_entry_d i x f) :
    ∃ n y : (rt_model_l C nc).Domain, M.PairMember I i n.val.val z ∧
      M.PairMember I x y.val.val p ∧ Tg_event_d J c n b h y := by
  obtain ⟨fn,s,play,graph⟩ := prior
  obtain ⟨n,y,hin,hxy,val⟩ := (graph i x (fn.bound_l value).1 (fn.bound_l value).2).mp value
  let N := smdl_structure_l I (R := R) nx
  let sn : N.Domain := ⟨s,(val.bounds_l I).2.2⟩
  let nn : N.Domain := ⟨n,(val.bounds_l I).1⟩
  let yn : N.Domain := ⟨y,(val.bounds_l I).2.1⟩
  have hs : N.mem sn C := play.member_l I
  have native := (rf_val_native_l I nx ext nn yn sn).mp val
  have members := rd_entry_transitive_l ct hs native
  let sp : (rt_model_l C nc).Domain := ⟨sn,hs⟩
  let np : (rt_model_l C nc).Domain := ⟨nn,members.1⟩
  let yp : (rt_model_l C nc).Domain := ⟨yn,members.2⟩
  exact ⟨np,yp,hin,hxy,(tg_play_native_l I nx ext C ct nc J c b h sp).mp play np yp
    ((rt_entry_l ct nc ext np yp sp).mpr native)⟩

variable (hZF : M.Models ZF)
local notation "K" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_prefix_d.append_l {Ω X R k m A z p f g y₀ : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l K (R := R) nx))
    (C : (smdl_structure_l K (R := R) nx).Domain)
    (ct : (smdl_structure_l K (R := R) nx).TransitiveSet C)
    (nc : Nonempty {x : (smdl_structure_l K (R := R) nx).Domain //
      (smdl_structure_l K (R := R) nx).mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc))
    (θ ε : Env (rt_model_l C nc) 46) (y : (rt_model_l C nc).Domain)
    (issued : Formula.satisfies ε tg_issued0_m)
    (head : ∀ i : Fin 19, ε.bound (i.castAdd 27) = θ.bound (i.castAdd 27))
    (left : Tg_prefix_d K k A X R C.val (θ.bound 4).val.val (θ.bound 3).val.val (θ.bound 20).val.val z p f)
    (right : Tg_prefix_d K m A X R C.val (ε.bound 4).val.val (ε.bound 3).val.val (ε.bound 20).val.val z p g)
    (numbers : M.IsSetFunction K z) (root : M.IsSetInjective K p)
    (hΩ : M.IsOmega Ω) (hk : M.mem k Ω) (succ : M.SuccessorOf m k)
    (keep : (smdl_structure_l K (R := R) nx).MemberSubset (θ.bound 20).val (ε.bound 20).val)
    (point : M.PairMember K k (θ.bound 19).val.val z) (played : M.PairMember K y₀ y.val.val p)
    (event : Tg_event_d J (θ.bound 4) (θ.bound 19) (θ.bound 3) (ε.bound 20) y) :
    Fseq_end_d K Ω g f y₀ := by
  have ep := rt_model_ext_l ext ct nc
  have state := (tg_issued_sat_l J ep ε).mp issued
  have e₄ : ε.bound 4 = θ.bound 4 := head 4
  have e₃ : ε.bound 3 = θ.bound 3 := head 3
  have sub : M.MemberSubset f g := by
    intro q hq
    obtain ⟨i,hi,x,hx,pair⟩ := left.1.1 q hq
    have value : Rd_entry_d i x f := ⟨q,pair,hq⟩
    obtain ⟨x',_,value'⟩ := right.1.2.1 i ((succ i).mpr (Or.inl hi))
    obtain ⟨n,u,hin,hxu,old⟩ := left.event_l K nx ext C ct nc J
      (θ.bound 4) (θ.bound 3) (θ.bound 20) value
    obtain ⟨n',u',hin',hx'u',new⟩ := right.event_l K nx ext C ct nc J
      (ε.bound 4) (ε.bound 3) (ε.bound 20) value'
    have eqn : n' = n := Subtype.ext (Subtype.ext (numbers.2 i n'.val.val n.val.val hin' hin))
    subst n'
    have old := old.mono_l J (fun a ha => keep a.val ha)
    have old : Tg_event_d J (ε.bound 4) n (ε.bound 3) (ε.bound 20) u := by
      simpa only [e₄,e₃] using old
    have eq := congrArg (fun a => a.val.val)
      (tg_control_event_unique_l J ep _ state.control state.history old new)
    have same := root x x' u'.val.val (eq ▸ hxu) hx'u'
    obtain ⟨r,pr,hr⟩ := (show Rd_entry_d i x g from same.symm ▸ value')
    exact (kpair_unique_l M hZF.1 pr pair) ▸ hr
  obtain ⟨x,_,value⟩ := right.1.2.1 k succ.predecessor_mem
  obtain ⟨n,u,hkn,hxu,actual⟩ := right.event_l K nx ext C ct nc J
    (ε.bound 4) (ε.bound 3) (ε.bound 20) value
  have eqn : n = θ.bound 19 := Subtype.ext (Subtype.ext (numbers.2 k n.val.val (θ.bound 19).val.val hkn point))
  subst n
  have event : Tg_event_d J (ε.bound 4) (θ.bound 19) (ε.bound 3) (ε.bound 20) y := by
    simpa only [e₄,e₃] using event
  have eq := congrArg (fun a => a.val.val)
    (tg_control_event_unique_l J ep _ state.control state.history actual event)
  have last : Rd_entry_d k y₀ g := (root x y₀ y.val.val (eq ▸ hxu) played) ▸ value
  obtain ⟨m',next,hm'⟩ := hΩ.1.2 k hk
  have hm : M.mem m Ω := next.eq hZF.1 succ ▸ hm'
  have ff := fn0_function_l (ZF.modelsKP hZF) left.1
  have fg := fn0_function_l (ZF.modelsKP hZF) right.1
  exact ⟨m,k,⟨⟨hm,hΩ.members_areOrdinals (ZF.modelsKP hZF) m hm,fg.1,fg.2.1⟩,hk,succ,
    ⟨hk,hΩ.members_areOrdinals (ZF.modelsKP hZF) k hk,ff.1,ff.2.1⟩,
    (Descriptive.ds_restrict_iff_l K ff fg.1).mpr sub,last⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原控制历史中的求值唯一性

两份原生短图在同一反射层读回控制事件，历史函数的单值性识别字母。
该读取只要求实际原请求及原生外延性，不依赖工作复制历史。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 同一原历史的两个原生求值给出同一个字母对象码。 -/
theorem Tg_play_d.native_entry_eq_l {X R s t i x y : M.Domain}
    (nx : ∃ x, M.mem x X) (ext : Extensional (smdl_structure_l I (R := R) nx))
    (C : (smdl_structure_l I (R := R) nx).Domain)
    (ct : (smdl_structure_l I (R := R) nx).TransitiveSet C)
    (nc : Nonempty {x // (smdl_structure_l I (R := R) nx).mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc))
    (ρ : Env (rt_model_l C nc) 46) (issued : Formula.satisfies ρ tg_issued0_m)
    (left : Tg_play_d I X R C.val (ρ.bound 4).val.val (ρ.bound 3).val.val (ρ.bound 20).val.val s)
    (right : Tg_play_d I X R C.val (ρ.bound 4).val.val (ρ.bound 3).val.val (ρ.bound 20).val.val t)
    (hi : Rf_val_d I X R i x s) (hy : Rf_val_d I X R i y t) : x = y := by
  let N := smdl_structure_l I (R := R) nx
  let sn : N.Domain := ⟨s,(hi.bounds_l I).2.2⟩
  let tn : N.Domain := ⟨t,(hy.bounds_l I).2.2⟩
  let n : N.Domain := ⟨i,(hi.bounds_l I).1⟩
  let a : N.Domain := ⟨x,(hi.bounds_l I).2.1⟩
  let b : N.Domain := ⟨y,(hy.bounds_l I).2.1⟩
  have hs : N.mem sn C := left.member_l I
  have ht : N.mem tn C := right.member_l I
  have ix := (rf_val_native_l I nx ext n a sn).mp hi
  have iy := (rf_val_native_l I nx ext n b tn).mp hy
  have hx := rd_entry_transitive_l ct hs ix
  have hy := rd_entry_transitive_l ct ht iy
  have ep := rt_model_ext_l ext ct nc
  have state := (tg_issued_sat_l J ep ρ).mp issued
  have ex := (tg_play_native_l I nx ext C ct nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) ⟨sn,hs⟩).mp left
    ⟨n,hx.1⟩ ⟨a,hx.2⟩ ((rt_entry_l ct nc ext _ _ _).mpr ix)
  have ey := (tg_play_native_l I nx ext C ct nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) ⟨tn,ht⟩).mp right
    ⟨n,hx.1⟩ ⟨b,hy.2⟩ ((rt_entry_l ct nc ext _ _ _).mpr iy)
  exact congrArg (fun z => z.val.val) (tg_control_event_unique_l J ep _ state.control state.history ex ey)

end YesMetaZFC.SetTheory.LargeCardinal
