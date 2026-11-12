import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.Forcing.Names.SequenceForcing
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.SetTheory.Ord.IncreasingCover
import YesMetaZFC.Model.Forcing.Collapse.ProductTopTruth
import YesMetaZFC.Model.Forcing.Functions.Generic
import YesMetaZFC.Model.Forcing.Homogeneous.HOD
import YesMetaZFC.Model.Forcing.Ground.Ordinals
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffModelMinimum
import YesMetaZFC.Model.Forcing.Order.QueryAttempt
import YesMetaZFC.Model.SetTheory.Images.BinaryImage

/-! # 指定阶段的实数集解释及单调性

单个规范阶段名字恰好包含拥有该阶段名字的全部实数。名字补长保持原
全泛型解释，故阶段实数集随内部自然数增长；不改变任何前缀泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rn_d.product_value_l {ω A P R W n C S b r : M.Domain}
    (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    (stage : Fp_stage_d hZF ω A n C S b) (hn : M.mem n ω) (name : Rn_d I C S b ω r)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain) (ground : ∀ a, Gval_d M P R P G a (j a))
    {Y : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Y) :
    ∀ x, x ∈ Y ↔ Fn0_d (j ω) (j ω) x ∧ ∃ τ, Name_d M C τ ∧ Qval_d M P R P G τ x := by
  let E := extension_l M hZF P R P G
  let H : M.Domain → Prop := fun p => M.mem p C ∧ G p
  let D := extension_l M hZF C S C H
  obtain ⟨small,e,ei,ef,keep,base⟩ := stage.stage.extension_l hZF product hw hn fa generic
  have hD : D.Models ZF := preserves_zf_l (stage.stage.order_l hZF) hZF small
  have hE : E.Models ZF := preserves_zf_l (product.order_l hZF) hZF generic
  obtain ⟨p,hp⟩ := small.inhabited
  have hb := small.upward p b hp stage.member (stage.top p (small.proper p hp).1)
  obtain ⟨_,_,_,data⟩ := name
  obtain ⟨k,groundK,B,vB,reals⟩ := data.value_l hZF (stage.stage.order_l hZF) small hb
  have commute a : e (k a) = j a := (base a (k a) (groundK a)).unique_l (product.order_l hZF) hZF generic (ground a)
  have eB : e B = Y := qval_unique_l (keep B r vB) value
  have function (x : D.Domain) : Fn0_d (k ω) (k ω) x ↔ Fn0_d (j ω) (j ω) (e x) := by
    let ρ : Env D 3 := ⟨fun i => [k ω,k ω,x].get i,fun _ => x⟩
    have tr := (fn0_sat_l hD.1 ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      ((delta0_image_l e ei ef (fn0_delta_l ..) ρ).trans (fn0_sat_l hE.1 _ _ _ _))
    change Fn0_d (k ω) (k ω) x ↔ Fn0_d (e (k ω)) (e (k ω)) (e x) at tr
    simpa only [commute] using tr
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy,eq⟩ := (ef B x).mp (eB.symm ▸ hx)
    obtain ⟨τ,nt,vy⟩ := value_name_l y
    exact ⟨eq ▸ (function y).mp ((reals y).mp hy),τ,nt,eq ▸ keep y τ vy⟩
  · rintro ⟨fn,τ,nt,vx⟩
    obtain ⟨y,vy⟩ := name_value_l (R := S) (z := C) (U := H) nt
    have eq : e y = x := qval_unique_l (keep y τ vy) vx
    exact eB ▸ (ef B x).mpr ⟨y,(reals y).mpr ((function y).mpr (eq.symm ▸ fn)),eq⟩

theorem Rp_part_d.monotone_l {ω A P R W n m r s : M.Domain}
    (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    (hn : M.mem n ω) (hm : M.mem m ω) (sub : M.MemberSubset n m)
    (left : Rp_part_d hZF ω A n r) (right : Rp_part_d hZF ω A m s)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain) (ground : ∀ a, Gval_d M P R P G a (j a))
    {Y Z : (extension_l M hZF P R P G).Domain}
    (vy : Qval_d M P R P G r Y) (vz : Qval_d M P R P G s Z) : ∀ x, x ∈ Y → x ∈ Z := by
  obtain ⟨C,S,b,stage,rn⟩ := left
  obtain ⟨D,T,d,later,sn⟩ := right
  intro x hx
  obtain ⟨fn,τ,nt,vx⟩ := (rn.product_value_l hZF hw fa product stage hn generic j ground vy x).mp hx
  obtain ⟨σ,ns,value⟩ := stage.stage.name_extend_l hZF hw hn hm fa product later.stage sub generic nt vx
  exact (sn.product_value_l hZF hw fa product later hm generic j ground vz x).mpr ⟨fn,σ,ns,value⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原泛型扩张中的实际阶段实数集序列

地模型的规范阶段名字函数经逐坐标名字装配，得到扩张内的一张集合函数图。
其各项是原前缀实数集，递增且并为原规范实数并。内部有限归纳可直接以
此图为集合参数，无需把外部阶段谓词放入分离模式。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rp_name_d.stages_l {ω A P R W r : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain) (ground : ∀ a, Gval_d M P R P G a (j a))
    {Z : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Z) :
    let E := extension_l M hZF P R P G
    ∃ V F : E.Domain, Fn0_d (j ω) V F ∧
      (∀ n Y, Entry_d E (j n) Y F ↔ M.mem n ω ∧ ∃ s, Rp_part_d hZF ω A n s ∧ Qval_d M P R P G s Y) ∧
      (∀ x, x ∈ Z ↔ ∃ n, n ∈ j ω ∧ ∃ Y, Entry_d E n Y F ∧ x ∈ Y) ∧
      ∀ n m Y T, n ∈ j ω → m ∈ j ω → (∀ a, a ∈ n → a ∈ m) →
        Entry_d E n Y F → Entry_d E m T F → ∀ x, x ∈ Y → x ∈ T := by
  dsimp only
  let E := extension_l M hZF P R P G
  have O := product.order_l hZF
  have hE : E.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨D,f,ff,entries,_⟩ := rp_parts_l hZF hw fa product
  have names n s (hn : M.mem n ω) (part : Rp_part_d hZF ω A n s) : Name_d M P s := by
    obtain ⟨C,S,b,stage,_,_,_,data⟩ := part
    exact name_conditions_mono_l
      (fun p hp => ((stage.stage.product_read_l hZF product hn).1 p).mp hp |>.1) data.name
  obtain ⟨p,hp⟩ := generic.inhabited
  obtain ⟨j₀,checks,full,inj⟩ := check_map_l O hZF generic hp
  have same : j₀ = j := funext fun a => (gval_check_map_l O hZF generic hp j₀ checks a (j a)).mp (ground a)
  subst j₀
  obtain ⟨t,nt⟩ := nseq_exists_l M hZF (generic.proper p hp).1 ff
    (fun n s ns => names n s ((entries n s).mp ns).1 ((entries n s).mp ns).2)
  obtain ⟨F,vF⟩ := name_value_l (R := R) (z := P) (U := G) nt.1
  obtain ⟨rel,read⟩ := nseq_value_l O hZF generic (generic.proper p hp).1 nt vF j checks
  have total a (ha : a ∈ j ω) : ∃ Y, Entry_d E a Y F := by
    obtain ⟨n,hn,rfl⟩ := (full ω a).mp ha
    obtain ⟨s,_,ns⟩ := ff.2.2 n hn
    obtain ⟨Y,vY⟩ := name_value_l (R := R) (z := P) (U := G)
      (names n s hn ((entries n s).mp ns).2)
    exact ⟨Y,(read (j n) Y).mpr ⟨n,s,ns,rfl,vY⟩⟩
  have bound a Y (ay : Entry_d E a Y F) : a ∈ j ω := by
    obtain ⟨n,s,ns,rfl,_⟩ := (read a Y).mp ay
    exact (image_member_l j inj full).mpr (ff.input_mem_of_pairMember ns)
  have unique a Y T (ay : Entry_d E a Y F) (at' : Entry_d E a T F) : Y = T := by
    obtain ⟨n,s,ns,en,vs⟩ := (read a Y).mp ay
    obtain ⟨m,t,mt,em,vt⟩ := (read a T).mp at'
    have eq := inj (en.trans em.symm)
    subst m
    have eq := ff.1.2 n s t ns mt
    subst t
    exact qval_unique_l vs vt
  have function : E.IsSetFunction (kp_pair_l (ZF.modelsKP hE)) F := ⟨rel,unique⟩
  have domain : E.IsDomainOf (kp_pair_l (ZF.modelsKP hE)) (j ω) F := fun a => ⟨total a,fun ⟨Y,ay⟩ => bound a Y ay⟩
  obtain ⟨V,range⟩ := ZF.exists_range_of_setFunction hE (kp_pair_l (ZF.modelsKP hE)) function domain
  have fn : Fn0_d (j ω) V F := fn0_of_function_l (ZF.modelsKP hE) ⟨function,domain,fun a ha => by
    obtain ⟨Y,ay⟩ := total a ha
    exact ⟨Y,(range Y).mpr ⟨a,ay⟩,ay⟩⟩
  have stages n Y : Entry_d E (j n) Y F ↔ M.mem n ω ∧ ∃ s, Rp_part_d hZF ω A n s ∧ Qval_d M P R P G s Y := by
    constructor
    · intro h
      obtain ⟨m,s,ms,eq,vs⟩ := (read (j n) Y).mp h
      have eq := inj eq
      subst m
      exact ⟨((entries n s).mp ms).1,s,((entries n s).mp ms).2,vs⟩
    · rintro ⟨hn,s,part,vs⟩
      exact (read (j n) Y).mpr ⟨n,s,(entries n s).mpr ⟨hn,part⟩,rfl,vs⟩
  refine ⟨V,F,fn,stages,?_,?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨τ,q,⟨v,pair,vr⟩,gq,vx⟩ := (qval_mem_l O hZF generic value).mp hx
      obtain ⟨n,s,hn,part,vs⟩ := (name.members v).mp vr
      obtain ⟨Y,vY⟩ := name_value_l (R := R) (z := P) (U := G) (names n s hn part)
      exact ⟨j n,(image_member_l j inj full).mpr hn,Y,(stages n Y).mpr ⟨hn,s,part,vY⟩,
        (qval_mem_l O hZF generic vY).mpr ⟨τ,q,⟨v,pair,vs⟩,gq,vx⟩⟩
    · rintro ⟨a,ha,Y,ay,xy⟩
      obtain ⟨n,hn,rfl⟩ := (full ω a).mp ha
      obtain ⟨_,s,part,vY⟩ := (stages n Y).mp ay
      obtain ⟨τ,q,⟨v,pair,vs⟩,gq,vx⟩ := (qval_mem_l O hZF generic vY).mp xy
      exact (qval_mem_l O hZF generic value).mpr
        ⟨τ,q,⟨v,pair,(name.members v).mpr ⟨n,s,hn,part,vs⟩⟩,gq,vx⟩
  · intro a b Y T ha hb sub ay bt x hx
    obtain ⟨n,hn,rfl⟩ := (full ω a).mp ha
    obtain ⟨m,hm,rfl⟩ := (full ω b).mp hb
    obtain ⟨_,s,left,vs⟩ := (stages n Y).mp ay
    obtain ⟨_,t,right,vt⟩ := (stages m T).mp bt
    exact left.monotone_l hZF hw fa product hn hm
      (fun a ha => (image_member_l j inj full).mp (sub (j a) ((image_member_l j inj full).mpr ha)))
      right generic j ground vs vt x hx

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全部内部有限实数参数列的共同前缀名字

实际阶段实数集序列给出内部有限列的统一阶段界。整列取值落在该阶段
实数集的像中，成员满嵌入的有限列反射遂把参数列整体回收到该前缀扩张，
再取其真实名字。内部长度无需外部标准。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rp_name_d.sequence_prefix_l {ω A P R W r : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain) (ground : ∀ a, Gval_d M P R P G a (j a))
    {Z k s : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Z)
    (hk : k ∈ j ω) (seq : Fn0_d k Z s) :
    ∃ n C S b τ, M.mem n ω ∧ Fp_stage_d hZF ω A n C S b ∧ Name_d M C τ ∧ Qval_d M P R P G τ s := by
  let E := extension_l M hZF P R P G
  have O := product.order_l hZF
  have hE : E.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨p,hp⟩ := generic.inhabited
  obtain ⟨j₀,checks,jf,ji⟩ := check_map_l O hZF generic hp
  have same : j₀ = j := funext fun a => (gval_check_map_l O hZF generic hp j₀ checks a (j a)).mp (ground a)
  subst j₀
  have omega : E.IsOmega (j ω) := image_omega_l (hEN := hE.1) j ji jf hZF
    (internal_foundation_l O hZF generic) hw (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (j ω))
  obtain ⟨V,F,fn,stages,union,mono⟩ := name.stages_l hZF hw fa product generic j ground value
  obtain ⟨a,ha,Y,ay,cover⟩ := increasing_finite_cover_l hE omega fn (fun x hx => (union x).mp hx) mono hk seq
  obtain ⟨n,hn,rfl⟩ := (jf ω a).mp ha
  obtain ⟨_,u,⟨C,S,b,stage,D₀,t,W₀,data⟩,vu⟩ := (stages n Y).mp ay
  let H : M.Domain → Prop := fun p => M.mem p C ∧ G p
  let D := extension_l M hZF C S C H
  obtain ⟨small,e,ei,ef,keep,base⟩ := stage.stage.extension_l hZF product hw hn fa generic
  have hD : D.Models ZF := preserves_zf_l (stage.stage.order_l hZF) hZF small
  obtain ⟨q,hq⟩ := small.inhabited
  have hb := small.upward q b hq stage.member (stage.top q (small.proper q hq).1)
  obtain ⟨l,groundL,B,vB,_⟩ := data.value_l hZF (stage.stage.order_l hZF) small hb
  have eB : e B = Y := qval_unique_l (keep B u vB) vu
  have commute a : e (l a) = j a := (base a (l a) (groundL a)).unique_l O hZF generic (ground a)
  obtain ⟨l₀,checkL,lf,li⟩ := check_map_l (stage.stage.order_l hZF) hZF small hq
  have same : l₀ = l := funext fun a => (gval_check_map_l (stage.stage.order_l hZF) hZF small hq l₀ checkL a (l a)).mp (groundL a)
  subst l₀
  have omegaD : D.IsOmega (l ω) := image_omega_l (hEN := hD.1) l li lf hZF
    (internal_foundation_l (stage.stage.order_l hZF) hZF small) hw
    (fun T => KP.difference_exists_d (ZF.modelsKP hD) T (l ω))
  have fs := fn0_function_l (ZF.modelsKP hE) seq
  have bounded : E.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hE)) s k (e B) := by
    refine ⟨fs.1,fs.2.1,fun i hi => ?_⟩
    obtain ⟨x,_,ix⟩ := seq.2.1 i hi
    exact ⟨x,eB.symm ▸ cover i x hi ix,ix⟩
  obtain ⟨_,s₀,_,_,_,eq⟩ := image_finite_function_pull_l hD hE e ei ef omegaD
    (by simpa only [commute] using omega) (by simpa only [commute] using hk) bounded
  obtain ⟨τ,nt,vt⟩ := value_name_l s₀
  exact ⟨n,C,S,b,τ,hn,stage,nt,eq ▸ keep s₀ τ vt⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 固定前缀泛型后的尾部全局判定

原前缀泛型命中实际定义的判定集。前缀中的加强否定经尾部消去反射为
全乘积力迫否定，所得同一个判定对全部延伸此前缀的尾部泛型同时有效。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Rp_name_d.prefix_decides_l {ω A P R r n C S b : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunction I A) (product : Fp_product_d hZF ω A P R)
    (stage : Fp_stage_d hZF ω A n C S b) (hn : M.mem n ω)
    {H : M.Domain → Prop} (small : Generic_d M C S C H)
    {a k} (φ : Formula a k) (closed : φ.FreeClosed) (ρ : Env M k)
    (params : ∀ i, ρ.bound i = r ∨ Name_d M C (ρ.bound i)) :
    ∃ a, H a ∧ (Forces_d M P R P φ ρ a ∨ Forces_d M P R P (.neg φ) ρ a) := by
  rcases generic_decide_l (stage.stage.order_l hZF) hZF small (forces_defined_l M P R P φ closed ρ) with yes | no
  · obtain ⟨a,ha,forced⟩ := yes
    exact ⟨a,ha,Or.inl forced⟩
  · obtain ⟨a,ha,no⟩ := no
    refine ⟨a,ha,Or.inr ((forces_neg_l hZF.1 φ ρ a).mpr ?_)⟩
    intro p pa forced
    obtain ⟨m,_,fp⟩ := (product.conditions p).mp pa.1
    have aa := (stage.stage.conditions a).mp (small.proper a ha).1
    have le := ((product.order p a).mp pa.2.2).2.2
    obtain ⟨c,cut,fc⟩ := fp.restrict_l hZF (le.domain_l I fp aa)
    have hc := (stage.stage.conditions c).mpr fc
    have ca : Entry_d M c a S := (stage.stage.order c a).mpr ⟨hc,(small.proper a ha).1,fun i s is => by
      obtain ⟨t,it,st⟩ := le i s is
      exact ⟨t,(cut.2 i t).mpr ⟨(aa.domain i).mpr ⟨s,is⟩,it⟩,st⟩⟩
    exact no c ⟨hc,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ hc),ca⟩
      ((name.tail_reduce_l hZF hw fa product stage hn φ closed ρ params pa.1 hc cut).mp forced)

/-- 判定见证只来自原前缀滤子；其真值同时覆盖全部实际尾部延伸。 -/
theorem Rp_name_d.prefix_global_l {ω A P R r n C S b : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunction I A) (product : Fp_product_d hZF ω A P R)
    (stage : Fp_stage_d hZF ω A n C S b) (hn : M.mem n ω)
    {H : M.Domain → Prop} (small : Generic_d M C S C H)
    {k} (φ : Formula 1 k) (closed : φ.FreeClosed) (ρ : Env M k)
    (params : ∀ i, ρ.bound i = r ∨ Name_d M C (ρ.bound i)) :
    ∃ a, H a ∧ (Forces_d M P R P φ ρ a ∨ Forces_d M P R P (.neg φ) ρ a) ∧
      ∀ G, Generic_d M P R P G → (∀ p, H p → G p) →
      ∀ η : Env (extension_l M hZF P R P G) k,
        (∀ i, Qval_d M P R P G (ρ.bound i) (η.bound i)) →
        (Formula.satisfies η φ ↔ Forces_d M P R P φ ρ a) := by
  obtain ⟨a,ha,decision⟩ := name.prefix_decides_l hZF hw fa product stage hn small φ closed ρ params
  refine ⟨a,ha,decision,fun G generic contains η values => ?_⟩
  have truth := forcing_closed_truth_l hZF (product.order_l hZF) generic φ closed ρ η values
  refine ⟨fun valid => decision.elim id (fun negative => ?_),fun forced => truth.mp ⟨a,contains a ha,forced⟩⟩
  have neg := (forcing_closed_truth_l hZF (product.order_l hZF) generic (.neg φ) closed ρ η values).mp
    ⟨a,contains a ha,negative⟩
  exact (neg valid).elim

end YesMetaZFC.Model.Forcing.Internal

/-! ## 尾部齐性恢复可定义旧集合子集的前缀名字

先在地模型内构造加权名字：子名字是旧集合元素的检查名字，权重只取
给定前缀中的条件，正文由全乘积的原力迫关系分离。前缀全局判定保证
每条真实成员关系已由此前缀泛型中的条件决定。因此同一个构造名字
在每个全乘积泛型中准确解释为指定可定义子集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 规范实数并加原前缀名字作参数时，旧集合中的可定义子集已有前缀名字。
名字在选择泛型之前实际构造；不假定目标子集已在前缀扩张中。 -/
theorem Rp_name_d.prefix_subset_l {ω A P R W r n C S b : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    (stage : Fp_stage_d hZF ω A n C S b) (hn : M.mem n ω)
    {d} (φ : UnarySchema d) (ρ : Env M d)
    (params : ∀ i, ρ.bound i = r ∨ Name_d M C (ρ.bound i)) (D : M.Domain) :
    ∃ σ, Name_d M C σ ∧ ∀ G, Generic_d M P R P G →
      ∀ j : M.Domain → (extension_l M hZF P R P G).Domain,
        (∀ a, Gval_d M P R P G a (j a)) →
      ∀ η : Env (extension_l M hZF P R P G) d,
        (∀ i, Qval_d M P R P G (ρ.bound i) (η.bound i)) →
      ∀ Y : (extension_l M hZF P R P G).Domain,
        (∀ y, y ∈ Y → y ∈ j D) →
        (∀ a, M.mem a D → (φ.denote η (j a) ↔ j a ∈ Y)) → Qval_d M P R P G σ Y := by
  obtain ⟨K,checks,names⟩ := check_image_l hZF stage.member D
  let δ := (ρ.push P).push R
  let ψ : BinarySchema (d+2) := {
    body := force_at_m φ.body (Fin.cases (.bound 1) (fun i => .bound i.succ.succ.succ.succ))
      (.bound 3) (.bound 2) (.bound 3) .newest
    freeClosed := force_at_closed_l _ _ _ _ _ _ φ.freeClosed
      (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl }
  have sat s p : ψ.denote δ s p ↔ Forces_d M P R P φ.body (ρ.push s) p := by
    let f : Fin (d+1) → Term (d+4) := Fin.cases (.bound 1) (fun i => .bound i.succ.succ.succ.succ)
    have eq : (⟨fun i => (f i).eval ((δ.push s).push p),((δ.push s).push p).free⟩ : Env M (d+1)) = ρ.push s := by
      rw [Env.mk.injEq]
      exact ⟨funext (Fin.cases rfl (fun _ => rfl)),rfl⟩
    exact (force_at_sat_l φ.body ((δ.push s).push p) f (.bound 3) (.bound 2) (.bound 3) .newest).trans
      (by change Forces_d M P R P φ.body _ p ↔ _; rw [eq])
  obtain ⟨σ,ns,_,edges⟩ := name_comp_l M hZF ψ δ C K names
  refine ⟨σ,ns,fun G generic j ground η values Y sub define => ?_⟩
  let E := extension_l M hZF P R P G
  have O := product.order_l hZF
  have hE : E.Models ZF := preserves_zf_l O hZF generic
  have cP : M.MemberSubset C P := fun p hp => ((stage.stage.product_read_l hZF product hn).1 p).mp hp |>.1
  have small := (stage.stage.extension_l hZF product hw hn fa generic).1
  obtain ⟨p,hp⟩ := small.inhabited
  have hb := small.upward p b hp stage.member (stage.top p (small.proper p hp).1)
  obtain ⟨j₀,checked,full,_⟩ := check_map_l O hZF generic hb.2
  have same : j₀ = j := funext fun a => (gval_check_map_l O hZF generic hb.2 j₀ checked a (j a)).mp (ground a)
  subst j₀
  obtain ⟨Z,value⟩ := name_value_l (R := R) (z := P) (U := G) (name_conditions_mono_l cP ns)
  have eq : Z = Y := hE.1.eq_of_same_members _ _ (fun y => by
    constructor
    · intro hy
      obtain ⟨s,q,sq,gq,sy⟩ := (qval_mem_l O hZF generic value).mp hy
      obtain ⟨hs,_,forced⟩ := (edges s q).mp sq
      obtain ⟨a,ha,check⟩ := (checks s).mp hs
      have ey : j a = y := qval_unique_l (checked a s check) sy
      have trueφ := (forcing_closed_truth_l hZF O generic φ.body φ.freeClosed (ρ.push s) (η.push (j a))
        (Fin.cases (checked a s check) values)).mp ⟨q,gq,(sat s q).mp forced⟩
      exact ey ▸ (define a ha).mp trueφ
    · intro hy
      obtain ⟨a,ha,rfl⟩ := (full D y).mp (sub y hy)
      obtain ⟨s,check,ns',_⟩ := zf_check_l M hZF stage.member a
      obtain ⟨q,hq,_,decide⟩ := name.prefix_global_l hZF hw fa.1 product stage hn small φ.body φ.freeClosed
        (ρ.push s) (Fin.cases (Or.inr ns') params)
      have forced := (decide G generic (fun _ h => h.2) (η.push (j a))
        (Fin.cases (checked a s check) values)).mp ((define a ha).mpr hy)
      exact (qval_mem_l O hZF generic value).mpr ⟨s,q,
        (edges s q).mpr ⟨(checks s).mpr ⟨a,ha,check⟩,hq.1,(sat s q).mpr forced⟩,hq.2,checked a s check⟩)
  exact eq ▸ value

end YesMetaZFC.Model.Forcing.Internal

/-! ## 由规范实数并及前缀参数定义的实数回收到原前缀

实数图包含于旧自然数方块。尾部齐性恢复其实际前缀名字，正则包含的
有界绝对性再反映全部函数条件。最后直接应用于原 Ob_eval 序数解码，
不额外要求参数定义公式；内部有限参数列的共同前缀由 ProductFiniteParameters 构造。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 从真实唯一定义恢复前缀名字，并证明其前缀解释已是实数。 -/
theorem Rp_name_d.prefix_real_l {ω A P R W r n C S b : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    (stage : Fp_stage_d hZF ω A n C S b) (hn : M.mem n ω)
    {d} (φ : UnarySchema d) (ρ : Env M d)
    (params : ∀ i, ρ.bound i = r ∨ Name_d M C (ρ.bound i))
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain)
    (ground : ∀ a, Gval_d M P R P G a (j a))
    (η : Env (extension_l M hZF P R P G) d)
    (values : ∀ i, Qval_d M P R P G (ρ.bound i) (η.bound i))
    {x : (extension_l M hZF P R P G).Domain} (real : Fn0_d (j ω) (j ω) x)
    (define : ∀ y, φ.denote η y ↔ y = x) :
    ∃ σ, Name_d M C σ ∧ Qval_d M P R P G σ x ∧ Rp_value_d hZF ω A P R G x := by
  let E := extension_l M hZF P R P G
  let H : M.Domain → Prop := fun p => M.mem p C ∧ G p
  let D := extension_l M hZF C S C H
  have O := product.order_l hZF
  have hE : E.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨p,hp⟩ := generic.inhabited
  obtain ⟨j₀,checks,full,inj⟩ := check_map_l O hZF generic hp
  have same : j₀ = j := funext fun a => (gval_check_map_l O hZF generic hp j₀ checks a (j a)).mp (ground a)
  subst j₀
  obtain ⟨Y,productY⟩ := ZF.exists_cartesianProduct hZF I ω ω
  have productE := image_product_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) j inj full productY
  obtain ⟨σ,ns,all⟩ := name.prefix_subset_l hZF hw fa product stage hn (od_member_s φ) ρ params Y
  have value := all G generic j ground η values x (fun t ht => (productE t).mpr (real.1 t ht))
    (fun a _ => od_member_sat_l φ η define (j a))
  obtain ⟨small,e,ei,ef,keep,base⟩ := stage.stage.extension_l hZF product hw hn fa generic
  have hD : D.Models ZF := preserves_zf_l (stage.stage.order_l hZF) hZF small
  obtain ⟨q,hq⟩ := small.inhabited
  obtain ⟨k,checkK,_,_⟩ := check_map_l (stage.stage.order_l hZF) hZF small hq
  have groundK a := (gval_check_map_l (stage.stage.order_l hZF) hZF small hq k checkK a (k a)).mpr rfl
  have commute a : e (k a) = j a := (base a (k a) (groundK a)).unique_l O hZF generic (ground a)
  obtain ⟨y,vy⟩ := name_value_l (R := S) (z := C) (U := H) ns
  have eq : e y = x := qval_unique_l (keep y σ vy) value
  let δ : Env D 3 := ⟨fun i => [k ω,k ω,y].get i,fun _ => y⟩
  have formula := (fn0_sat_l hD.1 δ (.bound 0) (.bound 1) (.bound 2)).symm.trans
    ((delta0_image_l e ei ef (fn0_delta_l ..) δ).trans (fn0_sat_l hE.1 _ _ _ _))
  have fy : Fn0_d (k ω) (k ω) y := formula.mpr (by
    change Fn0_d (e (k ω)) (e (k ω)) (e y)
    simpa only [commute,eq] using real)
  exact ⟨σ,ns,value,n,C,S,b,hn,stage,k,groundK,σ,y,vy,value,fy⟩

/-- 原层参数表示中的 Ob_eval 直接给出真实恢复实例：整个规范实数并、
一个已有前缀名字的参数对象和一个地序数码定义的实数，仍在该前缀。 -/
theorem Rp_name_d.prefix_ob_real_l {ω A P R W r n C S b τ q : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    (stage : Fp_stage_d hZF ω A n C S b) (hn : M.mem n ω) (nt : Name_d M C τ)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain)
    (ground : ∀ a, Gval_d M P R P G a (j a))
    {Z s p x : (extension_l M hZF P R P G).Domain}
    (value : Qval_d M P R P G r Z) (parameter : Qval_d M P R P G τ s)
    (pair : KPair_d (extension_l M hZF P R P G) p Z s)
    (code : Ob_eval_d (kp_pair_l (ZF.modelsKP (preserves_zf_l (product.order_l hZF) hZF generic))) (j q) p x)
    (real : Fn0_d (j ω) (j ω) x) :
    ∃ σ, Name_d M C σ ∧ Qval_d M P R P G σ x ∧ Rp_value_d hZF ω A P R G x := by
  let E := extension_l M hZF P R P G
  have O := product.order_l hZF
  have hE : E.Models ZF := preserves_zf_l O hZF generic
  have small := (stage.stage.extension_l hZF product hw hn fa generic).1
  obtain ⟨a,ha⟩ := small.inhabited
  have hb := small.upward a b ha stage.member (stage.top a (small.proper a ha).1)
  obtain ⟨t,check,nt',_⟩ := zf_check_l M hZF stage.member q
  have cP : M.MemberSubset C P := fun a ha => ((stage.stage.product_read_l hZF product hn).1 a).mp ha |>.1
  obtain ⟨v,vt⟩ := name_value_l (R := R) (z := P) (U := G) (name_conditions_mono_l cP nt')
  have eq : v = j q := (show Gval_d M P R P G q v from ⟨b,t,hb.2,check,vt⟩).unique_l O hZF generic (ground q)
  have vq : Qval_d M P R P G t (j q) := eq ▸ vt
  let φ : UnarySchema 3 := {
    body := .existsE (.conj (kpair_m .newest (.bound 2) (.bound 3))
      (ob_eval_m (.bound 4) .newest (.bound 1))) }
  let ρ : Env M 3 := ⟨fun i => [r,τ,t].get i,fun _ => r⟩
  let η : Env E 3 := ⟨fun i => [Z,s,j q].get i,fun _ => Z⟩
  have define y : φ.denote η y ↔ y = x := by
    have sat : φ.denote η y ↔ ∃ p', KPair_d E p' Z s ∧ Ob_eval_d (kp_pair_l (ZF.modelsKP hE)) (j q) p' y := by
      simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
        kpair_sat_l E hE.1,ob_eval_sat_l (kp_pair_l (ZF.modelsKP hE)) hE.1]
      rfl
    apply sat.trans
    exact ⟨fun ⟨p',pair',code'⟩ => ob_eval_unique_l (kp_pair_l (ZF.modelsKP hE)) hE
      (kpair_unique_l E hE.1 pair' pair ▸ code') code,fun eq => eq.symm ▸ ⟨p,pair,code⟩⟩
  exact name.prefix_real_l hZF hw fa product stage hn φ ρ
    (Fin.cases (Or.inl rfl) (Fin.cases (Or.inr nt) (Fin.cases (Or.inr nt') (fun i => Fin.elim0 i))))
    generic j ground η (Fin.cases value (Fin.cases parameter (Fin.cases vq (fun i => Fin.elim0 i)))) real define

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一规范名字的弱齐性、顶判定与全部尾延伸真值证书

证书直接消费已构造的乘积和规范名字。冻结前缀参数使用前缀泛型中的
实际判定条件；地参数情形使用原空顶条件，两者分别保留准确的量词域。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Rp_decision_d (ω A P R r : M.Domain) : Prop where
  homogeneous : ∀ n p q, M.mem p P → M.mem q P → Fp_agree_d hZF n p q →
    ∃ F s, Fp_tail_d I n P R F ∧ Entry_d M p s F ∧ Cmp_d M P R P s q
  top : ∀ o, (∀ x, ¬ M.mem x o) → ∀ {k} (φ : Formula 1 k), φ.FreeClosed → ∀ ρ : Env M k,
    (∀ i, ρ.bound i = r ∨ ∃ x, Check_d M o x (ρ.bound i)) →
      (Forces_d M P R P φ ρ o ∨ Forces_d M P R P (.neg φ) ρ o) ∧
      ∀ G, Generic_d M P R P G → ∀ η : Env (extension_l M hZF P R P G) k,
        (∀ i, Qval_d M P R P G (ρ.bound i) (η.bound i)) →
        (Forces_d M P R P φ ρ o ↔ Formula.satisfies η φ)
  prefix_decision : ∀ n C S b, M.mem n ω → Fp_stage_d hZF ω A n C S b →
    ∀ H, Generic_d M C S C H → ∀ {k} (φ : Formula 1 k), φ.FreeClosed → ∀ ρ : Env M k,
    (∀ i, ρ.bound i = r ∨ Name_d M C (ρ.bound i)) →
      ∃ a, H a ∧ (Forces_d M P R P φ ρ a ∨ Forces_d M P R P (.neg φ) ρ a) ∧
        ∀ G, Generic_d M P R P G → (∀ p, H p → G p) →
        ∀ η : Env (extension_l M hZF P R P G) k,
          (∀ i, Qval_d M P R P G (ρ.bound i) (η.bound i)) →
          (Formula.satisfies η φ ↔ Forces_d M P R P φ ρ a)

theorem Rp_name_d.decision_l {ω A P R r : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunction I A) (product : Fp_product_d hZF ω A P R) :
    Rp_decision_d hZF ω A P R r := by
  refine ⟨fun _ _ _ => fp_tail_homogeneous_l hZF hw fa product,?_,?_⟩
  · intro o empty k φ closed ρ params
    exact ⟨name.top_decides_l hZF hw fa product empty φ closed ρ params,
      fun _ generic η values => name.top_truth_l hZF hw fa product empty generic φ closed ρ params η values⟩
  · intro n C S b hn stage H small k φ closed ρ params
    exact name.prefix_global_l hZF hw fa product stage hn small φ closed ρ params

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原坍缩派生层的有限实数参数及地序数码

规范实数并的精确解释给出函数族，因而相对 Jensen 参数表示可直接应用。
地嵌入、相同 ω 和无新序数均由实际全乘积泛型构造；定义码随之回收
到原地模型。这里不声称参数列已经合并为规范实数并中的一个实数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rp_name_d.parameters_l {ω A P R W r : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    {Z : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Z) :
    let E := extension_l M hZF P R P G
    let hE := preserves_zf_l (product.order_l hZF) hZF generic
    ∃ j : M.Domain → E.Domain, (∀ a, Gval_d M P R P G a (j a)) ∧ E.IsOmega (j ω) ∧
      ∀ S, Tc_d Z S → ∀ x, Relative.La_d S x →
        ∃ n s p α, E.mem n (j ω) ∧ Fn0_d n Z s ∧ KPair_d E p Z s ∧
          M.IsOrdinal α ∧ Ob_eval_d (kp_pair_l (ZF.modelsKP hE)) (j α) p x := by
  dsimp only
  let E := extension_l M hZF P R P G
  have O := product.order_l hZF
  have hE : E.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨b,hb⟩ := generic.inhabited
  obtain ⟨j,checks,full,inj,ordinals⟩ := check_map_ordinals_l O hZF generic hb
  have ground a := (gval_check_map_l O hZF generic hb j checks a (j a)).mpr rfl
  have omega : E.IsOmega (j ω) := image_omega_l (hEN := hE.1) j inj full hZF
    (internal_foundation_l O hZF generic) hw (fun X => KP.difference_exists_d (ZF.modelsKP hE) X (j ω))
  obtain ⟨Z₀,value₀,members⟩ := name.value_l hZF hw fa product generic
  have eq := qval_unique_l value₀ value
  have functions x (hx : E.mem x Z) : Fn0_d (j ω) (j ω) x :=
    ((members x).mp (eq.symm ▸ hx)).function_l hZF hw fa product generic j ground
  refine ⟨j,ground,omega,fun S tc x hx => ?_⟩
  obtain ⟨n,s,p,q,hn,seq,pair,ordinal,code⟩ := Relative.dr_parameters_l hE omega functions tc hx
  obtain ⟨α,hα,eα⟩ := (ordinals q).mp ordinal
  exact ⟨n,s,p,α,hn,seq,pair,hα,eα.symm ▸ code⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原坍缩派生 Jensen 模型不增加实数

每个实际层元素由规范实数并、内部有限参数列及地序数码定义。整列的
共同前缀由内部有限覆盖构造，尾部齐性随后恢复定义所得实数的前缀名字。
由此得到真实相对 Jensen 并类中的实数恰为原规范实数并；不假定结论，
也不要求 Woodin、外部标准自然数或外部良基性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rp_name_d.no_new_reals_l {ω A P R W r : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    {Z : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Z) :
    let E := extension_l M hZF P R P G
    ∃ j : M.Domain → E.Domain, (∀ a, Gval_d M P R P G a (j a)) ∧ E.IsOmega (j ω) ∧
      ∀ S, Tc_d Z S → ∀ x, Relative.La_d S x →
        (Fn0_d (j ω) (j ω) x ↔ x ∈ Z) := by
  obtain ⟨j,ground,omega,parameters⟩ := name.parameters_l hZF hw fa product generic value
  obtain ⟨Z₀,value₀,members⟩ := name.value_l hZF hw fa product generic
  have eq := qval_unique_l value₀ value
  subst Z₀
  refine ⟨j,ground,omega,fun S tc x layer => ⟨fun real => ?_,fun hx =>
    ((members x).mp hx).function_l hZF hw fa product generic j ground⟩⟩
  obtain ⟨k,s,p,q,hk,seq,pair,_,code⟩ := parameters S tc x layer
  obtain ⟨n,C,T,b,τ,hn,stage,nt,vs⟩ := name.sequence_prefix_l hZF hw fa product generic j ground value hk seq
  obtain ⟨_,_,_,rp⟩ := name.prefix_ob_real_l hZF hw fa product stage hn nt generic j ground value vs pair code real
  exact (members x).mpr rp

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原派生模型的真实完整实数空间与原种子

无新实数定理直接装配相对 Jensen 模型内部的 Baire 空间和传递种子。
所有对象来自同一个规范实数并解释，重算相对并类仍包含原模型的全部元素，
可直接供层参数表示、最小坏收益及带符号见证构造调用。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rp_name_d.derived_model_l {ω A P R W r : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    {Z : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Z) :
    let E := extension_l M hZF P R P G
    let hE := preserves_zf_l (product.order_l hZF) hZF generic
    ∃ j : M.Domain → E.Domain, (∀ a, Gval_d M P R P G a (j a)) ∧ E.IsOmega (j ω) ∧
      ∀ S, ∀ tc : Tc_d Z S,
        let D := Relative.la_model_l S (ZF.models_kpi_l hE)
        let hD := Relative.la_model_zf_l S hE tc.1
        ∃ w z s : D.Domain, w.val = j ω ∧ z.val = Z ∧ s.val = S ∧
          Relative.Lr_seed_d hD w z s ∧ ∀ x : D.Domain, Relative.La_d s x := by
  dsimp only
  obtain ⟨j,ground,omega,reals⟩ := name.no_new_reals_l hZF hw fa product generic value
  exact ⟨j,ground,omega,fun S tc => Relative.la_real_self_l
    (preserves_zf_l (product.order_l hZF) hZF generic) omega tc (reals S tc)⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 固定前缀后的同一个最小坏代码

最小代码的序数性把它回收到地模型；参数实数由原规范实数并给出实际
有限前缀名字。前缀泛型中的一个条件迫使这同一个代码的最小性，且该
判定对全部延伸此前缀的尾部泛型有效。每个目标中的其他最小代码必相等。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.InnerModel.Relative
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际原前缀、原泛型接受条件、名字及全部尾延伸中的同代码结论。 -/
def Dm_prefix_d (φ : Formula 1 4) (ω A P R r : M.Domain) (product : Fp_product_d hZF ω A P R) (G : M.Domain → Prop)
    (a c : (extension_l M hZF P R P G).Domain) : Prop :=
  ∃ j : M.Domain → (extension_l M hZF P R P G).Domain,
    (∀ x, Gval_d M P R P G x (j x)) ∧ ∃ q, M.IsOrdinal q ∧ j q = c ∧
      ∃ n C S b τ κ u, M.mem n ω ∧ Fp_stage_d hZF ω A n C S b ∧ Name_d M C τ ∧
        Qval_d M P R P G τ a ∧ Check_d M b q κ ∧ M.mem u C ∧ G u ∧
        Forces_d M P R P (dm_min_m φ) (⟨fun i => [r,τ,κ].get i,fun _ => r⟩ : Env M 3) u ∧
        ∀ H, ∀ h : Generic_d M P R P H, (∀ p, M.mem p C → G p → H p) →
          ∀ j' : M.Domain → (extension_l M hZF P R P H).Domain,
            (∀ x, Gval_d M P R P H x (j' x)) →
          ∀ Z' a' : (extension_l M hZF P R P H).Domain,
            Qval_d M P R P H r Z' → Qval_d M P R P H τ a' →
            Dm_min_d (preserves_zf_l (product.order_l hZF) hZF h) φ Z' a' (j' q) ∧
              ∀ d, Dm_min_d (preserves_zf_l (product.order_l hZF) hZF h) φ Z' a' d → d = j' q

theorem Rp_name_d.minimum_prefix_l {φ : Formula 1 4} (hc : φ.FreeClosed) {ω A P R W r : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    {Z a c : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Z)
    (least : Dm_min_d (preserves_zf_l (product.order_l hZF) hZF generic) φ Z a c) :
    Dm_prefix_d hZF φ ω A P R r product G a c := by
  let E := extension_l M hZF P R P G
  have O := product.order_l hZF
  have hE : E.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨p,hp⟩ := generic.inhabited
  obtain ⟨j,checks,_,_,ordinals⟩ := check_map_ordinals_l O hZF generic hp
  have ground x := (gval_check_map_l O hZF generic hp j checks x (j x)).mpr rfl
  obtain ⟨q,oq,eq⟩ := (ordinals c).mp (least.ordinal_l hE)
  obtain ⟨Z₀,v₀,members⟩ := name.value_l hZF hw fa product generic
  have same := qval_unique_l v₀ value
  obtain ⟨n,C,S,b,hn,stage,_,_,τ,_,vτ,target,_⟩ := (members a).mp (same.symm ▸ least.real_l hE)
  have nt := qval_name_l vτ
  have small := (stage.stage.extension_l hZF product hw hn fa generic).1
  obtain ⟨t,ht⟩ := small.inhabited
  have hb := small.upward t b ht stage.member (stage.top t (small.proper t ht).1)
  obtain ⟨κ,check,nκ,_⟩ := zf_check_l M hZF stage.member q
  have vκ := check_map_change_l O hZF generic hp hb.2 j checks q κ check
  let ρ : Env M 3 := ⟨fun i => [r,τ,κ].get i,fun _ => r⟩
  let η : Env E 3 := ⟨fun i => [Z,a,j q].get i,fun _ => Z⟩
  have values : ∀ i, Qval_d M P R P G (ρ.bound i) (η.bound i) :=
    Fin.cases value (Fin.cases target (Fin.cases vκ (fun i => Fin.elim0 i)))
  have truth : Formula.satisfies η (dm_min_m φ) := (dm_min_sat_l hE φ hc η).mpr
    (show Dm_min_d hE φ Z a (j q) from eq.symm ▸ least)
  obtain ⟨u,hu,_,all⟩ := name.prefix_global_l hZF hw fa.1 product stage hn small (dm_min_m φ) (dm_min_closed_l hc) ρ
    (Fin.cases (Or.inl rfl) (Fin.cases (Or.inr nt) (Fin.cases (Or.inr nκ) (fun i => Fin.elim0 i))))
  have forced := (all G generic (fun _ h => h.2) η values).mp truth
  refine ⟨j,ground,q,oq,eq,n,C,S,b,τ,κ,u,hn,stage,nt,target,check,hu.1,hu.2,forced,?_⟩
  intro H h accepted j' ground' Z' a' vz va
  let E' := extension_l M hZF P R P H
  have hE' : E'.Models ZF := preserves_zf_l O hZF h
  have hbH := accepted b hb.1 hb.2
  have cP : M.MemberSubset C P := fun p hp => ((stage.stage.product_read_l hZF product hn).1 p).mp hp |>.1
  obtain ⟨d,vd⟩ := name_value_l (R := R) (z := P) (U := H) (name_conditions_mono_l cP nκ)
  have ed : d = j' q := (show Gval_d M P R P H q d from ⟨b,κ,hbH,check,vd⟩).unique_l O hZF h (ground' q)
  let η' : Env E' 3 := ⟨fun i => [Z',a',j' q].get i,fun _ => Z'⟩
  have values' : ∀ i, Qval_d M P R P H (ρ.bound i) (η'.bound i) :=
    Fin.cases vz (Fin.cases va (Fin.cases (show Qval_d M P R P H κ (j' q) from ed ▸ vd) (fun i => Fin.elim0 i)))
  have minimum := (dm_min_sat_l hE' φ hc η').mp
    ((all H h (fun p hp => accepted p hp.1 hp.2) η' values').mpr forced)
  exact ⟨minimum,fun d hd => hd.unique_l hE' minimum⟩

/-- 参数本来就在地模型时，原空顶条件迫使同一最小代码；无需先固定非空前缀。 -/
theorem Rp_name_d.minimum_top_l {φ : Formula 1 4} (hc : φ.FreeClosed) {ω A P R r a : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunction I A) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    (j : M.Domain → (extension_l M hZF P R P G).Domain) (ground : ∀ x, Gval_d M P R P G x (j x))
    {Z c : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Z)
    (least : Dm_min_d (preserves_zf_l (product.order_l hZF) hZF generic) φ Z (j a) c) :
    ∃ q o τ κ, M.IsOrdinal q ∧ (∀ x, ¬ M.mem x o) ∧ Check_d M o a τ ∧ Check_d M o q κ ∧ j q = c ∧
      Forces_d M P R P (dm_min_m φ) (⟨fun i => [r,τ,κ].get i,fun _ => r⟩ : Env M 3) o ∧
      ∀ H, ∀ h : Generic_d M P R P H,
        ∀ j' : M.Domain → (extension_l M hZF P R P H).Domain,
          (∀ x, Gval_d M P R P H x (j' x)) →
        ∀ Z' : (extension_l M hZF P R P H).Domain, Qval_d M P R P H r Z' →
          Dm_min_d (preserves_zf_l (product.order_l hZF) hZF h) φ Z' (j' a) (j' q) ∧
            ∀ d, Dm_min_d (preserves_zf_l (product.order_l hZF) hZF h) φ Z' (j' a) d → d = j' q := by
  have O := product.order_l hZF
  have hE := preserves_zf_l O hZF generic
  obtain ⟨p,hp⟩ := generic.inhabited
  obtain ⟨j₀,checks,_,_,ordinals⟩ := check_map_ordinals_l O hZF generic hp
  have same : j₀ = j := funext fun x => (gval_check_map_l O hZF generic hp j₀ checks x (j x)).mp (ground x)
  subst j₀
  obtain ⟨q,oq,eq⟩ := (ordinals c).mp (least.ordinal_l hE)
  obtain ⟨o,empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨ho,top⟩ := product.empty_top_l hZF hw empty
  have go := generic.upward p o hp ho (top p (generic.proper p hp).1)
  obtain ⟨τ,ca,_,_⟩ := zf_check_l M hZF ho a
  obtain ⟨κ,cq,_,_⟩ := zf_check_l M hZF ho q
  have va := check_map_change_l O hZF generic hp go j checks a τ ca
  have vq := check_map_change_l O hZF generic hp go j checks q κ cq
  let ρ : Env M 3 := ⟨fun i => [r,τ,κ].get i,fun _ => r⟩
  let η : Env (extension_l M hZF P R P G) 3 := ⟨fun i => [Z,j a,j q].get i,fun _ => Z⟩
  have truth : Formula.satisfies η (dm_min_m φ) := (dm_min_sat_l hE φ hc η).mpr
    (show Dm_min_d hE φ Z (j a) (j q) from eq.symm ▸ least)
  have forced := (name.top_truth_l hZF hw fa product empty generic (dm_min_m φ) (dm_min_closed_l hc) ρ
    (Fin.cases (Or.inl rfl) (Fin.cases (Or.inr ⟨a,ca⟩) (Fin.cases (Or.inr ⟨q,cq⟩) (fun i => Fin.elim0 i)))) η
    (Fin.cases value (Fin.cases va (Fin.cases vq (fun i => Fin.elim0 i))))).mpr truth
  refine ⟨q,o,τ,κ,oq,empty,ca,cq,eq,forced,fun H h j' ground' Z' vz => ?_⟩
  have hE' := preserves_zf_l O hZF h
  obtain ⟨p',hp'⟩ := h.inhabited
  have hoH := h.upward p' o hp' ho (top p' (h.proper p' hp').1)
  obtain ⟨l,checked,_,_⟩ := check_map_l O hZF h hoH
  have same : l = j' := funext fun x => (gval_check_map_l O hZF h hoH l checked x (j' x)).mp (ground' x)
  subst l
  let η' : Env (extension_l M hZF P R P H) 3 := ⟨fun i => [Z',j' a,j' q].get i,fun _ => Z'⟩
  have minimum := (dm_min_sat_l hE' φ hc η').mp
    ((forcing_closed_truth_l hZF O h (dm_min_m φ) (dm_min_closed_l hc) ρ η'
      (Fin.cases vz (Fin.cases (checked a τ ca) (Fin.cases (checked q κ cq) (fun i => Fin.elim0 i))))).mp ⟨o,hoH,forced⟩)
  exact ⟨minimum,fun d hd => hd.unique_l hE' minimum⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 从真实派生模型的 AD 否定构造最小坏代码

完整实数空间和种子由原无新实数定理构造。原 AD 否定给出实际收益，
原层呈示及最小元构造给出二值参数和最小坏代码，再装配精确相对化断言、
原前缀接受条件及全部尾延伸中的同代码力迫证书。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rp_name_d.counterexample_l {ω A P R W r : M.Domain}
    (name : Rp_name_d hZF ω A P r) (hw : M.IsOmega ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (product : Fp_product_d hZF ω A P R)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    {Z S : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G r Z) (tc : Tc_d Z S)
    (bad : ¬ (Relative.la_model_l S (ZF.models_kpi_l (preserves_zf_l (product.order_l hZF) hZF generic))).SatisfiesSentence Axioms.ad_axiom) :
    let E := extension_l M hZF P R P G
    let hE := preserves_zf_l (product.order_l hZF) hZF generic
    ∃ j : M.Domain → E.Domain, (∀ a, Gval_d M P R P G a (j a)) ∧ E.IsOmega (j ω) ∧
      ∃ a c : E.Domain, a ∈ Z ∧ Bc_binary_d (j ω) a ∧ Relative.Dm_min_d hE Relative.lr_payoff_m Z a c ∧
        Dm_prefix_d hZF Relative.lr_payoff_m ω A P R r product G a c := by
  dsimp only
  let E := extension_l M hZF P R P G
  have hE : E.Models ZF := preserves_zf_l (product.order_l hZF) hZF generic
  let D := Relative.la_model_l S (ZF.models_kpi_l hE)
  have hD : D.Models ZF := Relative.la_model_zf_l S hE tc.1
  let J := kp_pair_l (ZF.modelsKP hD)
  obtain ⟨j,ground,omega,models⟩ := name.derived_model_l hZF hw fa product generic value
  obtain ⟨w,b,s,ew,eb,_,seed,self⟩ := models S tc
  obtain ⟨T,finite⟩ := ZF.fseq_space_exists_l J hD seed.1.1 w
  have counter : ∃ B : D.Domain, D.MemberSubset B b ∧ ¬ Det_d J w b T B := by
    apply Classical.byContradiction
    intro none
    apply bad
    apply (ad_axiom_sat_l (ZF.modelsKP hD)).mpr
    exact ⟨w,b,T,seed.1,finite,fun B sub => Classical.byContradiction (fun no => none ⟨B,sub,no⟩)⟩
  obtain ⟨B,sub,no⟩ := counter
  let B' : (Relative.la_model_l s (ZF.models_kpi_l hD)).Domain := ⟨B,self B⟩
  obtain ⟨a,c,_,real,binary,least,_,_,_⟩ := Relative.jp_min_payoff_l hD seed B' sub no
  let ρ : Env D 2 := ⟨Fin.cases w (fun _ => a),fun _ => w⟩
  have raw := (bc_binary_sat_l hE.1 _ _ _).mp
    ((Relative.la_model_delta_l S (ZF.models_kpi_l hE) tc.1 (bc_binary_delta_l (.bound 0) (.bound 1)) ρ).mp
      ((bc_binary_sat_l hD.1 ρ (.bound 0) (.bound 1)).mpr binary))
  have bits : Bc_binary_d (j ω) a.val := by
    change Bc_binary_d w.val a.val at raw
    exact ew ▸ raw
  have minimum : Relative.Dm_min_d hE Relative.lr_payoff_m Z a.val c.val :=
    ⟨S,tc,b,a,c,eb,rfl,rfl,real,w,s,T,seed.1,seed.2,finite,least⟩
  refine ⟨j,ground,omega,a.val,c.val,?_,bits,minimum,
    name.minimum_prefix_l hZF Relative.lr_payoff_closed_l hw fa product generic value minimum⟩
  exact eb ▸ (show E.mem a.val b.val from real)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 统一最小代码的顶条件判定给出原 R* 查询的正负条件

消费固定参数版本已构造的原顶条件力迫。任意后续全泛型都接受同一个
空顶条件；实际规范实数并的求值和真值定理遂给出同一名字的一侧判定。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.InnerModel.Relative SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem Rp_name_d.query_top_l {φ : Formula 1 4} (hc : φ.FreeClosed)
    {ω A P R W r a q o s t τ : M.Domain} (name : Rp_name_d hZF ω A P r)
    (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) A ω W)
    (product : Fp_product_d hZF ω A P R) (binary : Bc_binary_d ω a)
    (empty : ∀ x, ¬ M.mem x o) (ca : Check_d M o a s) (cq : Check_d M o q t)
    (forced : Forces_d M P R P (dm_min_m φ) (⟨fun i => [r,s,t].get i,fun _ => r⟩ : Env M 3) o)
    {G : M.Domain → Prop} (generic : Generic_d M P R P G)
    {x : (extension_l M hZF P R P G).Domain} (value : Qval_d M P R P G τ x)
    (real : Rp_value_d hZF ω A P R G x) :
    G o ∧ ((∃ p, G p ∧ Qs_force_d φ true P R r ω a τ o p) ∨
      ∃ p, G p ∧ Qs_force_d φ false P R r ω a τ o p) := by
  have O := product.order_l hZF
  have hE := preserves_zf_l O hZF generic
  obtain ⟨ho,top⟩ := product.empty_top_l hZF hw empty
  obtain ⟨p,hp⟩ := generic.inhabited
  have go := generic.upward p o hp ho (top p (generic.proper p hp).1)
  obtain ⟨j,checks,full,inj⟩ := check_map_l O hZF generic go
  have ground z := (gval_check_map_l O hZF generic go j checks z (j z)).mpr rfl
  obtain ⟨Z,vZ,members⟩ := name.value_l hZF hw fa product generic
  let E := extension_l M hZF P R P G
  let ρ : Env M 3 := ⟨fun i => [r,s,t].get i,fun _ => r⟩
  let η : Env E 3 := ⟨fun i => [Z,j a,j q].get i,fun _ => Z⟩
  have least := (dm_min_sat_l hE φ hc η).mp
    ((forcing_closed_truth_l hZF O generic (dm_min_m φ) (dm_min_closed_l hc) ρ η
      (Fin.cases vZ (Fin.cases (checks a s ca) (Fin.cases (checks q t cq) (fun i => Fin.elim0 i))))).mp ⟨o,go,forced⟩)
  have hw' : E.IsOmega (j ω) := image_omega_l (hEN := hE.1) j inj full hZF
    (internal_foundation_l O hZF generic) hw (fun D => KP.difference_exists_d (ZF.modelsKP hE) D (j ω))
  have binary' := (bc_binary_image_l j inj full hZF.1 hE.1).mp binary
  exact ⟨go,qs_cover_l hZF O generic hc go j ground vZ value hw' binary' least ((members x).mpr real)⟩

end YesMetaZFC.Model.Forcing.Internal
