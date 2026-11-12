import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.Model.SetTheory.Relations.Collapse
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.CumulativeRelativeClosure

/-! # 同一原后继的塌缩逆图给出完整共同层

两侧已有的同一相对秩层只决定逆图的限制域。全前驱和全局缺失直接由
完整塌缩及背景外延性读取，不把原关系后继加强为原生 KP 模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 保留给定原目标及其塌缩，构造共同层的实际逆图。 -/
theorem ic_collapse_common_l
    {ω c X R d N S e P T g L W : M.Domain}
    (hw : M.IsOmega ω) (mx : Smem_d I c X R) (xt : M.TransitiveSet X)
    (mn : Smdl_d I d N S) (mp : Smem_d I e P T) (pt : M.TransitiveSet P)
    (map : Smap_d I ω d e N P g) (bij : M.IsSetBijectionFromTo I g N P)
    (hLX : M.mem L X) (hLP : M.mem L P) (hWX : M.mem W X) (hWP : M.mem W P)
    (left : Vr_d X L W) (right : Vr_d P L W) (limit : M.IsLimitOrdinal L)
    (exactness : Es_strength_d X L P) :
    ∃ l V t, Rd_entry_d l L g ∧ Rd_entry_d V W g ∧
      (∀ x E, Rd_entry_d x E t ↔ M.mem x W ∧ Rd_entry_d E x g) ∧
      Ic_common_d I X R N S L l W V W t := by
  obtain ⟨l,_,hl⟩ := bij.2 L hLP
  obtain ⟨V,_,hV⟩ := bij.2 W hWP
  obtain ⟨s,bs,inverse⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  obtain ⟨t,rest⟩ := ZF.exists_restriction hZF I s W
  have graph x E : Rd_entry_d x E t ↔ M.mem x W ∧ Rd_entry_d E x g :=
    (rest.2 x E).trans (and_congr Iff.rfl (inverse x E))
  have ft : M.IsSetInjectionFromTo I t W N :=
    ⟨rest.isSetFunctionFromTo bs.1.1 (pt W hWP),
      fun x y E hx hy => bs.1.2 x y E ((rest.2 x E).mp hx).2 ((rest.2 y E).mp hy).2⟩
  have wt := left.transitive_l xt hWX
  have ords : M.MemberSubset L W := left.ordinal_subset_l hZF xt hWX
  have rel a b x y (ha : Rd_entry_d a x g) (hb : Rd_entry_d b y g) :
      Rd_entry_d a b S ↔ M.mem x y :=
    (map.relation_l I hZF hw mn mp.1 ha hb).trans
      ⟨fun h => ((mp.2 x y).mp h).2.2,
        fun h => (mp.2 x y).mpr ⟨map.1.1.output_mem_of_pairMember ha,
          map.1.1.output_mem_of_pairMember hb,h⟩⟩
  -- 任意全前驱实现均等于其完整塌缩值，故缺失在整个原后继中保持。
  have rep x E (hx : M.mem x X) (sub : M.MemberSubset x W) :
      Er_rep_d X R N S t x E ↔ Rd_entry_d E x g := by
    constructor
    · intro h
      obtain ⟨y,hy,hEy⟩ := map.1.1.2.2 E h.2.1
      have eq : x = y := hZF.1.eq_of_same_members x y (fun a => by
        constructor
        · intro hax
          obtain ⟨Q,_,hQa⟩ := bij.2 a (pt W hWP a (sub a hax))
          have edge := (h.2.2 Q).mpr ⟨a,xt x hx a hax,
            (mx.2 a x).mpr ⟨xt x hx a hax,hx,hax⟩,(graph a Q).mpr ⟨sub a hax,hQa⟩⟩
          exact (rel Q E a y hQa hEy).mp edge
        · intro hay
          obtain ⟨Q,_,hQa⟩ := bij.2 a (pt y hy a hay)
          obtain ⟨b,_,hbx,hbQ⟩ := (h.2.2 Q).mp ((rel Q E a y hQa hEy).mpr hay)
          have eq := map.1.1.1.2 Q b a ((graph b Q).mp hbQ).2 hQa
          exact eq ▸ ((mx.2 b x).mp hbx).2.2)
      exact eq.symm ▸ hEy
    · intro hEx
      refine ⟨hx,map.1.1.input_mem_of_pairMember hEx,fun Q => ?_⟩
      constructor
      · intro hQE
        obtain ⟨a,_,hQa⟩ := map.1.1.2.2 Q (mn.2.2.2 Q E hQE).1
        have hax := (rel Q E a x hQa hEx).mp hQE
        exact ⟨a,xt x hx a hax,(mx.2 a x).mpr ⟨xt x hx a hax,hx,hax⟩,
          (graph a Q).mpr ⟨sub a hax,hQa⟩⟩
      · rintro ⟨a,_,hax,haQ⟩
        exact (rel Q E a x ((graph a Q).mp haQ).2 hEx).mpr ((mx.2 a x).mp hax).2.2
  have pred x E (hxE : Rd_entry_d x E t) Q :
      Rd_entry_d Q E S ↔ ∃ y, Rd_entry_d y x R ∧ Rd_entry_d y Q t := by
    have hx := (graph x E).mp hxE
    have h := (rep x E (xt W hWX x hx.1) (wt x hx.1)).mpr hx.2
    exact (h.2.2 Q).trans ⟨fun ⟨y,_,hy,hyQ⟩ => ⟨y,hy,hyQ⟩,
      fun ⟨y,hy,hyQ⟩ => ⟨y,xt W hWX y ((graph y Q).mp hyQ).1,hy,hyQ⟩⟩
  have exact' : Er_exact_d X R N S L t := by
    refine ⟨hLX,?_,?_⟩
    · intro α hα hαL x hx sub
      have hαL' := ((mx.2 α L).mp hαL).2.2
      have bound : M.MemberSubset x α := fun a ha =>
        ((mx.2 a α).mp (sub a (xt x hx a ha) ((mx.2 a x).mpr ⟨xt x hx a ha,hx,ha⟩))).2.2
      obtain ⟨E,_,hEx⟩ := bij.2 x (exactness.1 α hαL' x hx bound)
      exact ⟨E,(rep x E hx (fun a ha => ords a (limit.1.transitive α hαL' a (bound a ha)))).mpr hEx⟩
    · obtain ⟨x,hx,bound,missing⟩ := exactness.2
      refine ⟨x,hx,fun a ha hax => (mx.2 a L).mpr ⟨ha,hLX,bound a ((mx.2 a x).mp hax).2.2⟩,?_⟩
      intro E h
      exact missing (map.1.1.output_mem_of_pairMember ((rep x E hx (fun a ha => ords a (bound a ha))).mp h))
  have closed {a Y Q H} (my : Smem_d I a Y Q) (yt : M.TransitiveSet Y)
      (hH : M.mem H Y) (rank : Vr_d Y L H) : Rr_closed_d I Y Q H := by
    intro a b ha hb haH sub
    exact (my.2 b H).mpr ⟨hb,hH,rank.subset_mem_l yt hH ((my.2 a H).mp haH).2.2 hb
      (fun x hx => ((my.2 x a).mp (sub x (yt b hb x hx) ((my.2 x b).mpr ⟨yt b hb x hx,hb,hx⟩))).2.2)⟩
  have rightRank := (rr_rank_mem_l I (ZF.modelsKP hZF) mp pt hLP hWP).mpr right
  have rawRank := (rr_rank_truth_l I).mpr (((rr_rank_truth_l I).mp rightRank).pull_l I hZF hw mn mp.1 map
    (by simp -implicitDefEqProofs) (Fin.cases hV (fun _ => hl)))
  let nx : Nonempty {x // M.mem x X} := ⟨⟨L,hLX⟩⟩
  have nativeLimit : Rr_truth_d I X R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => L) := by
    refine ⟨fun _ => hLX,?_⟩
    exact (smem_formula_l I mx nx _
      (⟨fun _ => ⟨L,hLX⟩,fun _ => ⟨L,hLX⟩⟩ : Env (rt_model_l X nx) 1)).mp
        ((Formula.satisfies_isLimitOrdinal_iff ..).mpr ((rt_limit_l xt nx (ZF.modelsKP hZF) ⟨L,hLX⟩).mpr limit))
  refine ⟨l,V,t,hl,hV,graph,⟨(rr_rank_mem_l I (ZF.modelsKP hZF) mx xt hLX hWX).mpr left,
    rawRank,nativeLimit,?_,ft,?_,pred,closed mx xt hWX left,
    (map.rr_closed_l I hZF hw mn mp.1 hV).mpr (closed mp pt hWP right),(rep L l hLX ords).mpr hl,exact'⟩⟩
  · intro x
    exact ⟨fun hx => ⟨xt W hWX x hx,(mx.2 x W).mpr ⟨xt W hWX x hx,hWX,hx⟩⟩,
      fun ⟨_,hx⟩ => ((mx.2 x W).mp hx).2.2⟩
  · intro E
    constructor
    · intro hEV
      obtain ⟨x,_,hEx⟩ := map.1.1.2.2 E (mn.2.2.2 E V hEV).1
      have hx := (rel E V x W hEx hV).mp hEV
      exact ⟨x,hx,(graph x E).mpr ⟨hx,hEx⟩⟩
    · rintro ⟨x,hx,hxE⟩
      exact (rel E V x W ((graph x E).mp hxE).2 hV).mpr hx

/-- 同一共轭因子的层值、端点及逐点方块把完整共同层接到实际工作行。 -/
theorem ic_collapse_agree_l
    {ω c X R d N S e P T g L W A B π σ q φ W' : M.Domain}
    (hw : M.IsOmega ω) (mx : Smem_d I c X R) (xt : M.TransitiveSet X)
    (mn : Smdl_d I d N S) (mp : Smem_d I e P T) (pt : M.TransitiveSet P)
    (map : Smap_d I ω d e N P g) (bij : M.IsSetBijectionFromTo I g N P)
    (hLX : M.mem L X) (hLP : M.mem L P) (hWX : M.mem W X) (hWP : M.mem W P)
    (left : Vr_d X L W) (right : Vr_d P L W) (limit : M.IsLimitOrdinal L)
    (exactness : Es_strength_d X L P)
    (ta : M.TransitiveSet A) (tb : M.TransitiveSet B) (limit' : M.IsLimitOrdinal φ)
    (hWA : M.mem W' A) (hWB : M.mem W' B) (rankA : Vr_d A φ W') (rankB : Vr_d B φ W')
    (levelπ : Rd_entry_d W W' π) (levelq : Rd_entry_d W W' q)
    (endπ : Rd_entry_d L φ π) (endq : Rd_entry_d L φ q)
    (comp : It_comp_d g q σ)
    (points : ∀ x x', M.mem x W → Rd_entry_d x x' π → Rd_entry_d x x' q) :
    ∃ l V t, Rd_entry_d l L g ∧ Rd_entry_d V W g ∧
      (∀ x E, Rd_entry_d x E t ↔ M.mem x W ∧ Rd_entry_d E x g) ∧
      Ic_agree_d I X R A π N S B σ L l φ W V W t := by
  obtain ⟨l,V,t,hl,hV,graph,common⟩ := ic_collapse_common_l hZF hw mx xt mn mp pt map bij
    hLX hLP hWX hWP left right limit exactness
  refine ⟨l,V,t,hl,hV,graph,common,ta,tb,limit',
    ⟨W',hWA,hWB,rankA,rankB,levelπ,(comp.2 V W').mpr ⟨W,hV,levelq⟩⟩,
    endπ,(comp.2 l φ).mpr ⟨L,hl,endq⟩,?_⟩
  intro x x' E hxx hxE
  obtain ⟨hx,hEx⟩ := (graph x E).mp hxE
  exact (comp.2 E x').mpr ⟨x,hEx,points x x' hx hxx⟩

end YesMetaZFC.SetTheory.LargeCardinal
