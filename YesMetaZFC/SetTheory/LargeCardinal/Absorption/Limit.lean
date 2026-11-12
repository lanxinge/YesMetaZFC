import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Links
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswerTreeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Target
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.ReturnOrder

/-! # 实际无限吸收运行的整列外层相容历史

先从原记录投影四个历史坐标，再把相邻保持提升为全部早晚行的保持。
各行的模型、全部内部箭头及完整返回列均由有限反射运行直接提供。
三列保持只需传递性；取并保留原模型列、箭头和返回列，测试壳无需 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include trans

/-- 原四列历史、全部早晚相容及完整内部模型图与返回列均不要求测试模型满足 ZF。 -/
theorem ab_outer_trace_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain} {F : M.Domain}
    (hΩ : M.IsOmega ω.val) (run : Ab_run_d I P ω.val cY.val Y.val S.val F) :
    ∃ D H, Wi_history_d hZF ω.val cY.val Y.val S.val ω.val D H ∧
      ∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
        Wi_at_d H i (v 22) (v 23) (v 24) (v 25) := by
  obtain ⟨D,H,hf,graph⟩ := ab_history_function_l hZF (fn0_function_l (ZF.modelsKP hZF) run.function)
    (fun _ _ ir => (run.columns_l hZF.1 model trans ir).elim fun v h => ⟨v,h.1⟩)
  have read {i s : M.Domain} (hs : Rd_entry_d i s H) : ∃ r, ∃ v : Fin 26 → M.Domain,
      Rd_entry_d i r F ∧ Rt_tuple_d v r ∧ Rd_quad_d s (v 22) (v 23) (v 24) (v 25) ∧
      M.SuccessorOf (v 7) i ∧ Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω.val (v 7) (v 22) (v 23) (v 24) cY.val Y.val S.val (v 25) := by
    obtain ⟨r,ir,v,tuple,quad⟩ := (graph i s).mp hs
    obtain ⟨w,tuple',_,_,stage⟩ := run.columns_l hZF.1 model trans ir
    have eq := rt_tuple_inj_l tuple' tuple
    exact ⟨r,v,ir,tuple,quad,eq ▸ stage,run.histories i r v ir tuple⟩
  have trace {i r : M.Domain} {v : Fin 26 → M.Domain} (ir : Rd_entry_d i r F) (tuple : Rt_tuple_d v r) :
      Wi_at_d H i (v 22) (v 23) (v 24) (v 25) := by
    obtain ⟨s,quad⟩ := rd_quad_exists_l (ZF.modelsKP hZF) (v 22) (v 23) (v 24) (v 25)
    exact ⟨s,(graph i s).mpr ⟨r,ir,v,tuple,quad⟩,quad⟩
  have quads i s (hs : Rd_entry_d i s H) : ∃ T Q G U, Rd_quad_d s T Q G U := by
    obtain ⟨_,v,_,_,quad,_⟩ := read hs
    exact ⟨v 22,v 23,v 24,v 25,quad⟩
  have adjacent i j T Q G U T' Q' G' U' (succ : M.SuccessorOf j i)
      (first : Wi_at_d H i T Q G U) (last : Wi_at_d H j T' Q' G' U') : Wi_keep_d Q G U Q' G' U' := by
    obtain ⟨s,hs,ps⟩ := first
    obtain ⟨t,ht,pt⟩ := last
    obtain ⟨r,v,ir,vr,quad,_⟩ := read hs
    obtain ⟨s,w,js,ws,quad',_⟩ := read ht
    obtain ⟨rfl,rfl,rfl,rfl⟩ := ps.unique_l quad
    obtain ⟨rfl,rfl,rfl,rfl⟩ := pt.unique_l quad'
    exact run.keep_l hZF.1 model trans succ ir js vr ws
  refine ⟨D,H,⟨hf,?_,wi_chain_past_l hZF hΩ hf quads adjacent⟩,
    fun _ _ _ ir tuple => trace ir tuple⟩
  intro i s hs
  obtain ⟨_,v,_,_,quad,stage,state⟩ := read hs
  exact ⟨v 7,v 22,v 23,v 24,v 25,stage,quad,state⟩

theorem ab_outer_history_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain} {F : M.Domain}
    (hΩ : M.IsOmega ω.val)
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F) :
    ∃ D H T Q G U, Wi_history_d hZF ω.val cY.val Y.val S.val ω.val D H ∧
      Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω.val ω.val T Q G cY.val Y.val S.val U ∧
      (∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
        Wi_at_d H i (v 22) (v 23) (v 24) (v 25)) ∧
      (∀ i T' Q' G' U', Wi_at_d H i T' Q' G' U' → Wi_keep_d Q' G' U' Q G U) ∧
      ∀ i d X V, Rd_entry_d i d Q → Smdl_d I d X V → Zc_model_d I ω.val d X V := by
  have fn := fn0_function_l (ZF.modelsKP hZF) run.function
  obtain ⟨D,H,history,atH⟩ := ab_outer_trace_l hZF model trans hΩ run
  obtain ⟨T,Q,G,U,state,keep⟩ := history.union_l hZF (hΩ.isLimitOrdinal (ZF.modelsKP hZF))
  -- 首行证书来自同一有限反射运行；不再向外运输壳内 ZFC 模式。
  obtain ⟨o,empty,ho⟩ := hΩ.1.1
  obtain ⟨r₀,_,start⟩ := fn.2.2 o ho
  obtain ⟨v₀,tuple₀,code,_⟩ := run.columns_l hZF.1 model trans start
  have initial := atH o r₀ v₀ start tuple₀
  have cert₀ := (run.queues o r₀ v₀ start tuple₀).frame.theory
  have rootQ := (keep o _ _ _ _ initial).1 o (v₀ 0) code
  refine ⟨D,H,T,Q,G,U,history,state,atH,keep,?_⟩
  intro i d X V id mx
  obtain ⟨f,edge⟩ := state.diagram.map_l hZF
    (state.diagram.order.root_l hZF empty i ((state.diagram.model_domain i).mpr ⟨d,id⟩))
  exact cert₀.map_l hZF hΩ mx (state.diagram.elementary o i f (v₀ 0) (v₀ 1) (v₀ 2)
    d X V edge rootQ id cert₀.model mx)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 吸收列的实际传递直接极限及原全乘积

使用已装配的原模型图和返回列构造良基极限。每条原返回图经同一极限因子分解，
固定返回像的单射性识别各行全乘积和顺序的极限值。
此构造消费原行的背景证书、已装配历史及实际返回目标，不要求测试模型满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Ab_limit_d (ω cY Y F C U d X V J σ A Q T : M.Domain) : Prop where
  omega : M.IsOmega ω
  model : Smem_d I d X V
  theory : Zc_model_d I ω d X V
  transitive : M.TransitiveSet X
  inside : M.mem ω X ∧ M.mem A X ∧ M.mem Q X ∧ M.mem T X
  clock : (smdl_structure_l I (R := V) model.1.2.1).IsOmega ⟨ω,inside.1⟩
  alphabet : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (theory.native_l I hZF omega))))
    (⟨ω,inside.1⟩ : (smdl_structure_l I (R := V) model.1.2.1).Domain) ⟨A,inside.2.1⟩
  product : Fp_product_d (ZFC.models_zf_l (theory.native_l I hZF omega))
    (⟨ω,inside.1⟩ : (smdl_structure_l I (R := V) model.1.2.1).Domain)
    ⟨A,inside.2.1⟩ ⟨Q,inside.2.2.1⟩ ⟨T,inside.2.2.2⟩
  returns : Smap_d I ω d cY X Y σ
  product_image : Rd_entry_d Q C σ
  order_image : Rd_entry_d T U σ
  function : M.IsSetFunction I J
  domain : M.IsDomainOf I ω J
  rows : ∀ i r (v : Fin 26 → M.Domain) j, Rd_entry_d i r F → Rt_tuple_d v r → Rd_entry_d i j J →
    Smap_d I ω (v 0) d (v 1) X j ∧ It_comp_d j σ (v 3) ∧ Rd_entry_d (v 5) Q j ∧ Rd_entry_d (v 6) T j
  zero_alphabet : ∀ i r (v : Fin 26 → M.Domain) j, (∀ a, ¬ M.mem a i) →
    Rd_entry_d i r F → Rt_tuple_d v r → Rd_entry_d i j J → Rd_entry_d (v 4) A j
  cover : ∀ y, M.mem y X → ∃ i j x, Rd_entry_d i j J ∧ Rd_entry_d x y j
  cover_after : ∀ n, M.mem n ω → ∀ y, M.mem y X →
    ∃ i j x, (n = i ∨ M.mem n i) ∧ Rd_entry_d i j J ∧ Rd_entry_d x y j

variable {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
include trans

theorem Ab_run_d.limit_l {ω cY Y S C U : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F T₀ Q₀ G₀ U₀ : M.Domain}
    (hΩ : M.IsOmega ω.val)
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F) (ctx : Ab_return_order_d F C.val U.val)
    (system : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω.val ω.val T₀ Q₀ G₀ cY.val Y.val S.val U₀)
    (records : ∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → Wi_keep_d (v 23) (v 24) (v 25) Q₀ G₀ U₀) :
    ∃ d X V J σ A Q T, Ab_limit_d hZF ω.val cY.val Y.val F C.val U.val d X V J σ A Q T := by
  have nodes {i r : M.Domain} {v : Fin 26 → M.Domain} (ir : Rd_entry_d i r F) (vr : Rt_tuple_d v r) :
      Rd_entry_d i (v 0) Q₀ ∧ Rd_entry_d i (v 3) U₀ := by
    obtain ⟨w,wr,code,ret,_⟩ := run.columns_l hZF.1 model trans ir
    have eq := rt_tuple_inj_l vr wr
    subst v
    have keep := records i r _ ir wr
    exact ⟨keep.1 i (w 0) code,keep.2.2 i (w 3) ret⟩
  obtain ⟨o,empty₀,ho⟩ := hΩ.1.1
  obtain ⟨r₀,_,start⟩ := run.function.2.1 o ho
  obtain ⟨v,tuple₀,_,_⟩ := run.columns_l hZF.1 model trans start
  have base := (run.queues _ _ _ start tuple₀).frame
  obtain ⟨X₀,V₀,K₀,mx₀,source₀⟩ := system.sources o (v 0) (nodes start tuple₀).1
  obtain ⟨L,B,p,H,R',r,d,X,V,J,σ,_,_,mdl,cone,⟨K,source⟩,ret,_,squares,_,_⟩ :=
    it_embedding_limit_l hZF hΩ system.diagram (system.branch_l hZF) ho (nodes start tuple₀).1
      (it_source_mem_l hZF mx₀ source₀) run.target system.returns
  obtain ⟨j₀,oj⟩ := (cone.domain o).mp ho
  have root := cone.elementary o j₀ (v 0) (v 1) (v 2) oj (nodes start tuple₀).1 base.model.1
  have cert := base.theory.map_l hZF hΩ mdl.1 root
  let A₀ := smdl_structure_l I (R := v 2) base.model.1.2.1
  let B₀ := smdl_structure_l I (R := V) mdl.1.2.1
  have hA := ZFC.models_zf_l (base.theory.native_l I hZF hΩ)
  have hB := ZFC.models_zf_l (cert.native_l I hZF hΩ)
  let w : A₀.Domain := ⟨ω.val,base.inside.1⟩
  let a : A₀.Domain := ⟨v 4,base.inside.2.1⟩
  let q : A₀.Domain := ⟨v 5,base.inside.2.2.1⟩
  let t : A₀.Domain := ⟨v 6,base.inside.2.2.2.1⟩
  let n : A₀.Domain := ⟨v 7,base.inside.2.2.2.2.1⟩
  let c₀ : A₀.Domain := ⟨v 8,base.inside.2.2.2.2.2.1⟩
  let u₀ : A₀.Domain := ⟨v 9,base.inside.2.2.2.2.2.2.1⟩
  obtain ⟨hw₀,sequence,product,_⟩ := (ab_kernel_read_l I base.model base.transitive hA w a q t n c₀ u₀).mp base.kernel
  obtain ⟨e,elem,values⟩ := root.project_l I hZF hΩ base.model.1 mdl.1
  have ew : e w = (⟨ω.val,source.omega_mem⟩ : B₀.Domain) := Subtype.ext
    (root.1.1.1.2 _ _ _ (values w) (root.omega_l I hZF hΩ base.transitive source.transitive base.model mdl base.inside.1))
  have product' := fp_product_image_l hA hB e elem product
  rw [ew] at product'
  have sequence' := sequence.image_l (kp_pair_l (ZF.modelsKP hA)) (kp_pair_l (ZF.modelsKP hB)) hA.1 hB.1 e elem
  rw [ew] at sequence'
  let ρ : Env A₀ 1 := ⟨fun _ => w,fun _ => w⟩
  have hw' : B₀.IsOmega (e w) := (Formula.satisfies_isOmega_iff (image_env_l e ρ) .newest).mp
    ((elem (Formula.isOmega .newest) (by simp -implicitDefEqProofs) ρ).mp
      ((Formula.satisfies_isOmega_iff ρ .newest).mpr hw₀))
  rw [ew] at hw'
  have square := squares o (v 3) j₀ (nodes start tuple₀).2 oj
  have factor {x y z : M.Domain} (xy : Rd_entry_d x y j₀) (xz : Rd_entry_d x z (v 3)) : Rd_entry_d y z σ := by
    obtain ⟨y',xy',yz⟩ := (square.2 x z).mp xz
    exact root.1.1.1.2 _ _ _ xy' xy ▸ yz
  have qC := factor (values q) (ctx.rows o r₀ v start tuple₀).1
  have tU := factor (values t) (ctx.rows o r₀ v start tuple₀).2
  refine ⟨d,X,V,J,σ,(e a).val,(e q).val,(e t).val,
    ⟨hΩ,mdl,cert,source.transitive,⟨source.omega_mem,(e a).property,(e q).property,(e t).property⟩,
      hw',sequence',product',ret,qC,tU,cone.function,cone.domain,?_,?_,cone.cover,?_⟩⟩
  · intro i r v j ir vr ij
    have data := (run.queues _ _ _ ir vr).frame
    have node := nodes ir vr
    have leg := cone.elementary i j (v 0) (v 1) (v 2) ij node.1 data.model.1
    have square := squares i (v 3) j node.2 ij
    have productEq {x y z : M.Domain} (xz : Rd_entry_d x z (v 3)) (yz : Rd_entry_d y z σ) : Rd_entry_d x y j := by
      obtain ⟨y',xy',yz'⟩ := (square.2 x z).mp xz
      exact ret.1.2 _ _ _ yz' yz ▸ xy'
    exact ⟨leg,square,productEq (ctx.rows i r v ir vr).1 qC,productEq (ctx.rows i r v ir vr).2 tU⟩
  · -- 零轮及其锥腿由实际函数图唯一确定，故字母表就是构造时采用的同一个像。
    intro i r w j empty ir wr ij
    have ei : i = o := hZF.1.eq_of_same_members _ _ (fun x => iff_of_false (empty x) (empty₀ x))
    subst i
    have er : r = r₀ := (fn0_function_l (ZF.modelsKP hZF) run.function).1.2 _ _ _ ir start
    subst r
    have ev := rt_tuple_inj_l wr tuple₀
    have ej := cone.function.2 _ _ _ ij oj
    subst w j
    exact values a
  · intro n hn y hy
    obtain ⟨i,j,x,ij,xy⟩ := cone.cover y hy
    have hi := (cone.domain i).mpr ⟨j,ij⟩
    rcases (hΩ.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn i hi with eq | lt | gt
    · exact ⟨i,j,x,Or.inl (hZF.1.eq_of_same_members n i eq),ij,xy⟩
    · exact ⟨i,j,x,Or.inr lt,ij,xy⟩
    · -- 旧表示经原列箭头移到指定后来行；锥交换律保持同一个极限值。
      obtain ⟨r,_,ir⟩ := run.function.2.1 i hi
      obtain ⟨s,_,ns⟩ := run.function.2.1 n hn
      obtain ⟨v,vr,_,_⟩ := run.columns_l hZF.1 model trans ir
      obtain ⟨w,ws,_,_⟩ := run.columns_l hZF.1 model trans ns
      have left := (run.queues _ _ _ ir vr).frame
      have right := (run.queues _ _ _ ns ws).frame
      obtain ⟨f,arrow⟩ := system.diagram.map_l hZF (system.linear i n hn gt)
      have move := system.diagram.elementary i n f _ _ _ _ _ _ arrow (nodes ir vr).1 (nodes ns ws).1 left.model.1 right.model.1
      have old := cone.elementary i j _ _ _ ij (nodes ir vr).1 left.model.1
      obtain ⟨z,hz,xz⟩ := move.1.1.2.2 x (old.1.1.input_mem_of_pairMember xy)
      obtain ⟨k,nk⟩ := (cone.domain n).mp hn
      have new := cone.elementary n k _ _ _ nk (nodes ns ws).1 right.model.1
      obtain ⟨y',_,zy⟩ := new.1.1.2.2 z hz
      have eq := old.1.1.1.2 _ _ _ (cone.commute i n f j k arrow ij nk x z y' xz zy) xy
      exact ⟨n,k,z,Or.inl rfl,nk,eq ▸ zy⟩

end YesMetaZFC.SetTheory.LargeCardinal
