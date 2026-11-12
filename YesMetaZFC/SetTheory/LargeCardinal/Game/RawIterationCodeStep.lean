import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationNext
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawFirst
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueMove
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationNextSyntax

/-! # 原生有限状态的两分支实际后继

重置和继续直接使用已经核验的原后继，随后打包同一目标请求。
第一条边给新档案的父行几何，第二条边保持控制坐标和原前缀；
所有原操作的根临界下界随同这两次延伸保存。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意真实原字母输入都有同一次两步原树延伸及精确下一状态。 -/
theorem Tg_raw_iteration_d.advance_l
    {ω c₀ o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A x : M.Domain}
    {v : Fin 20 → M.Domain} {a : Fin 46 → M.Domain}
    (h : Tg_raw_iteration_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A v a)
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (cut : Tg_root_cut_d I c₀ X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A) (input : M.mem x A) :
    ∃ w b, Tg_raw_iteration_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A w b ∧
      Tg_raw_iteration_next_d hZF ω c₀ A x v w a b := by
  classical
  have finite {θ : M.Domain} (succ : M.SuccessorOf θ (v 6)) : M.mem θ ω := by
    obtain ⟨m,hm,hmω⟩ := h.tree.omega.1.2 (v 7) h.finite
    have em := hm.eq hZF.1 h.successor
    obtain ⟨n,hn,hnω⟩ := h.tree.omega.1.2 (v 6) (em ▸ hmω)
    exact hn.eq hZF.1 succ ▸ hnω
  by_cases empty : a 23 = a 1
  · obtain ⟨L,W,r₁,saved,vs,code,emptyCoord,treeCoord,lengthZero,shortZero,labelZero,graphZero,_,
      θ,T₁,Q₁,G₁,E₁,jp,q₁,succ,mid,first,node,pad,identity,_,_,_,rest⟩ :=
      h.request.reset_l hZFC root cut h.tree h.successor h.node h.model h.root_node
        h.levels_function h.levels empty h.play input
    obtain ⟨θ₂,T₂,Q₂,G₂,E₂,c₂,X₂,R₂,j₂,q₂,p₂,Λ₂,next,second,node₂,edge₂,_,_,
      function,levels,_,_,certificate,_,_,_,keepCritical,rest⟩ := rest
    obtain ⟨w₂,η₂,C₂,z₂,l,k',D',r',rr,y,f',b,succk,hy,even,request,points,history,tuple,append,play,ends⟩ := rest
    let row : Tg_raw_archive_row_d M.Domain := ⟨v 6,v 15,v 0,v 1,v 2,v 4,v 5,L,W,r₁,q₁⟩
    -- 重置的实际第一边是恒等边；原树对象的像由其全性和恒等证书给出。
    have map := mid.diagram.elementary (v 7) (v 6) jp (v 15) (v 0) (v 1) (v 15) (v 0) (v 1)
      pad (first.2.2.1 (v 7) (v 15) h.node) node h.model h.model
    have member : M.mem (a 7) (v 0) := treeCoord ▸ code.values_l I hZF.1 19
    obtain ⟨S,_,point⟩ := map.1.1.2.2 (a 7) member
    have eqS : S = vs 19 := (identity (a 7) S point).symm.trans treeCoord.symm
    have geometry : Tg_raw_archive_reset_d I row (a 7) jp :=
      ⟨vs,code,eqS ▸ point,lengthZero.trans emptyCoord.symm,shortZero.trans emptyCoord.symm,
        labelZero.trans emptyCoord.symm,graphZero.trans emptyCoord.symm⟩
    have parent : Tg_raw_iteration_parent_d hZF v a (v 7) G₁ row :=
      ⟨jp,pad,Or.inl ⟨empty,rfl,geometry⟩⟩
    let w : Fin 20 → M.Domain := fun i =>
      [X₂,R₂,w₂,z₂,η₂,C₂,θ₂,θ,T₂,Q₂,G₂,E₂,Λ₂,D',l,c₂,q₂,r',k',f'].get i
    refine ⟨w,b,?_,?_⟩
    · exact ⟨finite succ,second.1,next,function,levels,node₂,certificate.model,
        second.2.2.1 o c₀ (first.2.2.1 o c₀ h.root_node),request,play,keepCritical h.critical⟩
    · exact ⟨v 7,T₁,Q₁,G₁,E₁,j₂,mid,first,second,edge₂,points,history,succk,
        y,hy,ends,even,row,rr,rfl,tuple,parent,append⟩
  · obtain ⟨m₀,r₀,old,hm₀,index,stored,oldTuple,_,vs₀,oldCode,rest⟩ :=
      h.request.continue_l hZFC root cut h.tree h.successor h.node h.model h.root_node
        h.levels_function h.levels empty h.play input
    obtain ⟨L₁,θ,T₁,Q₁,G₁,E₁,Λ₁,c₁,X₁,R₁,j₁,q₁,p₁,_,mid,first,node₁,edge₁,_,_,
      _,_,_,_,_,_,_,rest⟩ := rest
    obtain ⟨w₁,η₁,C₁,L₂,W₂,r₂,saved,vs,us,code,oldPoints,restart,_,_,_,rest⟩ := rest
    obtain ⟨θ₂,T₂,Q₂,G₂,E₂,Λ₂,c₂,X₂,R₂,j₂,q₂,p₂,next,second,node₂,edge₂,_,_,
      function,levels,_,_,certificate,_,_,_,keepCritical,rest⟩ := rest
    obtain ⟨w₂,η₂,C₂,z₂,l,k',D',r',rr,y,f',b,succk,hy,even,request,points,history,tuple,append,play,ends⟩ := rest
    let row : Tg_raw_archive_row_d M.Domain := ⟨v 6,c₁,X₁,R₁,w₁,η₁,C₁,L₂,W₂,r₂,q₁⟩
    have geometry : Tg_raw_archive_step_d I old row j₁ :=
      ⟨vs₀,vs,oldCode,code,(fun i => us ([19,22,40,41,42].get i)),
        (fun i => oldPoints ([19,22,40,41,42].get i)),restart⟩
    have parent : Tg_raw_iteration_parent_d hZF v a old.i G₁ row :=
      ⟨j₁,edge₁,Or.inr ⟨empty,m₀,r₀,old,hm₀,index,stored,oldTuple,rfl,geometry⟩⟩
    let w : Fin 20 → M.Domain := fun i =>
      [X₂,R₂,w₂,z₂,η₂,C₂,θ₂,θ,T₂,Q₂,G₂,E₂,Λ₂,D',l,c₂,q₂,r',k',f'].get i
    refine ⟨w,b,?_,?_⟩
    · exact ⟨finite first.1,second.1,next,function,levels,node₂,certificate.model,
        second.2.2.1 o c₀ (first.2.2.1 o c₀ h.root_node),request,play,keepCritical h.critical⟩
    · exact ⟨old.i,T₁,Q₁,G₁,E₁,j₂,mid,first,second,edge₂,points,history,succk,
        y,hy,ends,even,row,rr,rfl,tuple,parent,append⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 六十六项原状态码的实际后继总性

输入码解出已经闭合的原请求；两类真实宏后继执行给定字母，再将同一
新状态编码。完整双边、三图几何、临界界及原前缀始终来自该次构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Tg_raw_iteration_edge_d (ω c A x s t : M.Domain) : Prop :=
  ∃ v w : Fin 66 → M.Domain, Rt_tuple_d v s ∧ Rt_tuple_d w t ∧
    Tg_raw_iteration_next_d hZF ω c A x
      (fun i => v (i.castAdd 46)) (fun i => w (i.castAdd 46))
      (fun i => v (Fin.natAdd 20 i)) (fun i => w (Fin.natAdd 20 i))

def tg_raw_iteration_edge_m {d} (ω c A x s t : Term d) : Formula 1 d :=
  let e : Term d → Term (66+d) := fun z => z.rename (Fin.natAdd 66)
  let f : Term (66+d) → Term (66+(66+d)) := fun z => z.rename (Fin.natAdd 66)
  let v : Fin 66 → Term (66+(66+d)) := fun i => f (.bound (i.castAdd d))
  let w : Fin 66 → Term (66+(66+d)) := fun i => .bound (i.castAdd (66+d))
  rb_exists_m (n := 66) (rb_exists_m (n := 66) (.conj (rt_tuple_m v (f (e s)))
    (.conj (rt_tuple_m w (f (e t))) (tg_raw_iteration_next_m (f (e ω)) (f (e c)) (f (e A)) (f (e x))
      (fun i => v (i.castAdd 46)) (fun i => w (i.castAdd 46))
      (fun i => v (Fin.natAdd 20 i)) (fun i => w (Fin.natAdd 20 i))))))

@[simp] theorem tg_raw_iteration_edge_closed_l {d} (ω c A x s t : Term d)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (hA : A.freeSupport = [])
    (hx : x.freeSupport = []) (hs : s.freeSupport = []) (ht : t.freeSupport = []) :
    (tg_raw_iteration_edge_m ω c A x s t).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_iteration_edge_m,Definitional.Formula.FreeClosed,hω,hc,hA,hx]
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs),
    rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using ht)⟩

theorem tg_raw_iteration_edge_sat_l {d} (ρ : Env M d) (ω c A x s t : Term d) :
    Formula.satisfies ρ (tg_raw_iteration_edge_m ω c A x s t) ↔
      Tg_raw_iteration_edge_d hZF (ω.eval ρ) (c.eval ρ) (A.eval ρ) (x.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [tg_raw_iteration_edge_m,Tg_raw_iteration_edge_d,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hZF.1,tg_raw_iteration_next_sat_l hZF,Definitional.Term.eval_rename,
    Env.reindex,Function.comp_def,Term.eval_bound,Fin.addCases_left,Fin.addCases_right]

theorem Tg_raw_iteration_edge_d.read_l {ω c A x s t : M.Domain} {v w : Fin 66 → M.Domain}
    (h : Tg_raw_iteration_edge_d hZF ω c A x s t) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :
    Tg_raw_iteration_next_d hZF ω c A x
      (fun i => v (i.castAdd 46)) (fun i => w (i.castAdd 46))
      (fun i => v (Fin.natAdd 20 i)) (fun i => w (Fin.natAdd 20 i)) := by
  obtain ⟨a,b,pa,pb,next⟩ := h
  exact (rt_tuple_inj_l pa ps) ▸ (rt_tuple_inj_l pb pt) ▸ next

variable (hZFC : M.Models ZFC)
local notation "J" => kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))

/-- 同一个真实根及根切片自动供应每个原字母的完整编码后继。 -/
theorem Tg_raw_iteration_code_d.advance_l
    {ω c o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A x s : M.Domain}
    (root : Zc_model_d J ω c X₀ R₀)
    (cut : Tg_root_cut_d J c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (h : Tg_raw_iteration_code_d (ZFC.models_zf_l hZFC) ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s)
    (hx : M.mem x A) : ∃ t,
      Tg_raw_iteration_code_d (ZFC.models_zf_l hZFC) ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A t ∧
      Tg_raw_iteration_edge_d (ZFC.models_zf_l hZFC) ω c A x s t := by
  obtain ⟨v,code,state⟩ := h
  obtain ⟨w,b,next,edge⟩ := state.advance_l hZFC root cut hx
  let q : Fin 66 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) w b
  obtain ⟨t,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP (ZFC.models_zf_l hZFC)) q
  refine ⟨t,⟨q,tuple,?_⟩,v,q,code,tuple,?_⟩
  · simpa only [q,Fin.addCases_left,Fin.addCases_right] using next
  · simpa only [q,Fin.addCases_left,Fin.addCases_right] using edge

end YesMetaZFC.SetTheory.LargeCardinal
