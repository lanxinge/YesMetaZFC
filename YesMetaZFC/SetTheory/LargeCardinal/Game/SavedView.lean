import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CriticalBound

/-! # 保存时的完整代码与当前共同图视图

档案保留原模型、原记录码及回答域的原生 γ 下界。标签、回答域和类型经实际共同图进入当前事件，
保存短前缀的同一图像逐项对应当前实数事件；轮号经数字图对应外部档案行。
准备步骤读取事件时，两侧复制图的交换性和目标复制的单射性识别三个事件坐标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_saved_view_d (I : kpair_convention_l.Interpretation M)
    (X R w U q γ g N S w' C c e a b z m h : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d X R w U q v ∧
    It_lower_d I γ X R (v 15) ∧
    ∃ n t κ u, M.PairMember I m n z ∧ M.PairMember I (v 41) t g ∧
      M.PairMember I (v 15) κ g ∧ M.PairMember I (v 11) u g ∧
      Tg_trace_d I N S w' C c e a n h t κ u ∧
      ∃ s, M.PairMember I (v 40) s g ∧ Tg_play_d I N S C c b h s

variable (I : kpair_convention_l.Interpretation M)

/-- 原码唯一性与实际复制方块确定同一视图，不要求两次选择的共同图字面相同。 -/
theorem Tg_saved_view_d.read_l (hE : Extensional M)
    {X R w U q γ g N S w' C c e a b z m h A π B σ L l φ V Γ l' φ' V' Γ' s n t κ u : M.Domain}
    (view : Tg_saved_view_d I X R w U q γ g N S w' C c e a b z m h)
    {v : Fin 54 → M.Domain} (code : Tg_saved_code_d X R w U q v)
    (old : Ic_agree_d I X R A π N S B σ L l φ U V Γ g)
    (now : Ic_agree_d I X R A π N S B σ L l' φ' U V' Γ' s)
    (left : M.IsSetFunctionFromTo I π X A) (right : M.IsSetInjectionFromTo I σ N B)
    (numbers : M.IsSetFunction I z) (index : M.PairMember I m n z)
    (it : M.PairMember I (v 41) t s) (iκ : M.PairMember I (v 15) κ s) (iu : M.PairMember I (v 11) u s) :
    Tg_trace_d I N S w' C c e a n h t κ u ∧
      ∃ x, M.PairMember I (v 40) x s ∧ Tg_play_d I N S C c b h x := by
  obtain ⟨p,cp,_,n₀,t₀,κ₀,u₀,index₀,it₀,iκ₀,iu₀,trace,x,ix,play⟩ := view
  have eq := cp.inj_l I hE code
  have et : p 41 = v 41 := congrFun eq 43
  have eκ : p 15 = v 15 := congrFun eq 17
  have eu : p 11 = v 11 := congrFun eq 13
  have es : p 40 = v 40 := congrFun eq 42
  have entry x y f : Rd_entry_d x y f ↔ M.PairMember I x y f := by
    let ρ : Env M 3 := ⟨fun i => [x,y,f].get i,fun _ => x⟩
    exact (rd_entry_sat_l hE ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      (Formula.satisfies_orderedPairMem_iff I ρ (.bound 0) (.bound 1) (.bound 2))
  have same x y y' (xy : M.PairMember I x y g) (xy' : M.PairMember I x y' s) : y = y' := by
    obtain ⟨x',_,xx'⟩ := left.2.2 x
      ((old.common.carrier x).mp (old.common.injection.1.input_mem_of_pairMember xy)).1
    exact right.2 y y' x'
      ((entry y x' σ).mp (old.points x x' y ((entry x x' π).mpr xx') ((entry x y g).mpr xy)))
      ((entry y' x' σ).mp (now.points x x' y' ((entry x x' π).mpr xx') ((entry x y' s).mpr xy')))
  have en := numbers.2 m n₀ n index₀ index
  have et := same (v 41) t₀ t (et ▸ it₀) it
  have eκ := same (v 15) κ₀ κ (eκ ▸ iκ₀) iκ
  have eu := same (v 11) u₀ u (eu ▸ iu₀) iu
  have source := (old.common.carrier (v 40)).mp
    (old.common.injection.1.input_mem_of_pairMember (es ▸ ix))
  obtain ⟨x',_,ix'⟩ := now.common.injection.1.2.2 (v 40) ((now.common.carrier (v 40)).mpr source)
  have ex := same (v 40) x x' (es ▸ ix) ix'
  exact ⟨en ▸ et ▸ eκ ▸ eu ▸ trace,x',ix',ex ▸ play⟩

end YesMetaZFC.SetTheory.LargeCardinal
