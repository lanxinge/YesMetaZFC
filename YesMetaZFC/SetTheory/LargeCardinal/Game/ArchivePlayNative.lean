import YesMetaZFC.SetTheory.LargeCardinal.Game.RequestState
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeEntry
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationStep

/-! # 同一原请求中的短图事件与实际背景前缀

两份原生求值在同一反射层中读取同一历史事件。时钟及历史的单值性识别其值，
实际请求的数字图随后把给定背景指标与原生指标对齐；源模型无需隶属呈示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 真实请求直接识别旧短图的值与当前背景前缀的根像。 -/
theorem Tg_request_state_d.play_value_l (hKP : M.Models KP)
    {Ω γ Bγ C₀ S₀ X R w η C A σ χ z k D r L p f s i n x y : M.Domain}
    {frame : Tg_archive_frame_d M.Domain} {v : Fin 46 → M.Domain}
    (request : Tg_request_state_d I Ω γ Bγ C₀ S₀ X R w η C A σ χ z k D r frame v)
    (ext : Rf_ext_d I X R)
    (prior : Tg_prefix_d I k L X R C (v 4) (v 3) (v 20) z p f)
    (play : Tg_play_d I X R C (v 4) (v 3) (v 20) s)
    (point : M.PairMember I i n z) (value : Rf_val_d I X R n x s)
    (actual : Rd_entry_d i y f) : M.PairMember I y x p := by
  let nx : ∃ a, M.mem a X := ⟨w,request.context.omega_mem⟩
  have en := ext.native_l I nx
  obtain ⟨nc,ρ,eq,issued,_⟩ := request.read_l I hKP en
  obtain ⟨fn,t,played,graph⟩ := prior
  obtain ⟨n',x',point',image,val⟩ := (graph i y (fn.bound_l actual).1 (fn.bound_l actual).2).mp actual
  have same : n' = n := request.numbers.injection.1.1.2 i n' n point' point
  subst n'
  have fs := request.context.finite_l nx en
  let J := rt_pair_l fs.transitive nc en fs.pair
  have same : x = x' := Tg_play_d.native_entry_eq_l I nx en ⟨C,request.context.member⟩ fs.transitive nc J ρ issued
    ((eq 4).symm ▸ (eq 3).symm ▸ (eq 20).symm ▸ play)
    ((eq 4).symm ▸ (eq 3).symm ▸ (eq 20).symm ▸ played) value val
  exact same.symm ▸ image

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一实际档案视图自动供应短图事件；当前前缀的取值按真实根图识别。 -/
theorem Tg_iteration_d.archive_value_l
    {Ω c o C₀ S₀ γ Bγ A m r : M.Domain} {v : Fin 29 → M.Domain} {a : Fin 46 → M.Domain}
    (state : Tg_iteration_d hZF Ω c o C₀ S₀ γ Bγ A v a)
    (row : Tg_archive_row_d M.Domain) (entry : Rd_entry_d m r (v 13))
    (tuple : Rt_tuple_d row.values_d r) {w : Fin 54 → M.Domain}
    (code : Tg_saved_code_d row.X row.R row.w row.U row.q w) :
    ∃ l φ V Γ g s,
      Ic_agree_d Kp row.X row.R row.A row.π (v 0) (v 1) (v 18) (v 19) row.L l φ row.U V Γ g ∧
      Rd_entry_d (w 40) s g ∧ Tg_play_d Kp (v 0) (v 1) (v 5) (a 4) (a 3) (a 20) s ∧
      ∀ i n x y, Rd_entry_d i n (v 3) → Rf_val_d Kp (v 0) (v 1) n x s →
        Rd_entry_d i y (v 28) → Rd_entry_d y x (v 16) := by
  obtain ⟨c',node,_,copy⟩ := state.history.row_l hZF state.row
  have eq := state.tree.diagram.model_function.2 (v 7) c' (v 15) node state.node
  subst c'
  obtain ⟨X',R',_,_,_,model,source,_⟩ := (copy.source_l hZF).objects
  obtain ⟨eqX,eqR⟩ := smdl_unique_l Kp model state.model
  subst X' R'
  obtain ⟨old,pack,_,_,_,_,l,φ,V,Γ,g,common,view⟩ := state.request.views m r entry
  have eq := Tg_archive_row_d.eq_l (rt_tuple_inj_l pack tuple)
  subst old
  obtain ⟨w',pack,_,_,_,_,_,_,_,_,_,_,s,image,play⟩ := view
  have eq : w' 40 = w 40 := congrFun (pack.inj_l Kp hZF.1 code) 42
  exact ⟨l,φ,V,Γ,g,s,common,eq ▸ image,play,
    fun _ _ _ _ point value actual => state.request.play_value_l Kp (ZF.modelsKP hZF)
      source.ext state.play play point value actual⟩

end YesMetaZFC.SetTheory.LargeCardinal
