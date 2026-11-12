import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationCopy
import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchivePlayNative

/-! # 每份原档案在足够晚的实际阶段与给定对局逐点对应

比较指标i时，将档案所在阶段与i的后继阶段合并。档案域的包含保证新阶段已经经过i，
所以同一短图事件可与给定原对局的第i个字母比较；不预设短图整体的字母表范围。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_archive_play_native_d (ω D H f : M.Domain) : Prop :=
  ∀ m r, ∀ row : Tg_archive_row_d M.Domain, Rd_entry_d m r D → Rt_tuple_d row.values_d r →
    ∀ w : Fin 54 → M.Domain, Tg_saved_code_d row.X row.R row.w row.U row.q w →
    ∀ i, M.mem i ω → ∃ k t, ∃ v : Fin 75 → M.Domain, ∃ l φ V Γ g s,
      Rd_entry_d k t H ∧ Rt_tuple_d v t ∧ M.mem i k ∧ Rd_entry_d m r (v 13) ∧
      Ic_agree_d I row.X row.R row.A row.π (v 0) (v 1) (v 18) (v 19) row.L l φ row.U V Γ g ∧
      Rd_entry_d (w 40) s g ∧ Tg_play_d I (v 0) (v 1) (v 5) (v 33) (v 32) (v 49) s ∧
      ∀ n x y, Rd_entry_d i n (v 3) → Rf_val_d I (v 0) (v 1) n x s →
        Rd_entry_d i y f → Rd_entry_d y x (v 16)

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_iteration_run_d.archive_play_l {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    (played : ∀ n t q, Rd_entry_d n t H → Rt_coord_d (28 : Fin 75) t q → M.IsRestrictionOf Kp q f n) :
    Tg_archive_play_native_d Kp ω (U 5) H f := by
  intro m r row entry tuple w code i hi
  obtain ⟨p,pair,hp⟩ := entry
  obtain ⟨v,k,t,ht,pack,hp⟩ := (u.columns 5 p).mp hp
  obtain ⟨j,succ,hj⟩ := u.tree.omega.1.2 i hi
  obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 j hj
  obtain ⟨v',pack',_⟩ := (h.rows j s hs).1
  obtain ⟨k',t',v'',ht',pack'',keep,keep'⟩ := (h.frames_l hZF).merge k j t s v v' ht hs pack pack'
  have current := h.read_l hZF v'' ht' pack''
  have prior := h.read_l hZF v' hs pack'
  have index : v' 27 = j := (h.rows j s hs).2.read_l v' pack'
  have index' : v'' 27 = k' := (h.rows k' t' ht').2.read_l v'' pack''
  obtain ⟨q,z,zp,hz⟩ := (prior.request.sequence.2.2 i).mp (index.symm ▸ succ.predecessor_mem)
  have ik : M.mem i k' := index' ▸ (current.request.sequence.2.2 i).mpr
    ⟨q,z,zp,keep'.2.2.1 5 z hz⟩
  have old : Rd_entry_d m r (v'' 13) := ⟨p,pair,keep.2.2.1 5 p hp⟩
  obtain ⟨l,φ,V,Γ,g,s',common,image,play,values⟩ := current.archive_value_l hZF row old tuple code
  have cut := played k' t' (v'' 28) ht' ⟨v'',pack'',rfl⟩
  exact ⟨k',t',v'',l,φ,V,Γ,g,s',ht',pack'',ik,old,common,image,play,
    fun n x y point value iy => values i n x y point value ((cut.2 i y).mpr ⟨ik,iy⟩)⟩

end YesMetaZFC.SetTheory.LargeCardinal
