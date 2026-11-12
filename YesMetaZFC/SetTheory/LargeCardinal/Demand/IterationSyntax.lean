import YesMetaZFC.SetTheory.LargeCardinal.Demand.IterationState
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveCode
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.TreeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationSyntax

/-! # 六十六项 demanding 状态的可分离公式

十九项头部和四十七槽请求直接组成状态码；语义与原后继逐字段等价。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def td_state_m {d} (g : Fin 10 → Term d) (v : Fin 19 → Term d) (a : Fin 47 → Term d) : Formula 1 d :=
  .conj (set[d] ⟪⌜v 5⌝ₛ ∈ ⌜g 0⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(⌜v 6⌝ₛ,⌜v 5⌝ₛ) ∧
    ⌜it_tree_m⌝ₚ(⌜g 0⌝ₛ,⌜g 1⌝ₛ,⌜v 6⌝ₛ,⌜v 7⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ) ∧
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 2⌝ₛ,⌜v 0⌝ₛ,⌜v 1⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 5⌝ₛ,⌜v 2⌝ₛ,⌜v 8⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜g 2⌝ₛ,⌜g 1⌝ₛ,⌜v 8⌝ₛ) ∧
    ⌜it_map_m⌝ₚ(⌜v 9⌝ₛ,⌜g 2⌝ₛ,⌜v 5⌝ₛ,⌜v 3⌝ₛ)⟫)
  (.conj (rr_truth_m (𝒞 := kpair_convention_l) td_issued0_m (v 0) (v 1) a)
  (.conj (rr_truth_m (𝒞 := kpair_convention_l) td_static0_m (v 0) (v 1) (fun i => a (i.castAdd 28)))
  (.conj (rr_layer_m (g 0) (v 0) (v 1) (a 0) (v 4))
  (.conj (tg_root_slice_m (fun i => [g 3,g 4,g 5,g 6,g 7,v 0,v 1,v 14,v 3,v 15,v 16,v 17].get i))
  (.conj (set[d] ⟪
    (∀ x, ⌜rd_entry0_m⌝ₚ(x,⌜v 15⌝ₛ,⌜v 1⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x,⌜a 24⌝ₛ,⌜v 1⌝ₛ)) ∧
    ⌜rd_entry0_m⌝ₚ(⌜a 0⌝ₛ,⌜v 16⌝ₛ,⌜v 1⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜a 6⌝ₛ,⌜v 16⌝ₛ,⌜v 1⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜g 8⌝ₛ,⌜a 6⌝ₛ,⌜v 3⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜g 9⌝ₛ,⌜a 7⌝ₛ,⌜v 3⌝ₛ) ∧
    ⌜v 12⌝ₛ ∈ ⌜g 0⌝ₛ ∧ ⌜Formula.isSequenceOfLength kpair_convention_l⌝ₚ(⌜v 11⌝ₛ,⌜v 12⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 12⌝ₛ,⌜a 19⌝ₛ,⌜v 4⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 13⌝ₛ,⌜a 24⌝ₛ,⌜v 1⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 13⌝ₛ,⌜a 5⌝ₛ,⌜v 1⌝ₛ)⟫)
  (.conj (td_archive_m (fun i => [g 0,g 1,g 3,g 8,g 9,v 11,v 0,v 1,v 13,a 4,a 1,a 2,v 4,a 20,g 6,v 3].get i))
  (.conj (td_archive_links_m (g 2) (v 8) (v 9) (v 10) (v 11))
    (.conj (pc_count_m (g 0) (v 0) (v 1) (a 5))
      (.conj (td_code_raw_m (v 0) (v 1) (a 7) (a 5)) (set[d] ⟪
        ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜v 18⌝ₛ) ∧
        (∀ i L, ⌜rd_entry0_m⌝ₚ(i,L,⌜v 18⌝ₛ) ↔
          ∃ p κ F, ⌜rd_entry0_m⌝ₚ(i,p,⌜v 10⌝ₛ) ∧ ⌜it_payload_m⌝ₚ(p,κ,L,F)) ∧
        ⌜td_clear_m⌝ₚ(⌜v 11⌝ₛ,⌜v 5⌝ₛ,⌜v 7⌝ₛ) ∧
        ⌜fun X R γ D C o Q G E => tg_raw_critical_m (fun i => [X,R,γ,D,C,o,Q,G,E].get i)⌝ₚ
          (⌜g 3⌝ₛ,⌜g 4⌝ₛ,⌜g 5⌝ₛ,⌜g 6⌝ₛ,⌜g 7⌝ₛ,⌜g 2⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ) ∧
        ⌜it_owned_m⌝ₚ(⌜g 0⌝ₛ,⌜v 8⌝ₛ,⌜v 10⌝ₛ)⟫))))))))))

@[simp] theorem td_state_closed_l {d} (g : Fin 10 → Term d) (v : Fin 19 → Term d) (a : Fin 47 → Term d)
    (hg : ∀ i, (g i).freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) (ha : ∀ i, (a i).freeSupport = []) :
    (td_state_m g v a).FreeClosed := by
  simp -implicitDefEqProofs [td_state_m,Definitional.Formula.FreeClosed,hg,hv,ha,Fin.forall_fin_succ]
  exact ⟨rr_truth_closed_l td_issued0_m td_issued0_closed_l _ _ _ (hv 0) (hv 1) ha,
    rr_truth_closed_l td_static0_m td_static0_closed_l _ _ _ (hv 0) (hv 1) (fun i => ha (i.castAdd 28))⟩

theorem td_state_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d)
    (g : Fin 10 → Term d) (v : Fin 19 → Term d) (a : Fin 47 → Term d) :
    Formula.satisfies ρ (td_state_m g v a) ↔
      Td_state_d hZF (fun i => (g i).eval ρ) (fun i => (v i).eval ρ) (fun i => (a i).eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [td_state_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,KP.succ0_sat_l hZF.1,
    it_tree_sat_l hZF,smdl_sat_l I,rd_entry0_sat_l hZF.1,it_map_sat_l hZF.1,
    rr_truth_sat_l I _ td_issued0_m td_issued0_closed_l,rr_truth_sat_l I _ td_static0_m td_static0_closed_l,
    rr_layer_sat_l I hZF.1,tg_root_slice_sat_l I hZF.1,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_isSequenceOfLength_iff I hZF.1,td_archive_sat_l (ZF.modelsKP hZF),
    td_archive_links_sat_l hZF.1,pc_count_sat_l I hZF.1,td_code_raw_sat_l I,
    Formula.satisfies_isFunction_iff I hZF.1,Formula.satisfies_iff_iff,Formula.satisfies_exists_iff,
    it_payload_sat_l hZF.1,td_clear_sat_l hZF.1,tg_raw_critical_sat_l I hZF.1,it_owned_sat_l I hZF.1,
    Definitional.Term.eval_weaken,List.get]
  exact ⟨fun ⟨⟨a,b,c,d,e,f,g⟩,h,i,j,k,⟨l,m,n,o,p,q,r,s,t,u⟩,v,w,x,y,z,zz,zzz,crit,owned⟩ =>
    ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,zz,zzz,crit,owned⟩,
    fun h => ⟨⟨h.finite,h.successor,h.tree,h.model,h.node,h.root_node,h.origin⟩,
      h.issued,h.static,h.numbers,h.slice,⟨h.below,h.omega_low,h.letters_low,h.letters_root,h.tree_root,
        h.round,h.sequence,h.index,h.bound,h.height⟩,h.archive,h.links,h.power,h.coding,h.levels_function,h.levels,h.clear,h.critical,h.owned⟩⟩

def Td_state_code_d (hZF : M.Models ZF) (g : Fin 10 → M.Domain) (s : M.Domain) : Prop :=
  ∃ v : Fin 66 → M.Domain, Rt_tuple_d v s ∧
    Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i))

def td_state_code_m {d} (g : Fin 10 → Term d) (s : Term d) : Formula 1 d :=
  let e : Term d → Term (66+d) := fun t => t.rename (Fin.natAdd 66)
  rb_exists_m (.conj (rt_tuple_m (fun i : Fin 66 => .bound (i.castAdd d)) (e s))
    (td_state_m (fun i => e (g i)) (fun i => .bound ((i.castAdd 47).castAdd d))
      (fun i => .bound ((Fin.natAdd 19 i).castAdd d))))

@[simp] theorem td_state_code_closed_l {d} (g : Fin 10 → Term d) (s : Term d)
    (hg : ∀ i, (g i).freeSupport = []) (hs : s.freeSupport = []) : (td_state_code_m g s).FreeClosed := by
  simp -implicitDefEqProofs [td_state_code_m,Definitional.Formula.FreeClosed,hg]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs)

theorem td_state_code_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (g : Fin 10 → Term d) (s : Term d) :
    Formula.satisfies ρ (td_state_code_m g s) ↔ Td_state_code_d hZF (fun i => (g i).eval ρ) (s.eval ρ) := by
  simp only [td_state_code_m,Td_state_code_d,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hZF.1,td_state_sat_l hZF,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]

theorem Td_state_d.pack_l (hZF : M.Models ZF) {g : Fin 10 → M.Domain}
    {v : Fin 19 → M.Domain} {a : Fin 47 → M.Domain} (h : Td_state_d hZF g v a) :
    ∃ s, Rt_tuple_d (Fin.addCases (m := 19) (n := 47) (motive := fun _ => M.Domain) v a) s ∧
      Td_state_code_d hZF g s := by
  obtain ⟨s,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF)
    (Fin.addCases (m := 19) (n := 47) (motive := fun _ => M.Domain) v a)
  exact ⟨s,tuple,_,tuple,by simpa only [Fin.addCases_left,Fin.addCases_right] using h⟩

theorem Td_state_code_d.read_l (hZF : M.Models ZF) {g : Fin 10 → M.Domain}
    {s : M.Domain} (h : Td_state_code_d hZF g s) {v : Fin 66 → M.Domain} (tuple : Rt_tuple_d v s) :
    Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i)) := by
  obtain ⟨w,pack,state⟩ := h
  exact rt_tuple_inj_l pack tuple ▸ state

end YesMetaZFC.SetTheory.LargeCardinal
