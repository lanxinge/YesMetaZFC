import YesMetaZFC.SetTheory.LargeCardinal.Game.RequestState
import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchiveSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationStep
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.TreeSyntax

/-! # 原请求及整列档案不变量的一阶编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- Ω,γ,Bγ,C₀,H,N,S,B,σ,w,C,c,e,a,b,z,h。
def tg_archive_views_m {d} (r : Fin 17 → Term d) : Formula 1 d :=
  let t : Fin 17 → Term (2+d) := fun i => (r i).rename (Fin.natAdd 2)
  let a : Fin 2 → Term (2+d) := fun i => .bound (i.castAdd d)
  rb_forall_m (.imp (Formula.orderedPairMem kpair_convention_l (a 0) (a 1) (t 4))
    (tg_archive_entry_m (fun i => [t 0,t 1,t 2,t 3,t 5,t 6,t 7,t 8,t 9,t 10,t 11,t 12,t 13,t 14,t 15,t 16,a 0,a 1].get i)))

@[simp] theorem tg_archive_views_closed_l {d} (r : Fin 17 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) : (tg_archive_views_m r).FreeClosed := by
  simp -implicitDefEqProofs [tg_archive_views_m,Definitional.Formula.FreeClosed,hr,Fin.forall_fin_succ]

theorem tg_archive_views_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (r : Fin 17 → Term d) :
    Formula.satisfies ρ (tg_archive_views_m r) ↔
      Tg_archive_views_d (kp_pair_l hKP) ((r 0).eval ρ) ((r 1).eval ρ) ((r 2).eval ρ) ((r 3).eval ρ)
        ((r 4).eval ρ) ((r 5).eval ρ) ((r 6).eval ρ) ((r 7).eval ρ) ((r 8).eval ρ) ((r 9).eval ρ)
        ((r 10).eval ρ) ((r 11).eval ρ) ((r 12).eval ρ) ((r 13).eval ρ) ((r 14).eval ρ)
        ((r 15).eval ρ) ((r 16).eval ρ) := by
  simp only [tg_archive_views_m,rb_forall_sat_l,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff (kp_pair_l hKP),tg_archive_entry_sat_l hKP,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left,List.get]
  exact ⟨fun h m r => h (fun i => [m,r].get i),fun h v => h (v 0) (v 1)⟩

-- Ω,γ,Bγ,C₀,S₀,X,R,w,η,C,A,σ,χ,z,k,D,r,o,n,Q,G,L,H。
def tg_request_state_m {d} (r : Fin 23 → Term d) (v : Fin 46 → Term d) : Formula 1 d := set[d] ⟪
  ⌜tg_context_data_m⌝ₚ(⌜r 7⌝ₛ,⌜r 5⌝ₛ,⌜r 6⌝ₛ,⌜r 8⌝ₛ,⌜r 9⌝ₛ) ∧
  ⌜rf_record_m (𝒞 := kpair_convention_l) tg_issued0_m⌝ₚ(⌜r 5⌝ₛ,⌜r 6⌝ₛ,⌜r 9⌝ₛ,⌜r 16⌝ₛ) ∧
  ⌜rf_tuple_m (𝒞 := kpair_convention_l) (r 5) (r 6) v⌝ₚ(⌜r 16⌝ₛ) ∧
  ⌜v 0⌝ₛ = ⌜r 7⌝ₛ ∧ ⌜Formula.isOmega⌝ₚ(⌜r 0⌝ₛ) ∧
  ⌜rr_layer_m⌝ₚ(⌜r 0⌝ₛ,⌜r 5⌝ₛ,⌜r 6⌝ₛ,⌜r 7⌝ₛ,⌜r 13⌝ₛ) ∧ ⌜r 14⌝ₛ ∈ ⌜r 0⌝ₛ ∧
  ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜r 14⌝ₛ,⌜v 19⌝ₛ,⌜r 13⌝ₛ) ∧
  ⌜Formula.isSequenceOfLength kpair_convention_l⌝ₚ(⌜r 15⌝ₛ,⌜r 14⌝ₛ) ∧
  ⌜fun H o n Q G L D => tg_archive_links_m (fun i => [H,o,n,Q,G,L,D].get i)⌝ₚ
    (⌜r 15⌝ₛ,⌜r 17⌝ₛ,⌜r 18⌝ₛ,⌜r 19⌝ₛ,⌜r 20⌝ₛ,⌜r 21⌝ₛ,⌜r 22⌝ₛ) ∧
  ⌜tg_archive_names_m⌝ₚ(⌜r 4⌝ₛ,⌜r 15⌝ₛ) ∧
  (∃ p, ⌜it_map_m⌝ₚ(⌜r 20⌝ₛ,⌜r 17⌝ₛ,⌜r 18⌝ₛ,p) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜r 4⌝ₛ,⌜v 7⌝ₛ,p)) ∧
  ⌜fun Ω γ Bγ C₀ H N S B σ w C c e a b z h => tg_archive_views_m
    (fun i => [Ω,γ,Bγ,C₀,H,N,S,B,σ,w,C,c,e,a,b,z,h].get i)⌝ₚ
      (⌜r 0⌝ₛ,⌜r 1⌝ₛ,⌜r 2⌝ₛ,⌜r 3⌝ₛ,⌜r 15⌝ₛ,⌜r 5⌝ₛ,⌜r 6⌝ₛ,⌜r 10⌝ₛ,⌜r 11⌝ₛ,
        ⌜r 7⌝ₛ,⌜r 9⌝ₛ,⌜v 4⌝ₛ,⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜r 13⌝ₛ,⌜v 20⌝ₛ) ∧
  ⌜it_lower_m⌝ₚ(⌜r 1⌝ₛ,⌜r 5⌝ₛ,⌜r 6⌝ₛ,⌜v 24⌝ₛ) ∧
  ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜r 12⌝ₛ,⌜v 24⌝ₛ,⌜r 6⌝ₛ)⟫

@[simp] theorem tg_request_state_closed_l {d} (r : Fin 23 → Term d) (v : Fin 46 → Term d)
    (hr : ∀ i, (r i).freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) :
    (tg_request_state_m r v).FreeClosed := by
  simp -implicitDefEqProofs [tg_request_state_m,Definitional.Formula.FreeClosed,hr,hv,Fin.forall_fin_succ,
    rf_record_closed_l _ tg_issued0_closed_l _ _ _ _ (hr 5) (hr 6) (hr 9) (hr 16)]

theorem tg_request_state_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (r : Fin 23 → Term d) (v : Fin 46 → Term d) : Formula.satisfies ρ (tg_request_state_m r v) ↔
      Tg_request_state_d (kp_pair_l hKP) ((r 0).eval ρ) ((r 1).eval ρ) ((r 2).eval ρ) ((r 3).eval ρ)
        ((r 4).eval ρ) ((r 5).eval ρ) ((r 6).eval ρ) ((r 7).eval ρ) ((r 8).eval ρ) ((r 9).eval ρ)
        ((r 10).eval ρ) ((r 11).eval ρ) ((r 12).eval ρ) ((r 13).eval ρ) ((r 14).eval ρ)
        ((r 15).eval ρ) ((r 16).eval ρ)
        ⟨(r 17).eval ρ,(r 18).eval ρ,(r 19).eval ρ,(r 20).eval ρ,(r 21).eval ρ,(r 22).eval ρ⟩
        (fun i => (v i).eval ρ) := by
  simp only [tg_request_state_m,Formula.satisfies_conj_iff,tg_context_data_sat_l (kp_pair_l hKP),
    rf_record_sat_l (kp_pair_l hKP) _ _ tg_issued0_closed_l,rf_tuple_sat_l (kp_pair_l hKP),
    Formula.satisfies_extensionalEq_iff_eq hKP.1,Formula.satisfies_isOmega_iff,
    rr_layer_sat_l (kp_pair_l hKP) hKP.1,Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff (kp_pair_l hKP),Formula.satisfies_isSequenceOfLength_iff (kp_pair_l hKP) hKP.1,
    tg_archive_links_sat_l (kp_pair_l hKP) hKP.1,tg_archive_names_sat_l (kp_pair_l hKP) hKP.1,
    Formula.satisfies_exists_iff,it_map_sat_l hKP.1,tg_archive_views_sat_l hKP,it_lower_sat_l (kp_pair_l hKP) hKP.1,
    Definitional.Term.eval_weaken,List.get]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o⟩,
    fun h => ⟨h.context,h.record,h.values,h.omega,h.external_omega,h.numbers,h.finite,h.index,
      h.sequence,h.links,h.names,h.name,h.views,h.lower,h.below⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原树、复制历史、档案与原局的七十五项状态码

状态码直接解释现用有限状态的全部字段。二十九项对象列在前，四十六项原请求在后。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def tg_iteration_m {d} (ω c o C₀ S₀ γ Bγ A : Term d) (v : Fin 29 → Term d) (a : Fin 46 → Term d) : Formula 1 d :=
  .conj (set[d] ⟪⌜v 7⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(⌜v 6⌝ₛ,⌜v 7⌝ₛ) ∧
    ⌜it_tree_m⌝ₚ(⌜ω⌝ₛ,⌜c⌝ₛ,⌜v 6⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,⌜v 11⌝ₛ) ∧
    ⌜ic_history_m⌝ₚ(⌜ω⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,⌜v 11⌝ₛ,⌜v 12⌝ₛ,⌜v 6⌝ₛ,⌜v 20⌝ₛ,⌜v 21⌝ₛ,⌜v 22⌝ₛ,⌜v 23⌝ₛ) ∧
    ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜v 12⌝ₛ) ∧
    (∀ i L, ⌜rd_entry0_m⌝ₚ(i,L,⌜v 12⌝ₛ) ↔ (∃ p κ F, ⌜rd_entry0_m⌝ₚ(i,p,⌜v 11⌝ₛ) ∧ ⌜it_payload_m⌝ₚ(p,κ,L,F))) ∧
    ⌜ic_at_m⌝ₚ(⌜v 20⌝ₛ,⌜v 7⌝ₛ,⌜v 0⌝ₛ,⌜v 18⌝ₛ,⌜v 19⌝ₛ,⌜v 24⌝ₛ,⌜v 25⌝ₛ,⌜v 26⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 7⌝ₛ,⌜v 15⌝ₛ,⌜v 9⌝ₛ) ∧ ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 15⌝ₛ,⌜v 0⌝ₛ,⌜v 1⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜o⌝ₛ,⌜c⌝ₛ,⌜v 9⌝ₛ) ∧ ⌜it_map_m⌝ₚ(⌜v 10⌝ₛ,⌜o⌝ₛ,⌜v 7⌝ₛ,⌜v 16⌝ₛ) ∧
    ⌜tg_basis_m⌝ₚ(⌜γ⌝ₛ,⌜Bγ⌝ₛ,⌜C₀⌝ₛ,⌜v 2⌝ₛ,⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 5⌝ₛ,⌜v 16⌝ₛ) ∧
    ⌜ic_bound_m⌝ₚ(⌜v 20⌝ₛ,⌜v 9⌝ₛ,⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 19⌝ₛ,⌜v 7⌝ₛ,⌜v 14⌝ₛ)⟫)
  (.conj (tg_request_state_m (fun i =>
    [ω,γ,Bγ,C₀,S₀,v 0,v 1,v 2,v 4,v 5,v 18,v 19,v 14,v 3,v 27,v 13,v 17,o,v 7,v 9,v 10,v 12,v 20].get i) a)
    (set[d] ⟪⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜A⌝ₛ,⌜a 6⌝ₛ,⌜v 16⌝ₛ) ∧
      ⌜tg_prefix_m⌝ₚ(⌜v 27⌝ₛ,⌜A⌝ₛ,⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 5⌝ₛ,⌜a 4⌝ₛ,⌜a 3⌝ₛ,⌜a 20⌝ₛ,⌜v 3⌝ₛ,⌜v 16⌝ₛ,⌜v 28⌝ₛ) ∧
      ⌜it_critical_bound_m⌝ₚ(⌜γ⌝ₛ,⌜v 9⌝ₛ,⌜v 11⌝ₛ)⟫))

@[simp] theorem tg_iteration_closed_l {d} (ω c o C₀ S₀ γ Bγ A : Term d)
    (v : Fin 29 → Term d) (a : Fin 46 → Term d)
    (hw : ω.freeSupport = []) (hc : c.freeSupport = []) (ho : o.freeSupport = [])
    (hC : C₀.freeSupport = []) (hS : S₀.freeSupport = []) (hγ : γ.freeSupport = [])
    (hB : Bγ.freeSupport = []) (hA : A.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (ha : ∀ i, (a i).freeSupport = []) :
    (tg_iteration_m ω c o C₀ S₀ γ Bγ A v a).FreeClosed := by
  simp -implicitDefEqProofs [tg_iteration_m,Definitional.Formula.FreeClosed,hw,hc,ho,hC,hS,hγ,hB,hA,hv,ha,Fin.forall_fin_succ]

theorem tg_iteration_sat_l {d} (ρ : Env M d) (ω c o C₀ S₀ γ Bγ A : Term d)
    (v : Fin 29 → Term d) (a : Fin 46 → Term d) :
    Formula.satisfies ρ (tg_iteration_m ω c o C₀ S₀ γ Bγ A v a) ↔
      Tg_iteration_d hZF (ω.eval ρ) (c.eval ρ) (o.eval ρ) (C₀.eval ρ) (S₀.eval ρ) (γ.eval ρ) (Bγ.eval ρ) (A.eval ρ)
        (fun i => (v i).eval ρ) (fun i => (a i).eval ρ) := by
  simp only [tg_iteration_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,KP.succ0_sat_l hZF.1,
    it_tree_sat_l hZF,ic_history_sat_l hZF,Formula.satisfies_isFunction_iff I hZF.1,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,rd_entry0_sat_l hZF.1,
    Formula.satisfies_exists_iff,it_payload_sat_l hZF.1,ic_at_sat_l hZF.1,smdl_sat_l I,it_map_sat_l hZF.1,
    tg_basis_sat_l I hZF.1,ic_bound_sat_l (ZF.modelsKP hZF),tg_request_state_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_orderedPairMem_iff I,tg_prefix_sat_l I hZF.1,it_critical_bound_sat_l I hZF.1,
    Definitional.Term.eval_weaken,List.get]
  exact ⟨fun ⟨⟨a,b,c,d,e,f,g,h,i,j,k,l,m⟩,n,o,p,q⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q⟩,
    fun h => ⟨⟨h.finite,h.successor,h.tree,h.history,h.levels_function,h.levels,h.row,h.node,h.model,
      h.root_node,h.root_map,h.basis,h.bound⟩,h.request,h.alphabet,h.play,h.critical⟩⟩

def Tg_iteration_code_d (ω c o C₀ S₀ γ Bγ A s : M.Domain) : Prop := ∃ q : Fin 75 → M.Domain,
  Rt_tuple_d q s ∧ Tg_iteration_d hZF ω c o C₀ S₀ γ Bγ A
    (fun i => q (i.castAdd 46)) (fun i => q (Fin.natAdd 29 i))

def tg_iteration_code_m {d} (ω c o C₀ S₀ γ Bγ A s : Term d) : Formula 1 d :=
  let r : Term d → Term (75+d) := fun t => t.rename (Fin.natAdd 75)
  rb_exists_m (.conj (rt_tuple_m (fun i : Fin 75 => .bound (i.castAdd d)) (r s))
    (tg_iteration_m (r ω) (r c) (r o) (r C₀) (r S₀) (r γ) (r Bγ) (r A)
      (fun i => .bound ((i.castAdd 46).castAdd d)) (fun i => .bound ((Fin.natAdd 29 i).castAdd d))))

@[simp] theorem tg_iteration_code_closed_l {d} (ω c o C₀ S₀ γ Bγ A s : Term d)
    (hw : ω.freeSupport = []) (hc : c.freeSupport = []) (ho : o.freeSupport = [])
    (hC : C₀.freeSupport = []) (hS : S₀.freeSupport = []) (hγ : γ.freeSupport = [])
    (hB : Bγ.freeSupport = []) (hA : A.freeSupport = []) (hs : s.freeSupport = []) :
    (tg_iteration_code_m ω c o C₀ S₀ γ Bγ A s).FreeClosed := by
  simp -implicitDefEqProofs [tg_iteration_code_m,Definitional.Formula.FreeClosed,hw,hc,ho,hC,hS,hγ,hB,hA]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs)

theorem tg_iteration_code_sat_l {d} (ρ : Env M d) (ω c o C₀ S₀ γ Bγ A s : Term d) :
    Formula.satisfies ρ (tg_iteration_code_m ω c o C₀ S₀ γ Bγ A s) ↔
      Tg_iteration_code_d hZF (ω.eval ρ) (c.eval ρ) (o.eval ρ) (C₀.eval ρ) (S₀.eval ρ)
        (γ.eval ρ) (Bγ.eval ρ) (A.eval ρ) (s.eval ρ) := by
  simp only [tg_iteration_code_m,Tg_iteration_code_d,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hZF.1,tg_iteration_sat_l hZF,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]

theorem Tg_iteration_d.pack_l {ω c o C₀ S₀ γ Bγ A : M.Domain} {v : Fin 29 → M.Domain} {a : Fin 46 → M.Domain}
    (h : Tg_iteration_d hZF ω c o C₀ S₀ γ Bγ A v a) : ∃ s,
      Rt_tuple_d (Fin.addCases (m := 29) (n := 46) (motive := fun _ => M.Domain) v a) s ∧
      Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A s := by
  let q : Fin 75 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v a
  obtain ⟨s,code⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) q
  exact ⟨s,code,q,code,by simpa only [q,Fin.addCases_left,Fin.addCases_right] using h⟩

end YesMetaZFC.SetTheory.LargeCardinal
