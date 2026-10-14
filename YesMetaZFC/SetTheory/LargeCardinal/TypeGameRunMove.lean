import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunNext
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunAdvance
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordCoordinate

/-! # 统一状态码中的原局前缀与带输入的实际后继

状态仍使用原 64 元组；这里只投影原局所需的四个坐标。
后继同时保留原树边及一次真实落子，供全体有限原局共享同一选择函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

def Tg_run_real_d (A n r s : M.Domain) : Prop := ∃ C c b h,
  Rt_coord_d (5 : Fin 64) r C ∧ Rt_coord_d (22 : Fin 64) r c ∧
  Rt_coord_d (21 : Fin 64) r b ∧ Rt_coord_d (38 : Fin 64) r h ∧ Tg_real_d A C c b n h s
def tg_run_real_m {d} (A n r s : Term d) : Formula 1 d := set[d] ⟪∃ C c b h,
  ⌜rt_coord_m (5 : Fin 64)⌝ₚ(⌜r⌝ₛ,C) ∧ ⌜rt_coord_m (22 : Fin 64)⌝ₚ(⌜r⌝ₛ,c) ∧
  ⌜rt_coord_m (21 : Fin 64)⌝ₚ(⌜r⌝ₛ,b) ∧ ⌜rt_coord_m (38 : Fin 64)⌝ₚ(⌜r⌝ₛ,h) ∧
  ⌜tg_real_m⌝ₚ(⌜A⌝ₛ,C,c,b,⌜n⌝ₛ,h,⌜s⌝ₛ)⟫
derive_free_closed tg_run_real_m
theorem tg_run_real_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A n r s : Term d) :
    Formula.satisfies ρ (tg_run_real_m A n r s) ↔ Tg_run_real_d (A.eval ρ) (n.eval ρ) (r.eval ρ) (s.eval ρ) := by
  simp only [tg_run_real_m,Tg_run_real_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rt_coord_sat_l hE,tg_real_sat_l hE,Definitional.Term.eval_weaken]; rfl

theorem Tg_run_real_d.read_l {A n r s : M.Domain} {q : Fin 64 → M.Domain}
    (h : Tg_run_real_d A n r s) (code : Rt_tuple_d q r) : Tg_real_d A (q 5) (q 22) (q 21) n (q 38) s := by
  obtain ⟨C,c,b,h,hC,hc,hb,hh,real⟩ := h
  have coord {i x} (h : Rt_coord_d i r x) : q i = x := by
    obtain ⟨v,p,e⟩ := h
    exact (congrFun (rt_tuple_inj_l code p) i).trans e
  exact (coord hC).symm ▸ (coord hc).symm ▸ (coord hb).symm ▸ (coord hh).symm ▸ real

theorem Tg_run_real_d.function_l {A n r s : M.Domain} (h : Tg_run_real_d A n r s) : Fn0_d n A s := by
  obtain ⟨_,_,_,_,_,_,_,_,real⟩ := h
  exact real.1

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_run_move_d (ω A n m r t x : M.Domain) : Prop := ∃ s q y,
  Tg_run_real_d A n r s ∧ Tg_run_real_d A m t q ∧ Fseq_end_d I ω q s y ∧ (Gm_even_d I ω n → y = x)
def tg_run_move_m {d} (ω A n m r t x : Term d) : Formula 1 d := set[d] ⟪∃ s q y,
  ⌜tg_run_real_m⌝ₚ(⌜A⌝ₛ,⌜n⌝ₛ,⌜r⌝ₛ,s) ∧ ⌜tg_run_real_m⌝ₚ(⌜A⌝ₛ,⌜m⌝ₛ,⌜t⌝ₛ,q) ∧
  ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,q,s,y) ∧
  (⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜n⌝ₛ) → y = ⌜x⌝ₛ)⟫
derive_free_closed tg_run_move_m
theorem tg_run_move_sat_l {d} (ρ : Env M d) (ω A n m r t x : Term d) :
    Formula.satisfies ρ (tg_run_move_m ω A n m r t x) ↔ Tg_run_move_d hZF
      (ω.eval ρ) (A.eval ρ) (n.eval ρ) (m.eval ρ) (r.eval ρ) (t.eval ρ) (x.eval ρ) := by
  simp only [tg_run_move_m,Tg_run_move_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    tg_run_real_sat_l hZF.1,fseq_end_sat_l I hZF.1,gm_even_sat_l I hZF.1,Formula.satisfies_imp_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Definitional.Term.eval_weaken]; rfl

theorem Tg_run_code_d.real_l {ω c o C γ Z A n r : M.Domain} (h : Tg_run_code_d hZF ω c o C γ Z A n r) :
    ∃ s, Tg_run_real_d A n r s := by
  obtain ⟨q,code,run,num⟩ := h
  let nc : Nonempty {z // M.mem z (q 5)} := ⟨⟨ω,run.context.omega⟩⟩
  obtain ⟨ρ,eq,valid⟩ := run.read_l hZF nc
  have fs := (run.context.read_l hZF run.source.source).1
  obtain ⟨s,real⟩ := tg_issued_real_l hZF fs nc ρ valid
  have real : Tg_real_d A (q 5) (q 22) (q 21) n (q 38) s :=
    run.alphabet ▸ num ▸ eq 6 ▸ eq 4 ▸ eq 3 ▸ eq 19 ▸ eq 20 ▸ real
  exact ⟨s,q 5,q 22,q 21,q 38,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,real⟩

theorem Tg_run_code_d.real_unique_l {ω c o C γ Z A n r s t : M.Domain}
    (h : Tg_run_code_d hZF ω c o C γ Z A n r) (hs : Tg_run_real_d A n r s) (ht : Tg_run_real_d A n r t) : s = t := by
  obtain ⟨q,code,run,num⟩ := h
  let nc : Nonempty {z // M.mem z (q 5)} := ⟨⟨ω,run.context.omega⟩⟩
  obtain ⟨ρ,eq,valid⟩ := run.read_l hZF nc
  have fs := (run.context.read_l hZF run.source.source).1
  have ea := (eq 6).trans run.alphabet
  have en := (eq 19).trans num
  exact Tg_real_d.unique_l hZF fs nc ρ valid
    (ea.symm ▸ (eq 4).symm ▸ (eq 3).symm ▸ en.symm ▸ (eq 20).symm ▸ hs.read_l code)
    (ea.symm ▸ (eq 4).symm ▸ (eq 3).symm ▸ en.symm ▸ (eq 20).symm ▸ ht.read_l code)

theorem Tg_run_move_d.last_l {ω A n m r t x : M.Domain} (h : Tg_run_move_d hZF ω A n m r t x) :
    ∃ s q y, Tg_run_real_d A n r s ∧ Tg_run_real_d A m t q ∧ Fseq_end_d I ω q s y ∧
      Rd_entry_d n y q ∧ (Gm_even_d I ω n → y = x) := by
  obtain ⟨s,q,y,hs,hq,endt,even⟩ := h
  obtain ⟨l,k,d⟩ := endt
  have kn := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) hs.function_l).2.1
  exact ⟨s,q,y,hs,hq,⟨l,k,d⟩,kn ▸ d.last_value,even⟩

theorem Tg_run_code_d.advance_l (hZFC : M.Models ZFC) {ω c₀ o C γ Z A n s x : M.Domain}
    (h : Tg_run_code_d (ZFC.models_zf_l hZFC) ω c₀ o C γ Z A n s) (ho : ∀ z, ¬ M.mem z o)
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z) (hAZ : M.mem A Z) (hx : M.mem x A) :
    ∃ m t, M.SuccessorOf m n ∧ Tg_run_code_d (ZFC.models_zf_l hZFC) ω c₀ o C γ Z A m t ∧
      Tg_run_edge_d (ZFC.models_zf_l hZFC) ω c₀ s t ∧ Tg_run_move_d (ZFC.models_zf_l hZFC) ω A n m s t x := by
  obtain ⟨q,code,run,num⟩ := h
  obtain ⟨v,u,next,edge,move⟩ := run.advance_l hZFC ho hγ hωZ hAZ hx
  have copy := edge
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,succ,_⟩ := copy
  let r : Fin 64 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v u
  obtain ⟨t,code'⟩ := rt_tuple_exists_l (ZF.modelsKP (ZFC.models_zf_l hZFC)) r
  have valid : Tg_run_code_d (ZFC.models_zf_l hZFC) ω c₀ o C γ Z A (u 19) t := by
    refine ⟨r,code',?_,rfl⟩
    simpa only [r,Fin.addCases_left,Fin.addCases_right] using next
  let z : Fin 128 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) q r
  refine ⟨u 19,t,num ▸ succ,valid,⟨z,?_,?_,?_⟩,?_⟩
  · simpa only [z,Fin.addCases_left] using code
  · simpa only [z,Fin.addCases_right] using code'
  · simpa only [z,r,Fin.addCases_left,Fin.addCases_right] using edge
  · obtain ⟨a,b,y,ha,hb,endt,even⟩ := move
    exact ⟨a,b,y,⟨q 5,q 22,q 21,q 38,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,num ▸ ha⟩,
      ⟨r 5,r 22,r 21,r 38,⟨r,code',rfl⟩,⟨r,code',rfl⟩,⟨r,code',rfl⟩,⟨r,code',rfl⟩,hb⟩,endt,num ▸ even⟩

end YesMetaZFC.SetTheory.LargeCardinal
