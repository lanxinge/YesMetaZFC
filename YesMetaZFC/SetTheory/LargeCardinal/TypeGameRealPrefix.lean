import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePlayTrace
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContext

/-! # 当前辅助历史唯一确定完整原实数前缀

前缀的定义域是已完成的原轮号；逐点对应仍在实际反射层中读取。
完整前缀与存档中的短前缀使用同一事件谓词，故可直接比较和搬运。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

def Tg_real_d (A C c b n h s : M.Domain) : Prop := Fn0_d n A s ∧ Tg_play_d C c b h s
def tg_real_m {d} (A C c b n h s : Term d) : Formula 1 d := .conj (fn0_m n A s) (tg_play_m C c b h s)
@[simp] theorem tg_real_closed_l {d} (A C c b n h s : Term d)
    (hA : A.freeSupport = []) (hC : C.freeSupport = []) (hc : c.freeSupport = []) (hb : b.freeSupport = [])
    (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hs : s.freeSupport = []) : (tg_real_m A C c b n h s).FreeClosed := by
  simp -implicitDefEqProofs [tg_real_m, Definitional.Formula.FreeClosed,hA,hC,hc,hb,hn,hh,hs]
theorem tg_real_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A C c b n h s : Term d) :
    Formula.satisfies ρ (tg_real_m A C c b n h s) ↔ Tg_real_d (A.eval ρ) (C.eval ρ) (c.eval ρ)
      (b.eval ρ) (n.eval ρ) (h.eval ρ) (s.eval ρ) := by
  simp only [tg_real_m,Tg_real_d,Formula.satisfies_conj_iff,fn0_sat_l hE,tg_play_sat_l]

def Tg_turn_move_d (I : kpair_convention_l.Interpretation M) (ω A C c b n h C' c' b' m h' x : M.Domain) : Prop :=
  ∃ s t y, Tg_real_d A C c b n h s ∧ Tg_real_d A C' c' b' m h' t ∧
    Fseq_end_d I ω t s y ∧ (Gm_even_d I ω n → y = x)
def tg_turn_move_m {d} (ω A C c b n h C' c' b' m h' x : Term d) : Formula 1 d := set[d] ⟪∃ s t y,
  ⌜tg_real_m⌝ₚ(⌜A⌝ₛ,⌜C⌝ₛ,⌜c⌝ₛ,⌜b⌝ₛ,⌜n⌝ₛ,⌜h⌝ₛ,s) ∧
  ⌜tg_real_m⌝ₚ(⌜A⌝ₛ,⌜C'⌝ₛ,⌜c'⌝ₛ,⌜b'⌝ₛ,⌜m⌝ₛ,⌜h'⌝ₛ,t) ∧
  ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,t,s,y) ∧ (⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜n⌝ₛ) → y = ⌜x⌝ₛ)⟫
derive_free_closed tg_turn_move_m
theorem tg_turn_move_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {d} (ρ : Env M d)
    (ω A C c b n h C' c' b' m h' x : Term d) : Formula.satisfies ρ (tg_turn_move_m ω A C c b n h C' c' b' m h' x) ↔
    Tg_turn_move_d I (ω.eval ρ) (A.eval ρ) (C.eval ρ) (c.eval ρ) (b.eval ρ) (n.eval ρ) (h.eval ρ)
      (C'.eval ρ) (c'.eval ρ) (b'.eval ρ) (m.eval ρ) (h'.eval ρ) (x.eval ρ) := by
  simp only [tg_turn_move_m,Tg_turn_move_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,tg_real_sat_l hE,
    fseq_end_sat_l I hE,gm_even_sat_l I hE,Formula.satisfies_imp_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem tg_issued_real_l {ω C : M.Domain} (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 46) (valid : Formula.satisfies ρ tg_issued0_m) :
    ∃ s, Tg_real_d (ρ.bound 6).val C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 19).val (ρ.bound 20).val s := by
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  obtain ⟨h,x,_,_,_,_,_,_,_,_,_,endt,digits,_⟩ := tg_issued_query_l J (rt_model_ext_l hZF.1 fs.transitive nc) ρ valid
  refine ⟨x.val,(rt_fn_l fs.transitive nc hZF.1 _ _ _).mp digits.1,?_⟩
  apply (tg_play_read_l hZF fs.transitive nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) x).mpr
  intro i v hi
  exact ((digits.2 i v (digits.1.bound_l hi).1).mp hi).end_l endt

theorem Tg_real_d.unique_l {ω C s t : M.Domain} (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 46) (valid : Formula.satisfies ρ tg_issued0_m)
    (hs : Tg_real_d (ρ.bound 6).val C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 19).val (ρ.bound 20).val s)
    (ht : Tg_real_d (ρ.bound 6).val C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 19).val (ρ.bound 20).val t) : s = t := by
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have gs := fn0_function_l (ZF.modelsKP hZF) hs.1
  have gt := fn0_function_l (ZF.modelsKP hZF) ht.1
  exact hZF.1.eq_of_same_members s t fun p =>
    ⟨hs.2.subset_l hZF fs.transitive nc J ρ valid ht.2 ⟨gs.1,gs.2.1⟩ ⟨gt.1,gt.2.1⟩ (fun _ h => h) p,
     ht.2.subset_l hZF fs.transitive nc J ρ valid hs.2 ⟨gt.1,gt.2.1⟩ ⟨gs.1,gs.2.1⟩ (fun _ h => h) p⟩

end YesMetaZFC.SetTheory.LargeCardinal
